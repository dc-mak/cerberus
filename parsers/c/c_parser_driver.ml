open Cerb_frontend

(* How to render an offending token in a parser error message differs between
   the two lexers: the text lexer reads a real lexbuf, so its lexeme can be
   sliced out of the buffer; the internal-cpp token feed reads a dummy lexbuf, so
   the lexeme is recovered from its spelling table.  [handle] takes this policy
   explicitly (rather than via global state), so the two cases stay separate. *)
type show_token = Lexing.position * Lexing.position -> string

(* Text lexer: slice the offending lexeme out of [lexbuf] (offset accounts for a
   magic-comment substring's shift). *)
let text_show_token ~offset (lexbuf : Lexing.lexbuf) : show_token =
  fun (start, curr) ->
    try
      Lexing.lexeme {
        lexbuf with
        lex_start_pos = start.Lexing.pos_cnum - offset;
        lex_curr_pos = curr.Lexing.pos_cnum - offset;
      }
    with Invalid_argument _ ->
      Printf.sprintf
        "CPARSER_DRIVER(lex_buffer_len = %d; offset = %d; start_index = %d; end_index = %d)"
        lexbuf.lex_buffer_len offset
        (start.pos_cnum - offset) (curr.pos_cnum - offset)

(* Token feed: recover the lexeme from the feed's spelling table by start key. *)
let feed_show_token feed : show_token =
  fun (start, _curr) ->
    match Preproc_token_feed.lexeme_at feed start.Lexing.pos_cnum with
    | Some s -> s
    | None -> ""

(* The internal feed gives the parser raw positions whose file pos_cnum is a
   side-table key; resolve one through the feed.  (The text lexer's positions are
   already real, so its enrich is Fun.id.) *)
let feed_enrich feed (p : Cerb_position.t) =
  match Preproc_token_feed.lookup feed (Cerb_position.to_file_lexing p).pos_cnum with
  | Some resolved -> resolved
  | None -> p

(* [to_pos] resolves a reported Lexing.position to a Cerb_position (it already
   bakes in the lexer's enrich); [show_token] renders an offending lexeme.  Both
   are supplied by the caller — no line map / global state is consulted here. *)
let handle parse (token_pos_buffer, lexer) ~to_pos ~(show_token : show_token) lexbuf =
  try Exception.except_return (parse lexer lexbuf) with
  | C_lexer.Error err ->
    let loc = Cerb_location.point (to_pos (Lexing.lexeme_start_p lexbuf)) in
    Exception.fail (loc, Errors.CPARSER err)
  | C_parser.Error state ->
    let message =
      try
        let msg = C_parser_error.message state in
        if String.equal msg "<YOUR SYNTAX ERROR MESSAGE HERE>\n" then raise Not_found else msg
      with Not_found ->
        Printf.sprintf "Please add error message for state %d to parsers/c/c_parser_error.messages\n" state
    in
    let message = String.sub message 0 (String.length message - 1) in
    let range = (to_pos (Lexing.lexeme_start_p lexbuf), to_pos (Lexing.lexeme_end_p lexbuf)) in
    let loc = Cerb_location.(region range NoCursor) in
    let where = MenhirLib.ErrorReports.show show_token token_pos_buffer in
    Exception.fail (loc, Errors.CPARSER (Errors.Cparser_unexpected_token  (where ^ "\n" ^ message)))
  | Failure msg ->
    prerr_endline "CPARSER_DRIVER (Failure)";
    failwith msg
  | Lexer_feedback.KnR_declaration loc ->
    Exception.fail (loc, Errors.CPARSER Errors.Cparser_KnR_declaration)
  | exn ->
    let loc = Cerb_location.point @@ Cerb_position.from_lexing @@ Lexing.lexeme_start_p lexbuf in
    failwith @@ "CPARSER_DRIVER(" ^ Cerb_location.location_to_string loc ^ ")" ^ " ==> " ^ Stdlib.Printexc.to_string exn

let start_pos = function
  | Cerb_location.Loc_point loc
  | Loc_region (loc, _, _)
  | Loc_regions ((loc, _) :: _, _) -> Some loc
  | _ -> None

let diagnostic_get_tokens ~inside_cn loc string =
  (* `C_lexer.magic_token' ensures `loc` is a region *)
  let start_pos = Option.get @@ start_pos loc in
  let lexbuf = Lexing.from_string string in
  let `LEXER lexer = C_lexer.create_lexer ~inside_cn ~enrich:Fun.id in
  let rec relex (toks, pos) =
    try
      match lexer lexbuf with
      | Tokens.EOF -> (List.rev ("EOF" :: toks), List.rev pos)
      | t ->
        let Lexing.{ pos_lnum; pos_bol; pos_cnum; _ } = lexbuf.lex_start_p in
        let (line, col) =
          (* the first line needs to have columns shifted by /*@ but the rest do not *)
          let col_off = if inside_cn && pos_lnum > 1 then 1 else Cerb_position.column start_pos in
          let fi_pos = Cerb_position.to_file_lexing start_pos in
          (pos_lnum + fi_pos.pos_lnum, col_off + pos_cnum - pos_bol) in
        relex (Tokens.string_of_token t :: toks, (line, col) :: pos)
      with
        C_lexer.Error err ->
          (List.rev (Pp_errors.string_of_cparser_cause err :: toks), List.rev pos)
  in
  relex ([], [])

let parse_loc_string parse ~inside_cn (loc, str) =
  let lexbuf = Lexing.from_string str in
  (* `C_lexer.magic_token' ensures `loc` is a region *)
  let start_pos = Option.get @@ start_pos loc in
  Lexing.set_position lexbuf (Cerb_position.to_file_lexing start_pos);
  Lexing.set_filename lexbuf (Option.value ~default:"<none>" (Cerb_location.get_filename loc));
  (* TODO: the CN re-parse story (parse_loc_string / magic_comments_to_cn_toplevel)
     still needs to be figured out: the magic payload is re-lexed in its own
     coordinate space, and how its positions/enrich should compose with the outer
     translation unit (especially under the internal cpp) is left for later. *)
  let `LEXER cn_lexer = C_lexer.create_lexer ~inside_cn ~enrich:Fun.id in
  let offset = (Cerb_position.to_file_lexing start_pos).pos_cnum in
  handle
    parse
    (MenhirLib.ErrorReports.wrap cn_lexer)
    ~to_pos:Cerb_position.from_lexing
    ~show_token:(text_show_token ~offset lexbuf)
    lexbuf

let update_enclosing_region payload_region xs =
  let slash_inclusive_region = match payload_region with
    | Cerb_location.Loc_region (start_pos, end_pos, cursor) ->
      (* TODO: adjust CERB_MAGIC and EDecl_magic to carry a record:
         { slash_inclusive_region: Cerb_location.t; payload_region: Cerb_location.t } *)
        Cerb_location.region ( Cerb_position.change_cnum start_pos (-3)
                             , Cerb_position.change_cnum end_pos 2) cursor
    | _ -> assert false (* loc should always be a region *)
  in
  let update_decl_with_enclosing_region = function
    | Cabs.EDecl_funcCN func ->
        Cabs.EDecl_funcCN { func with Cn.cn_func_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_lemmaCN lmma ->
        Cabs.EDecl_lemmaCN { lmma with Cn.cn_lemma_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_predCN pred ->
        Cabs.EDecl_predCN { pred with Cn.cn_pred_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_datatypeCN dt ->
        Cabs.EDecl_datatypeCN { dt with Cn.cn_dt_magic_loc= slash_inclusive_region }
    | Cabs.EDecl_type_synCN ts ->
        Cabs.EDecl_type_synCN { ts with Cn.cn_tysyn_loc= slash_inclusive_region }
    | Cabs.EDecl_fun_specCN spec ->
        Cabs.EDecl_fun_specCN spec
    | _ ->
        (* C_parser.cn_toplevel only returns CN external declarations *)
        assert false
  in
  List.map update_decl_with_enclosing_region xs

let magic_comments_to_cn_toplevel (Cabs.TUnit decls) =
  let magic_comments_to_cn_toplevel = function
    | Cabs.EDecl_magic (loc, str) ->
      parse_loc_string C_parser.cn_toplevel ~inside_cn:true (loc, str)
      |> Exception.except_fmap (update_enclosing_region loc)
    | decl ->
      Exception.except_return [decl] in
  decls
  |> Exception.except_mapM magic_comments_to_cn_toplevel
  |> Exception.except_fmap (fun decls -> Cabs.TUnit (List.concat decls))

let parse_with_magic_comments lexbuf =
  (* Text lexer: the # line-marker rule sets real positions, so enrich = Fun.id
     and no post-parse traversal is needed. *)
  let `LEXER c_lexer = C_lexer.create_lexer ~inside_cn:false ~enrich:Fun.id in
  handle
    C_parser.translation_unit
    (MenhirLib.ErrorReports.wrap c_lexer)
    ~to_pos:Cerb_position.from_lexing
    ~show_token:(text_show_token ~offset:0 lexbuf)
    lexbuf

let parse lexbuf =
  Exception.except_bind (parse_with_magic_comments lexbuf)
    magic_comments_to_cn_toplevel

(* Parse a token stream produced by the internal preprocessor.  The [feed] (built
   by the caller — see pipeline) is the "line map": it supplies Tokens.token
   directly, gives the parser raw positions whose file pos_cnum is a side-table
   key, and resolves them.  After parsing, Cabs_location_map resolves every
   location through the feed; error locations are resolved by [to_pos].  No line
   map / global state in the lexer. *)
let parse_tokens ~filename feed =
  let enrich = feed_enrich feed in
  let to_pos x = enrich (Cerb_position.from_lexing x) in
  let `LEXER lexer = Preproc_token_feed.lexer feed in
  let dummy = Lexing.from_string "" in
  Lexing.set_filename dummy filename;
  handle C_parser.translation_unit (MenhirLib.ErrorReports.wrap lexer)
    ~to_pos ~show_token:(feed_show_token feed) dummy
  |> fun result -> Exception.except_bind result magic_comments_to_cn_toplevel
  |> Exception.except_fmap (Cabs_location_map.enrich enrich)

let parse_from_channel input =
  let read f input =
    let channel = open_in input in
    let result  = f channel in
    let ()      = close_in channel in
    result
  in
  let parse_channel ic = parse @@ Lexing.from_channel ic in
  read parse_channel input

let parse_from_string ~filename str =
  let lexbuf = Lexing.from_string str in
  Lexing.set_filename lexbuf filename;
  parse lexbuf

open Cerb_frontend

(* How to render an offending token in a parser error message differs between
   the two lexers: the text lexer reads a real lexbuf, so its lexeme can be
   sliced out of the buffer; the internal-cpp path reads a dummy lexbuf, so
   the lexeme is recovered from the raw-location map.  [handle] takes this policy
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

(* Raised by the internal-cpp token supplier when the lexer rejects a character
   inside a macro-body token.  The offending column is meaningless at the macro
   *use* site (the body text is not spelled there), so the supplier resolves it
   itself into a [Cerb_position.t] whose innermost "expanded from:" note caret is
   the bad character, and [handle] turns that into a CPARSER failure directly —
   without re-resolving any (dummy) lexbuf position. *)
exception Error_in_expansion of Errors.cparser_cause * Cerb_position.t

(* [to_pos] resolves a reported Lexing.position to a Cerb_position (it already
   bakes in the lexer's from_raw); [show_token] renders an offending lexeme.  Both
   are supplied by the caller — no line map / global state is consulted here. *)
let handle parse (token_pos_buffer, lexer) ~to_pos ~(show_token : show_token) lexbuf =
  try Exception.except_return (parse lexer lexbuf) with
  | Error_in_expansion (err, pos) ->
    Exception.fail (Cerb_location.point pos, Errors.CPARSER err)
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
  let `LEXER lexer = C_lexer.create_lexer ~inside_cn () in
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
     coordinate space, and how its positions/from_raw should compose with the outer
     translation unit (especially under the internal cpp) is left for later. *)
  let `LEXER cn_lexer = C_lexer.create_lexer ~inside_cn () in
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
  (* Text lexer: the # line-marker rule sets real positions, so from_raw defaults
     to Fun.id and no post-parse traversal is needed. *)
  let `LEXER c_lexer = C_lexer.create_lexer ~inside_cn:false () in
  handle
    C_parser.translation_unit
    (MenhirLib.ErrorReports.wrap c_lexer)
    ~to_pos:Cerb_position.from_lexing
    ~show_token:(text_show_token ~offset:0 lexbuf)
    lexbuf

let parse lexbuf =
  Exception.except_bind (parse_with_magic_comments lexbuf)
    magic_comments_to_cn_toplevel

(* Resolve a raw Lexing.position through the raw-location map: replace the
   synthetic pos_bol key with the real line-start offset (so the column comes out
   right) and attach the macro-expansion chain.  Positions not in the map (EOF,
   or any external-path position) are returned unchanged. *)
let from_raw map (p : Lexing.position) : Cerb_position.t =
  match Cpp.Preprocessor.lookup map p.Lexing.pos_bol with
  | None -> Cerb_position.from_lexing p
  | Some e ->
      let uses = List.map (fun (f : Cpp.Location.frame) ->
          Cerb_position.{ macro_name = f.Cpp.Location.macro_name
                        ; caret      = f.Cpp.Location.use })
        e.Cpp.Preprocessor.expansions in
      Cerb_position.with_expansions uses
        (Cerb_position.from_lexing
           { p with Lexing.pos_bol = e.Cpp.Preprocessor.actual_pos_bol })

(* Shift the innermost macro-use note's caret right by [offset] columns.  A lex
   error inside a macro-body token lands [offset] characters into that token's
   spelling; the innermost "expanded from:" note points at the token's start, so
   moving it by [offset] makes it land on the actual bad character. *)
let shift_innermost_caret offset pos =
  let bump (p : Lexing.position) =
    { p with Lexing.pos_cnum = p.Lexing.pos_cnum + offset } in
  match List.rev (Cerb_position.expansions pos) with
  | [] -> pos
  | inner :: rest ->
      let s, e = inner.Cerb_position.caret in
      let inner = { inner with Cerb_position.caret = (bump s, bump e) } in
      Cerb_position.with_expansions (List.rev (inner :: rest)) pos

(* Parse a token stream produced by the internal preprocessor.  [tokens] is the
   expanded pp-token list; [map] resolves each token's synthetic pos_bol key to
   its real source position and macro-expansion chain.

   A single [create_lexer] instance lexes the whole stream, exactly as on the
   text path — it carries the typedef-deferral state (the TYPE/VARIABLE markers)
   across tokens.  Each pull feeds it a fresh lexbuf holding the head token's
   lexeme, positioned at that token's real source start (accurate
   pos_cnum/lnum/fname, synthetic pos_bol key).  c_lexer then produces exactly
   the Tokens.token it would on the text path, including CERB_MAGIC for magic
   comments, and tracks positions for free: an intra-token lex error (e.g. an
   invalid string character) lands on the bad character's real pos_cnum, which
   [from_raw] resolves through the same pos_bol key.

   The deferral fires a TYPE/VARIABLE marker without consuming input, so on those
   pulls the head token is left pending and the marker inherits the name's
   position (the dummy lexbuf is left untouched).

   TODO: this function is excessively complicated — the dual-lexbuf juggling
   (one per-token [inner] plus the [dummy] that carries positions to Menhir), the
   TYPE/VARIABLE un-pop, and the bespoke error resolution should be simplified
   later, once the design has settled. *)
let parse_tokens ~filename (tokens, map) =
  let to_pos lp = from_raw map lp in
  let from_raw_pos p = from_raw map (Cerb_position.to_file_lexing p) in
  let dummy = Lexing.from_string "" in
  Lexing.set_filename dummy filename;
  let rest = ref tokens in
  let `LEXER lexer = C_lexer.create_lexer ~inside_cn:false ~from_raw:from_raw_pos () in
  (* The head pp-token (Newlines skipped), not yet consumed. *)
  let rec head () =
    match !rest with
    | tok :: tl ->
        (match Cpp.Token.kind tok with
         | Cpp.Token.Newline -> rest := tl; head ()
         | _ -> Some tok)
    | [] -> None
  in
  let supplier _ =
    let h = head () in
    (* [start] is the token's primary caret (the macro use for an expanded token);
       [inner] holds the lexeme positioned there so c_lexer tracks real columns. *)
    let start, inner = match h with
      | Some tok ->
          let lb = Lexing.from_string (Cpp.Token.lexeme tok) in
          let s, _ = Cpp.Location.primary (Cpp.Token.loc tok) in
          Lexing.set_filename lb s.Lexing.pos_fname;
          Lexing.set_position lb s;
          (s, lb)
      | None ->
          (* Drained: an empty lexbuf yields EOF.  pos_bol = -1 is not a key, so
             from_raw leaves the EOF position alone. *)
          let lb = Lexing.from_string "" in
          let s = { Lexing.dummy_pos with pos_bol = -1 } in
          Lexing.set_position lb s;
          (s, lb)
    in
    let t =
      try lexer inner
      with C_lexer.Error err as ex ->
        (match Cpp.Preprocessor.lookup map start.Lexing.pos_bol with
         | Some e when (match e.Cpp.Preprocessor.expansions with [] -> false | _ :: _ -> true) ->
             (* The token came from a macro body: the bad character sits [offset]
                chars into its spelling, which is at the macro use site here.  Resolve
                the position ourselves so the innermost "expanded from:" note caret
                lands on the bad character, and raise it through [handle]. *)
             let offset = inner.Lexing.lex_start_p.Lexing.pos_cnum - start.Lexing.pos_cnum in
             let pos = shift_innermost_caret offset (from_raw map start) in
             raise (Error_in_expansion (err, pos))
         | _ ->
             (* Ordinary token: the bad character's real position is accurate. *)
             dummy.Lexing.lex_start_p <- inner.Lexing.lex_start_p;
             dummy.Lexing.lex_curr_p  <- inner.Lexing.lex_start_p;
             raise ex)
    in
    (match t with
     | Tokens.TYPE | Tokens.VARIABLE ->
         (* Deferral marker: [inner] was not consumed, so the head token is still
            pending.  Leave the dummy positions as the name's. *)
         ()
     | _ ->
         (match h with Some _ -> rest := List.tl !rest | None -> ());
         dummy.Lexing.lex_start_p <- inner.Lexing.lex_start_p;
         dummy.Lexing.lex_curr_p  <- inner.Lexing.lex_curr_p);
    t
  in
  let show_token (start, _) =
    match Cpp.Preprocessor.lookup map start.Lexing.pos_bol with
    | Some e -> e.Cpp.Preprocessor.lexeme
    | None -> ""
  in
  handle C_parser.translation_unit (MenhirLib.ErrorReports.wrap supplier)
    ~to_pos ~show_token dummy
  |> fun result -> Exception.except_bind result magic_comments_to_cn_toplevel
  |> Exception.except_fmap (Cabs_location_map.from_raw from_raw_pos)

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

(* A token supplier is inherently stateful — it is pulled repeatedly by Menhir —
   so this module holds mutable state (the cursor into the expanded stream, the
   growing side table, and the key counter), mirroring c_lexer's create_lexer.
   [make] allocates it fresh per parse. *)
type t =
  { mutable rest : Preproc_location.t Preproc_token.t list
  ; table        : (int, Cerb_position.t) Hashtbl.t
  ; mutable counter : int }

let make toks = { rest = toks; table = Hashtbl.create 256; counter = 0 }

let lookup t k = Hashtbl.find_opt t.table k

(* Map a token's Preproc_location into the macro-expansion notes the diagnostic
   renderer will show: the primary caret is the outermost use site, so the notes
   are the *inner* invocation sites (the remaining frames' use regions) followed
   by the token's own spelling in the innermost macro body.  Ordinary (unexpanded)
   tokens get no notes. *)
let macro_frames loc =
  match Preproc_location.expansion loc with
  | [] -> []
  | _outermost :: inner ->
      List.map
        (fun (f : Preproc_location.frame) ->
           Cerb_position.{ macro_name = f.macro_name; caret = f.use })
        inner
      @ [ Cerb_position.{ macro_name = None
                        ; caret = Preproc_location.spelling loc } ]

(* Allocate a side-table key for a precomputed Cerb_position and return a
   Lexing.position whose pos_cnum is that key (other fields irrelevant — the seam
   reads only the key). *)
let key_position t cp =
  let k = t.counter in
  t.counter <- t.counter + 1;
  Hashtbl.replace t.table k cp;
  { Lexing.dummy_pos with pos_cnum = k }

(* Build CERB_MAGIC's payload region from the magic token's full comment span:
   drop the three opening characters (slash star delim) and the two closing
   characters (star slash). *)
let magic_token loc (m : Preproc_token.magic) =
  let s_full, e_full = Preproc_location.spelling loc in
  let payload_start = Cerb_position.change_cnum (Cerb_position.from_lexing s_full) 3 in
  let payload_end = Cerb_position.change_cnum (Cerb_position.from_lexing e_full) (-2) in
  let region =
    Cerb_location.region (payload_start, payload_end) Cerb_location.NoCursor in
  Tokens.CERB_MAGIC (region, (m.delimiter, m.payload))

(* Set the lexbuf positions for a token spanning [start_loc].[end_loc], keying
   the side table to the precomputed Cerb_positions (provenance from start). *)
let emit_positions t lexbuf start_loc end_loc =
  let frames = macro_frames start_loc in
  let s, _ = Preproc_location.primary start_loc in
  let _, e = Preproc_location.primary end_loc in
  lexbuf.Lexing.lex_start_p <-
    key_position t (Cerb_position.with_provenance frames (Cerb_position.from_lexing s));
  lexbuf.Lexing.lex_curr_p <-
    key_position t (Cerb_position.with_provenance frames (Cerb_position.from_lexing e))

let rec next t lexbuf =
  match t.rest with
  | [] ->
      let p = key_position t Cerb_position.dummy in
      lexbuf.Lexing.lex_start_p <- p;
      lexbuf.Lexing.lex_curr_p <- p;
      Tokens.EOF
  | tok :: rest ->
      (match Preproc_token.kind tok with
       | Preproc_token.Newline -> t.rest <- rest; next t lexbuf
       | Preproc_token.Magic m ->
           t.rest <- rest;
           emit_positions t lexbuf (Preproc_token.loc tok) (Preproc_token.loc tok);
           magic_token (Preproc_token.loc tok) m
       | _ ->
           t.rest <- rest;
           emit_positions t lexbuf (Preproc_token.loc tok) (Preproc_token.loc tok);
           C_lexer.token_of_string ~inside_cn:false (Preproc_token.spelling tok))

let lexer t = C_lexer.defer_typedef (fun lexbuf -> next t lexbuf)

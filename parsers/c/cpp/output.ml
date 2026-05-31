(* The reconstruction is line-oriented: [has_content] tracks whether the current
   logical line has emitted any token, so leading indentation is suppressed (a
   token's [preceded_by_space] only matters once content is present) and blank
   lines collapse (a Newline with no content emits nothing).

   The paste-avoiding / doubled-space refinements cscout applies to
   macro-expanded output are not needed yet — phase-3 source tokens are already
   maximally munched — and are added alongside the macro engine. *)
let reconstruct toks =
  let buf = Buffer.create 256 in
  let rec go has_content = function
    | [] ->
        if has_content then Buffer.add_char buf '\n'
    | t :: rest ->
        let has_content =
          match Token.kind t with
          | Token.Newline ->
              (* cscout keeps a single trailing space before the newline when the
                 source had whitespace there (the Newline token records it). *)
              if has_content then begin
                if Token.preceded_by_space t then Buffer.add_char buf ' ';
                Buffer.add_char buf '\n'
              end;
              false
          | _ ->
              if has_content && Token.preceded_by_space t then
                Buffer.add_char buf ' ';
              Buffer.add_string buf (Token.lexeme t);
              true
        in
        go has_content rest
  in
  go false toks;
  Buffer.contents buf

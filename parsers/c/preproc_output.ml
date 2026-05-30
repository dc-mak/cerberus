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
          match Preproc_token.kind t with
          | Preproc_token.Newline ->
              (* cscout keeps a single trailing space before the newline when the
                 source had whitespace there (the Newline token records it). *)
              if has_content then begin
                if Preproc_token.preceded_by_space t then Buffer.add_char buf ' ';
                Buffer.add_char buf '\n'
              end;
              false
          | _ ->
              if has_content && Preproc_token.preceded_by_space t then
                Buffer.add_char buf ' ';
              Buffer.add_string buf (Preproc_token.spelling t);
              true
        in
        go has_content rest
  in
  go false toks;
  Buffer.contents buf

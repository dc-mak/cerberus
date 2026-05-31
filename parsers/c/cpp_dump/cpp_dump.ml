(* Standalone oracle for the internal preprocessor: read a C file, run phase-3
   tokenisation and the macro engine, and print the reconstructed text so it can
   be diffed against the cscout goldens via tests/diff-prog.py.  See
   tests/preprocessor/README.md.

   With [--expand-magic], each CN magic comment's payload is additionally
   macro-expanded (using the macro table captured for it) and reconstructed
   inline.  This is opt-in because the engine deliberately leaves magic payloads
   opaque — their real expansion happens later, at CN re-parse — and the default
   dump must stay byte-identical to the cscout goldens (cscout has no notion of
   magic comments). *)

(* Replace each [Magic] token with one whose payload has been macro-expanded with
   the table in scope at that comment.  The synthetic key [assign_keys] stored in
   the token's primary pos_bol is the same key [macro_defns] is keyed by. *)
let expand_magic_payloads macro_defns toks =
  List.map (fun tok ->
    match Cpp.Token.kind tok with
    | Cpp.Token.Magic { delimiter; payload } ->
        let key = (fst (Cpp.Location.primary (Cpp.Token.loc tok))).Lexing.pos_bol in
        (match Cpp.Preprocessor.find_macro_defns macro_defns key with
         | None -> tok
         | Some macros ->
             let ftoks, _ =
               Cpp.Preprocessor.expand_fragment macros (Lexing.from_string payload) in
             let expanded = String.trim (Cpp.Output.reconstruct ftoks) in
             let lexeme = Printf.sprintf "/*%c %s %c*/" delimiter expanded delimiter in
             Cpp.Token.make
               ~kind:(Cpp.Token.Magic { delimiter; payload = expanded })
               ~lexeme
               ~preceded_by_space:(Cpp.Token.preceded_by_space tok)
               ~loc:(Cpp.Token.loc tok) ())
    | _ -> tok
  ) toks

let run ~expand_magic path =
  let toks, _, macro_defns =
    Cpp.Preprocessor.preprocess ~include_dirs:[] ~predefined:[] ~undefs:[]
      ~forced_includes:[] ~filename:path
  in
  let toks = if expand_magic then expand_magic_payloads macro_defns toks else toks in
  print_string (Cpp.Output.reconstruct toks)

let () =
  match Sys.argv with
  | [| _; path |] -> run ~expand_magic:false path
  | [| _; "--expand-magic"; path |] -> run ~expand_magic:true path
  | _ ->
      prerr_endline "usage: cpp_dump [--expand-magic] <file.c>";
      exit 2

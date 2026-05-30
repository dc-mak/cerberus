(* Standalone oracle for the internal preprocessor: read a C file, run phase-3
   tokenisation and the macro engine, and print the reconstructed text so it can
   be diffed against the cscout goldens via tests/diff-prog.py.  See
   tests/preprocessor/README.md. *)

let () =
  match Sys.argv with
  | [| _; path |] ->
      let toks =
        Cpp.preprocess ~include_dirs:[] ~predefined:[] ~undefs:[]
          ~forced_includes:[] ~filename:path
      in
      print_string (Preproc_output.reconstruct toks)
  | _ ->
      prerr_endline "usage: cpp_dump <file.c>";
      exit 2

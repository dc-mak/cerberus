(* The macro engine.  Names follow Prosser's pseudocode (design doc Appendix A):
   [expand] rescans a token sequence, [subst] instantiates a replacement list,
   [glue] pastes across ##, [hsadd] adds a hide set to every token, [stringize]
   realises #.  Provenance is orthogonal to the algorithm — hide sets stop
   re-expansion, while expansion frames are pushed as [subst] copies body
   tokens. *)

module HS = Preproc_token.Hide_set
module SS = Set.Make (String)

(* --- Token predicates ------------------------------------------------------ *)

let is_ident t =
  match Preproc_token.kind t with Preproc_token.Identifier -> true | _ -> false

let is_newline t =
  match Preproc_token.kind t with Preproc_token.Newline -> true | _ -> false

let is_punct s t =
  match Preproc_token.kind t with
  | Preproc_token.Punctuator -> String.equal (Preproc_token.spelling t) s
  | _ -> false

(* --- Provenance ------------------------------------------------------------ *)

(* Rebase a macro-body token onto the invocation site's provenance: keep its own
   spelling (a position in the macro body) but make its expansion chain the
   invoking token's chain extended by one frame for this macro, so nested
   expansions nest the way Clang's "expanded from:" notes do. *)
let push_frames frames loc =
  let rec go loc = function
    | [] -> loc
    | f :: fs -> go (Preproc_location.push_expansion f loc) fs
  in
  go loc frames

let rebase ~name ~invoked_at bt =
  let frame =
    Preproc_location.
      { macro_name = Some name
      ; use = Preproc_location.spelling (Preproc_token.loc invoked_at) }
  in
  let frames =
    Preproc_location.expansion (Preproc_token.loc invoked_at) @ [ frame ] in
  let loc' = push_frames frames (Preproc_token.loc bt) in
  Preproc_token.map (fun _ -> loc') bt

(* hsadd(HS, TS): union HS into every token's hide set. *)
let rec hsadd hs = function
  | [] -> []
  | t :: ts ->
      let t = Preproc_token.with_hide_set (HS.union hs (Preproc_token.hide_set t)) t in
      t :: hsadd hs ts

(* --- # and ## -------------------------------------------------------------- *)

(* §6.10.3.2: only a backslash and double-quote *within* a string-literal or
   character-constant spelling are escaped when stringizing. *)
let escape_for_string s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (fun c ->
       if Char.equal c '"' || Char.equal c '\\' then Buffer.add_char buf '\\';
       Buffer.add_char buf c)
    s;
  Buffer.contents buf

(* stringize(TS): one string-literal token from the actual's spellings, interior
   white-space collapsed to single spaces, leading/trailing dropped. *)
let stringize ~name ~invoked_at ~at actual =
  let buf = Buffer.create 16 in
  Buffer.add_char buf '"';
  List.iteri
    (fun i tok ->
       if i > 0 && Preproc_token.preceded_by_space tok then Buffer.add_char buf ' ';
       let s = Preproc_token.spelling tok in
       let s =
         match Preproc_token.kind tok with
         | Preproc_token.String_literal | Preproc_token.Char_const ->
             escape_for_string s
         | _ -> s
       in
       Buffer.add_string buf s)
    actual;
  Buffer.add_char buf '"';
  let tok =
    Preproc_token.make ~kind:Preproc_token.String_literal
      ~spelling:(Buffer.contents buf)
      ~preceded_by_space:(Preproc_token.preceded_by_space at)
      ~loc:(Preproc_token.loc at) ()
  in
  rebase ~name ~invoked_at tok

(* The kind a pasted spelling lexes to, so an identifier produced by ## is still
   recognised as a macro on rescan. *)
let paste_kind spelling =
  let toks = Preproc_lexer.tokens (Lexing.from_string spelling) in
  match List.filter (fun t -> not (is_newline t)) toks with
  | [ t ] -> Preproc_token.kind t
  | _ -> Preproc_token.Other

(* glue(LS, RS): paste the last token of LS onto the first of RS. *)
let rec glue ls rs =
  match ls with
  | [] -> rs
  | [ l ] ->
      (match rs with
       | [] -> [ l ]
       | r :: rs' ->
           let spelling = Preproc_token.spelling l ^ Preproc_token.spelling r in
           let hide_set = HS.inter (Preproc_token.hide_set l) (Preproc_token.hide_set r) in
           let pasted =
             Preproc_token.make ~kind:(paste_kind spelling) ~spelling
               ~preceded_by_space:(Preproc_token.preceded_by_space l)
               ~hide_set ~loc:(Preproc_token.loc l) ()
           in
           pasted :: rs')
  | l :: ls' -> l :: glue ls' rs

(* --- Argument handling ----------------------------------------------------- *)

(* Collect a function-like macro's actuals, starting just after the '('.  Splits
   on commas at paren depth 0, stops at the matching ')'.  Newlines collapse to
   leading white-space on the following token.  Returns the actuals, the closing
   paren's hide set, and the tokens after ')'; None if unterminated. *)
let collect_args toks =
  let rec go depth space cur args = function
    | [] -> None
    | t :: rest when is_newline t -> go depth true cur args rest
    | t :: rest ->
        let t = if space then Preproc_token.with_preceded_by_space true t else t in
        if depth = 0 && is_punct ")" t then
          Some (List.rev (List.rev cur :: args), Preproc_token.hide_set t, rest)
        else if depth = 0 && is_punct "," t then
          go 0 false [] (List.rev cur :: args) rest
        else
          let depth =
            if is_punct "(" t then depth + 1
            else if is_punct ")" t then depth - 1
            else depth
          in
          go depth false (t :: cur) args rest
  in
  go 0 false [] [] toks

(* A synthetic comma to rejoin the actuals folded into __VA_ARGS__. *)
let synth_comma =
  Preproc_token.make ~kind:Preproc_token.Punctuator ~spelling:","
    ~preceded_by_space:false
    ~loc:(Preproc_location.of_lexing (Lexing.dummy_pos, Lexing.dummy_pos)) ()

let rec join_with_commas = function
  | [] -> []
  | [ a ] -> a
  | a :: rest -> a @ (synth_comma :: join_with_commas rest)

(* Map each formal parameter (and __VA_ARGS__ for a variadic macro) to its
   actual.  A lone empty actual for a zero-parameter macro — f() — yields no
   bindings. *)
let build_assoc params variadic actuals =
  let rec zip ps acts acc =
    match ps, acts with
    | [], rest ->
        if variadic then List.rev (("__VA_ARGS__", join_with_commas rest) :: acc)
        else List.rev acc
    | p :: ps', a :: acts' -> zip ps' acts' ((p, a) :: acc)
    | p :: ps', [] -> zip ps' [] ((p, []) :: acc)
  in
  zip params actuals []

let actual_of assoc t =
  match Preproc_token.kind t with
  | Preproc_token.Identifier -> List.assoc_opt (Preproc_token.spelling t) assoc
  | _ -> None

let is_param assoc t =
  match actual_of assoc t with Some _ -> true | None -> false

let rec skip_newlines = function
  | t :: ts when is_newline t -> skip_newlines ts
  | ts -> ts

(* A replacement list's (or argument's) own leading white-space is not
   significant: the first token produced takes the spacing of the macro name (or
   parameter) it stands in for. *)
let set_first_space space = function
  | [] -> []
  | t :: ts -> Preproc_token.with_preceded_by_space space t :: ts

(* --- expand / subst -------------------------------------------------------- *)

(* subst(IS, FP, AP, HS, OS) over the formal/actual binding [assoc].  Cases are
   in Prosser's order; the parameter case re-expands the actual ([expand]),
   which is why this is mutually recursive with [expand]. *)
let rec subst macros ~name ~invoked_at assoc is hs os =
  match is with
  (* # • T  with T a parameter *)
  | h :: t :: is' when is_punct "#" h && is_param assoc t ->
      let actual = Option.value (actual_of assoc t) ~default:[] in
      let s = stringize ~name ~invoked_at ~at:h actual in
      subst macros ~name ~invoked_at assoc is' hs (os @ [ s ])
  (* ## • T  with T a parameter *)
  | h :: t :: is' when is_punct "##" h && is_param assoc t ->
      (match Option.value (actual_of assoc t) ~default:[] with
       | [] -> subst macros ~name ~invoked_at assoc is' hs os
       | actual -> subst macros ~name ~invoked_at assoc is' hs (glue os actual))
  (* ## • T  with T an ordinary token *)
  | h :: t :: is' when is_punct "##" h ->
      subst macros ~name ~invoked_at assoc is' hs (glue os [ t ])
  (* T • ## ...  with T a parameter *)
  | t :: h :: is' when is_param assoc t && is_punct "##" h ->
      (match Option.value (actual_of assoc t) ~default:[] with
       | [] ->
           (match is' with
            | t' :: is'' when is_param assoc t' ->
                let act2 = Option.value (actual_of assoc t') ~default:[] in
                subst macros ~name ~invoked_at assoc is'' hs (os @ act2)
            | _ -> subst macros ~name ~invoked_at assoc is' hs os)
       | actual ->
           subst macros ~name ~invoked_at assoc (h :: is') hs (os @ actual))
  (* T  a parameter: substitute the *expanded* actual, whose first token takes
     the parameter's spacing *)
  | t :: is' when is_param assoc t ->
      let actual = Option.value (actual_of assoc t) ~default:[] in
      let sub = set_first_space (Preproc_token.preceded_by_space t) (expand macros actual) in
      subst macros ~name ~invoked_at assoc is' hs (os @ sub)
  (* otherwise: copy the body token, recording provenance *)
  | t :: is' ->
      let t = rebase ~name ~invoked_at t in
      subst macros ~name ~invoked_at assoc is' hs (os @ [ t ])
  | [] -> hsadd hs os

(* expand(TS): rescan, replacing macro names not already in their own hide set. *)
and expand macros = function
  | [] -> []
  | t :: ts when is_ident t ->
      let name = Preproc_token.spelling t in
      if HS.mem name (Preproc_token.hide_set t) then t :: expand macros ts
      else begin
        match Macro_table.find name macros with
        | Some (Macro_table.Object_like body) ->
            let hs = HS.add name (Preproc_token.hide_set t) in
            let out = subst macros ~name ~invoked_at:t [] body hs [] in
            let out = set_first_space (Preproc_token.preceded_by_space t) out in
            expand macros (out @ ts)
        | Some (Macro_table.Function_like { params; variadic; body }) ->
            (* Invoked only if the next token (past any newlines) is '('. *)
            (match skip_newlines ts with
             | lp :: after when is_punct "(" lp ->
                 (match collect_args after with
                  | Some (actuals, close_hs, rest) ->
                      let assoc = build_assoc params variadic actuals in
                      let hs = HS.add name (HS.inter (Preproc_token.hide_set t) close_hs) in
                      let out = subst macros ~name ~invoked_at:t assoc body hs [] in
                      let out = set_first_space (Preproc_token.preceded_by_space t) out in
                      expand macros (out @ rest)
                  | None -> t :: expand macros ts)
             | _ -> t :: expand macros ts)
        | None -> t :: expand macros ts
      end
  | t :: ts -> t :: expand macros ts

(* --- Directive parsing ----------------------------------------------------- *)

(* Parse a function-like macro's parameter list, starting just after the '('. *)
let rec parse_params acc = function
  | t :: rest when is_punct ")" t -> (List.rev acc, false, rest)
  | t :: rest when is_punct "..." t ->
      let rest = match rest with r :: rs when is_punct ")" r -> rs | rs -> rs in
      (List.rev acc, true, rest)
  | t :: rest when is_ident t ->
      let acc = Preproc_token.spelling t :: acc in
      (match rest with
       | c :: rest' when is_punct "," c -> parse_params acc rest'
       | r :: rest' when is_punct ")" r -> (List.rev acc, false, rest')
       | _ -> (List.rev acc, false, rest))
  | rest -> (List.rev acc, false, rest)

let do_define macros = function
  | name :: rest when is_ident name ->
      let def =
        match rest with
        | lp :: rest'
          when is_punct "(" lp && not (Preproc_token.preceded_by_space lp) ->
            let params, variadic, body = parse_params [] rest' in
            Macro_table.Function_like { params; variadic; body }
        | _ -> Macro_table.Object_like rest
      in
      (match Macro_table.define (Preproc_token.spelling name) def macros with
       | Ok macros' -> macros'
       (* Incompatible redefinition: keep the existing definition for now;
          diagnostics arrive with the frontend integration. *)
       | Error _ -> macros)
  | _ -> macros

let do_undef macros = function
  | n :: _ when is_ident n -> Macro_table.undef (Preproc_token.spelling n) macros
  | _ -> macros

(* --- Conditional inclusion (§6.10.1) --------------------------------------- *)

(* One #if/#ifdef/#ifndef group on the conditional stack.  [outer] records
   whether the enclosing context was emitting (a group nested in a skipped region
   never activates any branch); [taken] whether some branch has matched; [active]
   whether the current branch emits (already accounts for [outer]). *)
type cond = { outer : bool; taken : bool; active : bool }

let emitting = function [] -> true | f :: _ -> f.active

(* Substitute each literal [defined X] / [defined(X)] with 0 or 1 before the line
   is macro-expanded, so the operand is not itself expanded. *)
let mk_num present template =
  Preproc_token.make ~kind:Preproc_token.Pp_number
    ~spelling:(if present then "1" else "0")
    ~preceded_by_space:(Preproc_token.preceded_by_space template)
    ~loc:(Preproc_token.loc template) ()

let rec replace_defined macros = function
  | d :: rest
    when is_ident d && String.equal (Preproc_token.spelling d) "defined" ->
      (match rest with
       | lp :: n :: rp :: rest'
         when is_punct "(" lp && is_ident n && is_punct ")" rp ->
           mk_num (Macro_table.mem (Preproc_token.spelling n) macros) d
           :: replace_defined macros rest'
       | n :: rest' when is_ident n ->
           mk_num (Macro_table.mem (Preproc_token.spelling n) macros) d
           :: replace_defined macros rest'
       | _ -> d :: replace_defined macros rest)
  | t :: rest -> t :: replace_defined macros rest
  | [] -> []

(* Evaluate a #if / #elif controlling expression: resolve [defined], expand, then
   hand the result to Cpp_eval.  An ill-formed expression counts as false. *)
let eval_cond macros toks =
  let expanded = expand macros (replace_defined macros toks) in
  match Cpp_eval.eval expanded with Ok b -> b | Error _ -> false

let push_if conds ~outer ~cond =
  let active = outer && cond in
  { outer; taken = active; active } :: conds

let do_elif conds eval_branch =
  match conds with
  | f :: rest ->
      if (not f.outer) || f.taken then { f with active = false } :: rest
      else let b = eval_branch () in { f with active = b; taken = b } :: rest
  | [] -> conds  (* stray #elif: ignored *)

let do_else conds =
  match conds with
  | f :: rest ->
      let active = f.outer && not f.taken in
      { f with active; taken = true } :: rest
  | [] -> conds

let do_endif conds = match conds with _ :: rest -> rest | [] -> []

(* Dispatch one directive, given whether we are currently emitting.  Returns the
   updated macro table and conditional stack. *)
let apply_directive macros conds ds =
  let em = emitting conds in
  match ds with
  | [] -> (macros, conds)  (* null directive *)
  | d :: rest ->
      (match Preproc_token.spelling d with
       | "define" -> ((if em then do_define macros rest else macros), conds)
       | "undef" -> ((if em then do_undef macros rest else macros), conds)
       | "ifdef" ->
           let cond =
             match rest with n :: _ -> Macro_table.mem (Preproc_token.spelling n) macros | _ -> false in
           (macros, push_if conds ~outer:em ~cond)
       | "ifndef" ->
           let cond =
             match rest with n :: _ -> not (Macro_table.mem (Preproc_token.spelling n) macros) | _ -> false in
           (macros, push_if conds ~outer:em ~cond)
       | "if" -> (macros, push_if conds ~outer:em ~cond:(em && eval_cond macros rest))
       | "elif" -> (macros, do_elif conds (fun () -> eval_cond macros rest))
       | "else" -> (macros, do_else conds)
       | "endif" -> (macros, do_endif conds)
       (* #include / #line / #pragma / #error handled in later commits *)
       | _ -> (macros, conds))

(* --- Line-oriented driver -------------------------------------------------- *)

(* Segment the stream into logical lines, keeping each line's terminating Newline
   token so non-directive lines can re-emit it. *)
let split_lines toks =
  let rec go cur = function
    | [] -> [ (List.rev cur, None) ]
    | t :: ts when is_newline t -> (List.rev cur, Some t) :: go [] ts
    | t :: ts -> go (t :: cur) ts
  in
  go [] toks

(* --- #include resolution ---------------------------------------------------- *)

(* Read a file and lift it to the engine's located pp-token stream. *)
let lex_file filename =
  let ic = open_in filename in
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf filename;
  let toks = Preproc_lexer.tokens lexbuf in
  close_in ic;
  List.map (Preproc_token.map Preproc_location.of_lexing) toks

(* The header name and whether it was the angle-bracket form, from the tokens
   after `include`.  "..." takes the string-literal content; <...> concatenates
   the spellings between the brackets.  (Computed/macro includes are not yet
   handled.) *)
let include_target ds =
  match ds with
  | s :: _ when (match Preproc_token.kind s with
                 | Preproc_token.String_literal -> true | _ -> false) ->
      let sp = Preproc_token.spelling s in
      if String.length sp >= 2 then Some (String.sub sp 1 (String.length sp - 2), false)
      else None
  | t :: rest when is_punct "<" t ->
      let rec collect acc = function
        | u :: _ when is_punct ">" u -> Some (String.concat "" (List.rev acc))
        | u :: us -> collect (Preproc_token.spelling u :: acc) us
        | [] -> None
      in
      (match collect [] rest with Some n -> Some (n, true) | None -> None)
  | _ -> None

(* "..." searches the current file's directory first, then the -I dirs; <...>
   searches only the -I dirs (no system paths, matching -nostdinc -undef). *)
let resolve ~include_dirs ~dir ~angled name =
  let dirs = if angled then include_dirs else dir :: include_dirs in
  let rec find = function
    | [] -> None
    | d :: ds ->
        let p = Filename.concat d name in
        if Sys.file_exists p then Some p else find ds
  in
  find dirs

(* --- Line-oriented driver (per file, threading macros + #pragma once) ------- *)

(* Process one file's lines.  [conds] is local (a #if must close in its file);
   [macros] and [once] thread across includes.  Output is accumulated as a
   reversed list of token chunks.  Emitting runs of non-directive lines are
   expanded together (function-like invocations may span newlines); a directive
   flushes the pending text and emits nothing.  In a skipped region text is
   dropped but conditionals are still tracked. *)
let rec process_lines ~include_dirs ~dir ~canon macros once acc conds pending lines =
  match lines with
  | [] ->
      (expand macros (List.concat (List.rev pending)) :: acc, macros, once)
  | (ltoks, nl) :: rest ->
      (match ltoks with
       | t :: ds when is_punct "#" t ->
           let em = emitting conds in
           let flushed =
             if em then expand macros (List.concat (List.rev pending)) else [] in
           let acc = flushed :: acc in
           (match ds with
            | d :: drest
              when em && is_ident d
                   && String.equal (Preproc_token.spelling d) "include" ->
                let inc, macros, once = do_include ~include_dirs ~dir macros once drest in
                process_lines ~include_dirs ~dir ~canon macros once (inc :: acc) conds [] rest
            | d :: e :: _
              when em && is_ident d && is_ident e
                   && String.equal (Preproc_token.spelling d) "pragma"
                   && String.equal (Preproc_token.spelling e) "once" ->
                process_lines ~include_dirs ~dir ~canon macros (SS.add canon once) acc conds [] rest
            | _ ->
                let macros, conds = apply_directive macros conds ds in
                process_lines ~include_dirs ~dir ~canon macros once acc conds [] rest)
       | _ ->
           if emitting conds then
             let chunk = match nl with Some n -> ltoks @ [ n ] | None -> ltoks in
             process_lines ~include_dirs ~dir ~canon macros once acc conds (chunk :: pending) rest
           else
             process_lines ~include_dirs ~dir ~canon macros once acc conds pending rest)

(* Resolve and splice an included file, sharing the macro table and honouring
   #pragma once (keyed by resolved path).  A missing header is skipped silently
   here; the frontend integration will diagnose it. *)
and do_include ~include_dirs ~dir macros once ds =
  match include_target ds with
  | None -> ([], macros, once)
  | Some (name, angled) ->
      (match resolve ~include_dirs ~dir ~angled name with
       | None -> ([], macros, once)
       | Some path when SS.mem path once -> ([], macros, once)
       | Some path ->
           let lines = split_lines (lex_file path) in
           let acc, macros, once =
             process_lines ~include_dirs ~dir:(Filename.dirname path) ~canon:path
               macros once [] [] [] lines
           in
           (List.concat (List.rev acc), macros, once))

let preprocess ~include_dirs ~filename =
  let lines = split_lines (lex_file filename) in
  let acc, _, _ =
    process_lines ~include_dirs ~dir:(Filename.dirname filename) ~canon:filename
      Macro_table.empty SS.empty [] [] [] lines
  in
  List.concat (List.rev acc)

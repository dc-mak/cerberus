(* The macro engine.  Names follow Prosser's pseudocode (design doc Appendix A):
   [expand] rescans a token sequence, [subst] instantiates a replacement list,
   [glue] pastes across ##, [hsadd] adds a hide set to every token, [stringize]
   realises #.  Provenance is orthogonal to the algorithm — hide sets stop
   re-expansion, while expansion frames are pushed as [subst] copies body
   tokens. *)

module HS = Token.Hide_set
module SS = Set.Make (String)

(* --- Token predicates ------------------------------------------------------ *)

let is_ident t =
  match Token.kind t with Token.Identifier -> true | _ -> false

let is_newline t =
  match Token.kind t with Token.Newline -> true | _ -> false

let is_punct s t =
  match Token.kind t with
  | Token.Punctuator -> String.equal (Token.lexeme t) s
  | _ -> false

(* --- Provenance ------------------------------------------------------------ *)

(* Rebase a macro-body token onto the invocation site's provenance: keep its own
   lexeme (a position in the macro body) but make its expansion chain the
   invoking token's chain extended by one frame for this macro, so nested
   expansions nest the way Clang's "expanded from:" notes do. *)
let push_frames frames loc =
  let rec go loc = function
    | [] -> loc
    | f :: fs -> go (Location.push_expansion f loc) fs
  in
  go loc frames

let rebase ~name ~invoked_at bt =
  let frame =
    Location.
      { macro_name = Some name
      ; use = Location.lexeme (Token.loc invoked_at) }
  in
  let frames =
    Location.expansion (Token.loc invoked_at) @ [ frame ] in
  let loc' = push_frames frames (Token.loc bt) in
  Token.map (fun _ -> loc') bt

(* hsadd(HS, TS): union HS into every token's hide set. *)
let rec hsadd hs = function
  | [] -> []
  | t :: ts ->
      let t = Token.with_hide_set (HS.union hs (Token.hide_set t)) t in
      t :: hsadd hs ts

(* --- # and ## -------------------------------------------------------------- *)

(* §6.10.3.2: only a backslash and double-quote *within* a string-literal or
   character-constant lexeme are escaped when stringizing. *)
let escape_for_string s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (fun c ->
       if Char.equal c '"' || Char.equal c '\\' then Buffer.add_char buf '\\';
       Buffer.add_char buf c)
    s;
  Buffer.contents buf

(* stringize(TS): one string-literal token from the actual's lexemes, interior
   white-space collapsed to single spaces, leading/trailing dropped. *)
let stringize ~name ~invoked_at ~at actual =
  let buf = Buffer.create 16 in
  Buffer.add_char buf '"';
  List.iteri
    (fun i tok ->
       if i > 0 && Token.preceded_by_space tok then Buffer.add_char buf ' ';
       let s = Token.lexeme tok in
       let s =
         match Token.kind tok with
         | Token.String_literal | Token.Char_const ->
             escape_for_string s
         | _ -> s
       in
       Buffer.add_string buf s)
    actual;
  Buffer.add_char buf '"';
  let tok =
    Token.make ~kind:Token.String_literal
      ~lexeme:(Buffer.contents buf)
      ~preceded_by_space:(Token.preceded_by_space at)
      ~loc:(Token.loc at) ()
  in
  rebase ~name ~invoked_at tok

(* The kind a pasted lexeme lexes to, so an identifier produced by ## is still
   recognised as a macro on rescan. *)
let paste_kind lexeme =
  let toks = Lexer.tokens (Lexing.from_string lexeme) in
  match List.filter (fun t -> not (is_newline t)) toks with
  | [ t ] -> Token.kind t
  | _ -> Token.Other

(* glue(LS, RS): paste the last token of LS onto the first of RS. *)
let rec glue ls rs =
  match ls with
  | [] -> rs
  | [ l ] ->
      (match rs with
       | [] -> [ l ]
       | r :: rs' ->
           let lexeme = Token.lexeme l ^ Token.lexeme r in
           let hide_set = HS.inter (Token.hide_set l) (Token.hide_set r) in
           let pasted =
             Token.make ~kind:(paste_kind lexeme) ~lexeme
               ~preceded_by_space:(Token.preceded_by_space l)
               ~hide_set ~loc:(Token.loc l) ()
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
        let t = if space then Token.with_preceded_by_space true t else t in
        if depth = 0 && is_punct ")" t then
          Some (List.rev (List.rev cur :: args), Token.hide_set t, rest)
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
  Token.make ~kind:Token.Punctuator ~lexeme:","
    ~preceded_by_space:false
    ~loc:(Location.of_lexing (Lexing.dummy_pos, Lexing.dummy_pos)) ()

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
  match Token.kind t with
  | Token.Identifier -> List.assoc_opt (Token.lexeme t) assoc
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
  | t :: ts -> Token.with_preceded_by_space space t :: ts

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
     the parameter's spacing.  Argument tokens keep their own spelling (the call
     site) and their own expansion chain — they are NOT "expanded from" this
     macro, so no frame for it is added here. *)
  | t :: is' when is_param assoc t ->
      let actual = Option.value (actual_of assoc t) ~default:[] in
      let sub = set_first_space (Token.preceded_by_space t) (expand macros actual) in
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
      let name = Token.lexeme t in
      if HS.mem name (Token.hide_set t) then t :: expand macros ts
      else begin
        match Macro_table.find name macros with
        | Some (Macro_table.Object_like body) ->
            let hs = HS.add name (Token.hide_set t) in
            let out = subst macros ~name ~invoked_at:t [] body hs [] in
            let out = set_first_space (Token.preceded_by_space t) out in
            expand macros (out @ ts)
        | Some (Macro_table.Function_like { params; variadic; body }) ->
            (* Invoked only if the next token (past any newlines) is '('. *)
            (match skip_newlines ts with
             | lp :: after when is_punct "(" lp ->
                 (match collect_args after with
                  | Some (actuals, close_hs, rest) ->
                      let assoc = build_assoc params variadic actuals in
                      let hs = HS.add name (HS.inter (Token.hide_set t) close_hs) in
                      let out = subst macros ~name ~invoked_at:t assoc body hs [] in
                      let out = set_first_space (Token.preceded_by_space t) out in
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
      let acc = Token.lexeme t :: acc in
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
          when is_punct "(" lp && not (Token.preceded_by_space lp) ->
            let params, variadic, body = parse_params [] rest' in
            Macro_table.Function_like { params; variadic; body }
        | _ -> Macro_table.Object_like rest
      in
      (match Macro_table.define (Token.lexeme name) def macros with
       | Ok macros' -> macros'
       (* Incompatible redefinition: keep the existing definition for now;
          diagnostics arrive with the frontend integration. *)
       | Error _ -> macros)
  | _ -> macros

let do_undef macros = function
  | n :: _ when is_ident n -> Macro_table.undef (Token.lexeme n) macros
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
  Token.make ~kind:Token.Pp_number
    ~lexeme:(if present then "1" else "0")
    ~preceded_by_space:(Token.preceded_by_space template)
    ~loc:(Token.loc template) ()

let rec replace_defined macros = function
  | d :: rest
    when is_ident d && String.equal (Token.lexeme d) "defined" ->
      (match rest with
       | lp :: n :: rp :: rest'
         when is_punct "(" lp && is_ident n && is_punct ")" rp ->
           mk_num (Macro_table.mem (Token.lexeme n) macros) d
           :: replace_defined macros rest'
       | n :: rest' when is_ident n ->
           mk_num (Macro_table.mem (Token.lexeme n) macros) d
           :: replace_defined macros rest'
       | _ -> d :: replace_defined macros rest)
  | t :: rest -> t :: replace_defined macros rest
  | [] -> []

(* Evaluate a #if / #elif controlling expression: resolve [defined], expand, then
   hand the result to Eval.  An ill-formed expression counts as false. *)
let eval_cond macros toks =
  let expanded = expand macros (replace_defined macros toks) in
  match Eval.eval expanded with Ok b -> b | Error _ -> false

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
      (match Token.lexeme d with
       | "define" -> ((if em then do_define macros rest else macros), conds)
       | "undef" -> ((if em then do_undef macros rest else macros), conds)
       | "ifdef" ->
           let cond =
             match rest with n :: _ -> Macro_table.mem (Token.lexeme n) macros | _ -> false in
           (macros, push_if conds ~outer:em ~cond)
       | "ifndef" ->
           let cond =
             match rest with n :: _ -> not (Macro_table.mem (Token.lexeme n) macros) | _ -> false in
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
  let toks = Lexer.tokens lexbuf in
  close_in ic;
  List.map (Token.map Location.of_lexing) toks

(* The header name and whether it was the angle-bracket form, from the tokens
   after `include`.  "..." takes the string-literal content; <...> concatenates
   the lexemes between the brackets.  (Computed/macro includes are not yet
   handled.) *)
let include_target ds =
  match ds with
  | s :: _ when (match Token.kind s with
                 | Token.String_literal -> true | _ -> false) ->
      let sp = Token.lexeme s in
      if String.length sp >= 2 then Some (String.sub sp 1 (String.length sp - 2), false)
      else None
  | t :: rest when is_punct "<" t ->
      let rec collect acc = function
        | u :: _ when is_punct ">" u -> Some (String.concat "" (List.rev acc))
        | u :: us -> collect (Token.lexeme u :: acc) us
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
                   && String.equal (Token.lexeme d) "include" ->
                let inc, macros, once = do_include ~include_dirs ~dir macros once drest in
                process_lines ~include_dirs ~dir ~canon macros once (inc :: acc) conds [] rest
            | d :: e :: _
              when em && is_ident d && is_ident e
                   && String.equal (Token.lexeme d) "pragma"
                   && String.equal (Token.lexeme e) "once" ->
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

(* Lex a -D macro value (or "1" for a bare -DNAME) into a replacement list. *)
let lex_value s =
  Lexer.tokens (Lexing.from_string s)
  |> List.filter (fun t -> not (is_newline t))
  |> List.map (Token.map Location.of_lexing)

let rec seed_defines macros = function
  | [] -> macros
  | (name, v) :: rest ->
      let body = lex_value (match v with Some s -> s | None -> "1") in
      let macros =
        match Macro_table.define name (Macro_table.Object_like body) macros with
        | Ok m -> m
        | Error _ -> macros
      in
      seed_defines macros rest

let rec seed_undefs macros = function
  | [] -> macros
  | name :: rest -> seed_undefs (Macro_table.undef name macros) rest

type entry =
  { actual_pos_bol : int
  ; expansions     : Location.frame list
  ; lexeme         : string
  }

(* The raw_loc_map is a hash table keyed by the synthetic [pos_bol].  Abstract in
   the .mli, so callers can only [lookup]. *)
type raw_loc_map = (int, entry) Hashtbl.t

let lookup map key = Hashtbl.find_opt map key

(* The "expanded from:" notes a diagnostic shows for a token, Clang-style.  The
   primary caret already sits at the outermost invocation (Location.primary), so
   each frame contributes one note "expanded from macro 'NAME'" whose caret
   points at the *next* level in: the next frame's invocation site, or — for the
   innermost frame — the token's own lexeme in the macro body.  Ordinary
   (unexpanded) tokens get no notes. *)
let expansion_notes loc =
  let lex_pos = Location.lexeme loc in
  let rec go = function
    | [] -> []
    | [ (f : Location.frame) ] ->
        [ Location.{ macro_name = f.macro_name; use = lex_pos } ]
    | f :: (g :: _ as rest) ->
        Location.{ macro_name = f.macro_name; use = g.Location.use } :: go rest
  in
  go (Location.expansion loc)

(* Assign synthetic [pos_bol] keys to non-Newline tokens and build the
   raw_loc_map.  Each key is a counter value (unique across the stream).  The
   real [pos_bol] goes into the entry; [pos_fname], [pos_lnum], and [pos_cnum]
   stay accurate in the token's position, so the raw token is useful for
   debugging even without the map. *)
let assign_keys toks =
  let map : raw_loc_map = Hashtbl.create 256 in
  let counter = ref 0 in
  let keyed = List.map (fun tok ->
    match Token.kind tok with
    | Token.Newline -> tok
    | _ ->
        let key = !counter in
        counter := key + 1;
        let s, e = Location.primary (Token.loc tok) in
        Hashtbl.replace map key
          { actual_pos_bol = s.Lexing.pos_bol
          ; expansions     = expansion_notes (Token.loc tok)
          ; lexeme         = Token.lexeme tok };
        (* Give the token a plain (unexpanded) location at its primary caret with
           the synthetic key in pos_bol — pos_fname/pos_lnum/pos_cnum stay
           accurate.  The expansion chain is already captured in the map entry, so
           the rewritten location carries no frames: its primary is exactly this
           caret, which is what the parser driver positions the lexer at. *)
        let s' = { s with Lexing.pos_bol = key } in
        Token.map (fun _ -> Location.of_lexing (s', e)) tok
  ) toks in
  (keyed, map)

let preprocess ~include_dirs ~predefined ~undefs ~forced_includes ~filename =
  let macros0 = seed_undefs (seed_defines Macro_table.empty predefined) undefs in
  (* Forced includes (e.g. builtins.h) are processed before the main file, as if
     textually included at the top: their output is prepended and their macros
     thread into the main file. *)
  let rec go macros once acc = function
    | [] -> assign_keys (List.concat (List.rev acc))
    | f :: fs ->
        let lines = split_lines (lex_file f) in
        let out_acc, macros, once =
          process_lines ~include_dirs ~dir:(Filename.dirname f) ~canon:f
            macros once [] [] [] lines
        in
        go macros once (List.concat (List.rev out_acc) :: acc) fs
  in
  go macros0 SS.empty [] (forced_includes @ [ filename ])

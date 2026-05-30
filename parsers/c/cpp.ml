(* The macro engine.  Names follow Prosser's pseudocode (see the design doc's
   Appendix A): [expand] rescans a token sequence, [subst] instantiates a
   replacement list, [hsadd] adds a hide set to every token.  Provenance is
   orthogonal to the algorithm — hide sets stop re-expansion, while expansion
   frames are pushed as [subst] copies body tokens. *)

module HS = Preproc_token.Hide_set

(* Small token predicates. *)
let is_ident t =
  match Preproc_token.kind t with Preproc_token.Identifier -> true | _ -> false

let is_newline t =
  match Preproc_token.kind t with Preproc_token.Newline -> true | _ -> false

let is_punct s t =
  match Preproc_token.kind t with
  | Preproc_token.Punctuator -> String.equal (Preproc_token.spelling t) s
  | _ -> false

(* Rebase a macro-body token onto the invocation site's provenance: keep its own
   spelling (a position in the macro body) but make its expansion chain the
   invoking token's chain extended with one frame for this macro.  This nests
   provenance the way Clang does — the new frame's [use] caret points at where
   the macro name is written in its own context. *)
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

(* subst for an object-like replacement list: there are no parameters, no # and
   no ##, so every body token falls into Prosser's "otherwise" case — copy it
   (recording provenance) and, in the base case, hsadd the accumulated hide set. *)
let rec subst ~name ~invoked_at body hs os =
  match body with
  | [] -> hsadd hs os
  | bt :: body' ->
      let bt = rebase ~name ~invoked_at bt in
      subst ~name ~invoked_at body' hs (os @ [ bt ])

(* expand(TS): rescan, replacing object-like macro names not already in their own
   hide set. *)
and expand macros = function
  | [] -> []
  | t :: ts when is_ident t ->
      let name = Preproc_token.spelling t in
      if HS.mem name (Preproc_token.hide_set t) then
        t :: expand macros ts
      else begin
        match Macro_table.find name macros with
        | Some (Macro_table.Object_like body) ->
            let hs = HS.add name (Preproc_token.hide_set t) in
            let out = subst ~name ~invoked_at:t body hs [] in
            expand macros (out @ ts)
        | Some (Macro_table.Function_like _) | None ->
            (* function-like expansion needs '(' lookahead — deferred to C7 *)
            t :: expand macros ts
      end
  | t :: ts -> t :: expand macros ts

(* --- Directive parsing ----------------------------------------------------- *)

(* Parse a function-like macro's parameter list, starting just after the '(',
   returning the names, whether it is variadic, and the replacement list. *)
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
        | lp :: rest' when is_punct "(" lp && not (Preproc_token.preceded_by_space lp) ->
            let params, variadic, body = parse_params [] rest' in
            Macro_table.Function_like { params; variadic; body }
        | _ ->
            Macro_table.Object_like rest
      in
      (match Macro_table.define (Preproc_token.spelling name) def macros with
       | Ok macros' -> macros'
       (* Incompatible redefinition: keep the existing definition for now;
          diagnostics come with the frontend integration. *)
       | Error _ -> macros)
  | _ -> macros

let directive macros = function
  | d :: rest when is_ident d ->
      (match Preproc_token.spelling d with
       | "define" -> do_define macros rest
       | "undef" ->
           (match rest with
            | n :: _ when is_ident n -> Macro_table.undef (Preproc_token.spelling n) macros
            | _ -> macros)
       (* #if / #ifdef / #include / #line / ... handled in later commits *)
       | _ -> macros)
  | _ -> macros  (* a null directive: '#' alone on a line *)

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

let rec run macros = function
  | [] -> []
  | (ltoks, nl) :: rest ->
      (match ltoks with
       | t :: ds when is_punct "#" t ->
           (* a directive line produces no output, not even its newline *)
           run (directive macros ds) rest
       | _ ->
           let expanded = expand macros ltoks in
           let nl_toks = match nl with Some n -> [ n ] | None -> [] in
           expanded @ nl_toks @ run macros rest)

let preprocess toks =
  let lifted = List.map (Preproc_token.map Preproc_location.of_lexing) toks in
  run Macro_table.empty (split_lines lifted)

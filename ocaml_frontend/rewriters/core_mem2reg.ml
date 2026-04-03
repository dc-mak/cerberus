(* This file implements an analysis to find 'promotable' variables,
   stack variables which can be promoted out of memory operations and
   into pure Core expressions. *)
open Core

(* ------------------------------------------------------------------ *)
(* Internal classification of how a pointer sym is used               *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Occurrence helpers                                                 *)
(* ------------------------------------------------------------------ *)

let is_pesym sym (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Symbol.symbolEquality s sym
  | _ -> false

let sym_empty_set = Pset.empty Symbol.compare_sym

let sym_empty_map = Pmap.empty Symbol.compare_sym

(* [pexpr_vars pe] is the set of all symbols mentioned in [pe]
   we don't care about bound variables here *)
let rec pexpr_vars (Pexpr (_, _, pe_)) =
  match pe_ with
  | PEsym s -> Pset.singleton Symbol.compare_sym s
  | PEval _ | PEimpl _ | PEundef _ | PEerror _ -> sym_empty_set
  | PEctor (_, pes) | PEcall (_, pes) | PEmemop (_, pes) ->
      pexpr_list_vars pes
  | PEcase (pe, arms) ->
      pexpr_list_vars (pe :: (List.map snd arms))
  | PEarray_shift (pe1, _, pe2) | PEop (_, pe1, pe2)
  | PElet (_, pe1, pe2) | PEwrapI (_, _, pe1, pe2)
  | PEcatch_exceptional_condition (_, _, pe1, pe2)
  | PEare_compatible (pe1, pe2) ->
      pexpr_list_vars [pe1; pe2]
  | PEmember_shift (pe, _, _)
  | PEconv_int (_, pe)
  | PEnot pe
  | PEis_scalar pe | PEis_integer pe | PEis_signed pe | PEis_unsigned pe
  | PEmemberof (_, _, pe) | PEunion (_, _, pe) | PEcfunction pe
  | PEbmc_assume pe ->
      pexpr_vars pe
  | PEif (pe1, pe2, pe3) ->
      pexpr_list_vars [pe1; pe2; pe3]
  | PEconstrained ivs ->
      pexpr_list_vars (List.map snd ivs)
  | PEstruct (_, fields) ->
      pexpr_list_vars (List.map snd fields)

and pexpr_list_vars pes =
  List.fold_left (fun set pe ->
      Pset.union set (pexpr_vars pe)) sym_empty_set pes

(* [action_escaping_vars creates act_] is the set of all vars which are
   mentioned in non-direct-address positions. For Store0/Load0/Kill/SeqRMW the
   bare-PEsym address argument is excluded; everything else is included.  *)
let action_escaping_vars act_ =
  (* addr_indirect addr_pe: if not a bare PEsym, all syms in addr_pe are bad *)
  let addr_indirect addr_pe =
    match addr_pe with
    | Pexpr (_, _, PEsym _) ->
      sym_empty_set
    | _ ->
      pexpr_vars addr_pe
  in
  match act_ with
  | Store0 (_, ctype_pe, addr_pe, val_pe, _) ->
      Pset.union (addr_indirect addr_pe) (pexpr_list_vars [ctype_pe; val_pe])
  | Load0 (_, addr_pe, _) | Kill (_, addr_pe) ->
      addr_indirect addr_pe
  | SeqRMW (_, ty_pe, addr_pe, _, upd_pe) ->
      Pset.union (addr_indirect addr_pe) (pexpr_list_vars [ty_pe; upd_pe])
  | Create (pe1, pe2, _) | Alloc0 (pe1, pe2, _)
  | LinuxLoad (pe1, pe2, _) ->
      pexpr_list_vars [pe1; pe2]
  | CreateReadOnly (pe1, pe2, pe3, _) | LinuxStore (pe1, pe2, pe3, _)
  | LinuxRMW (pe1, pe2, pe3, _) ->
      pexpr_list_vars [pe1; pe2; pe3]
  | Fence0 _ | LinuxFence _ -> sym_empty_set
  | RMW0 (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeStrong (pe1, pe2, pe3, pe4, _, _)
  | CompareExchangeWeak (pe1, pe2, pe3, pe4, _, _) ->
      pexpr_list_vars [pe1; pe2; pe3; pe4]

(* ------------------------------------------------------------------ *)
(* Esave memo tables                                                  *)
(*                                                                    *)
(* sequentialisable analyses Esave bodies once via the default args   *)
(* and once per Erun call site.  Results are memoised per             *)
(* (label_sym, param_sym) to avoid redundant traversals and to        *)
(* terminate on back-edge Eruns.                                      *)
(* ------------------------------------------------------------------ *)

type 'a esave_memo_entry = {
  params  : (Symbol.sym * pexpr) list;            (* (param_sym, default_pe) by position *)
  body    : (unit, unit, Symbol.sym) generic_expr;
  results : (Symbol.sym, 'a) Pmap.map ref;        (* param_sym -> cached result, filled lazily *)
}

(* 'a = bool * (Event_set.t * env) option  for sequentialisable   *)
type 'a memo_save_info = (Symbol.sym, 'a esave_memo_entry) Pmap.map

(* find_single_direct_alias sym pairs:
   Given an association list of (param_sym, pe) pairs, returns:
     None           — sym does not appear as a bare PEsym in any pe
     Some param_sym — sym appears as a bare PEsym in exactly one pe
   Raises failwith if sym appears in more than one pe (invariant violation). *)
let find_single_direct_alias sym pairs =
  match List.filter_map (fun (param_sym, pe) ->
    if is_pesym sym pe then Some param_sym else None) pairs
  with
  | []          -> None
  | [param_sym] -> Some param_sym
  | _ :: _ :: _ -> failwith "Core_mem2reg: multiple direct aliases for the same sym"

(*
let process_erun_args creates params args =
  List.iter2 (fun _ arg ->
    match arg with
    | Pexpr (_, _, PEsym s) when Pset.mem s !creates -> ()
    | _ -> pexpr_vars creates arg)
    params args
*)

(* collect_info: single pass over the function body that simultaneously
   (a) collects all Esave definitions into a memo table,
   (b) collects Create-bound syms that are candidates for promotion, and
   (c) removes from the candidate set any sym that appears in a non-direct-
       address position (i.e., not as the bare PEsym address argument of a
       Store0/Load0/Kill/SeqRMW).  Whatever remains in `creates` after the
       walk has been seen only in those safe positions.                    *)
let rec collect_info ~also_fun_args (esave_memo, creates, pending_eruns) (Expr (_, e_)) =
    match e_ with
    | Esave ((label_sym, _), params, esave_body) ->
        let entry = {
          params  = List.map (fun (s, (_, pe)) -> (s, pe)) params;
          body    = esave_body;
          results = ref (Pmap.empty Symbol.compare_sym);
        } in
        let esave_memo = Pmap.add label_sym entry esave_memo in
        collect_info ~also_fun_args (esave_memo, creates, pending_eruns) esave_body
    | Esseq (
        Pattern (_, CaseBase (Some ptr_sym, _)),
        Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _,
            (Symbol.PrefSource _ | Symbol.PrefCompoundLiteral _)))))),
        body
      ) ->
        let creates = Pset.add ptr_sym creates in
        collect_info ~also_fun_args (esave_memo, creates, pending_eruns) body
    | Esseq (
        Pattern (_, CaseBase (Some ptr_sym, _)),
        Expr (_, Eaction (Paction (_, Action (_, _, Create (_, _, Symbol.PrefFunArg _))))),
        body
      ) when also_fun_args ->
        let creates = Pset.add ptr_sym creates in
        collect_info ~also_fun_args (esave_memo, creates, pending_eruns) body
    | Eaction (Paction (_, Action (_, _, act_))) ->
        (esave_memo, Pset.diff creates (action_escaping_vars act_), pending_eruns)
    | Epure pe ->
        (esave_memo, Pset.diff creates (pexpr_vars pe), pending_eruns)
    | Ememop (_, pes) ->
        (esave_memo, Pset.diff creates (pexpr_list_vars pes), pending_eruns)
    | Elet (_, pe, e) ->
        let creates = Pset.diff creates (pexpr_vars pe) in
        collect_info ~also_fun_args (esave_memo, creates, pending_eruns) e
    | Ecase (pe, arms) ->
        let creates = Pset.diff creates (pexpr_vars pe) in
        let _ = List.map (fun (_, e) -> collect_info ~also_fun_args (esave_memo, creates, pending_eruns)) arms in
        _
    | Eif (pe, e1, e2) ->
        _
        (* pexpr_vars creates pe; walk e1; walk e2 *)
    | Eccall (_, fn_pe, arg_pe, pes) ->
        _
        (* List.iter (pexpr_vars creates) (fn_pe :: arg_pe :: pes) *)
    | Eproc (_, _, pes) ->
        _
        (* List.iter (pexpr_vars creates) pes *)
    | Erun (_, label_sym, args) ->
        _
        (* (match Pmap.lookup label_sym !esave_memo with *)
        (* | Some entry -> process_erun_args creates entry.params args *)
        (* | None -> pending_eruns := (label_sym, args) :: !pending_eruns) *)
    | Ewseq (_, e1, e2) | Esseq (_, e1, e2) ->
      _
      (* walk e1; walk e2 *)
    | Ebound e | Eannot (_, e) ->
      collect_info ~also_fun_args (esave_memo, creates, pending_eruns) e
    | Eunseq es | End es | Epar es           ->
      _
      (* List.iter walk es *)
    | Ewait _ | Eexcluded _                  ->
      (esave_memo, creates, pending_eruns)
      (* () *)

let collect_info ~also_fun_args body =
  let esave_memo    = Pmap.empty Symbol.compare_sym in
  let creates       = Pset.empty Symbol.compare_sym in
  let pending_eruns = [] in
  let (esave_memo, creates, pending_eruns) =
    collect_info ~also_fun_args (esave_memo, creates, pending_eruns) body
  in
  (esave_memo, creates)
(*
  (* Process any Eruns whose labels were not yet defined at the time of the
     walk (forward references).  All Esaves are now in esave_memo.         *)
  List.iter (fun (label_sym, args) ->
    match Pmap.lookup label_sym !esave_memo with
    | None -> ()
    | Some entry -> process_erun_args creates entry.params args)
  !pending_eruns;
  (esave_memo, creates)
*)

(* ------------------------------------------------------------------ *)
(* sequentialisable: unified promotability analysis                    *)
(*                                                                     *)
(* Returns:                                                            *)
(*   None           — all control-flow paths end in Erun (vacuous)    *)
(*   Some (ev, env') — events observed on sym and env after expr      *)
(* Raises Not_sequentialisable on any conflict.                        *)
(* Raises Load_from_uninit when a Load0/SeqRMW sees env=Uninit;       *)
(*   caught by save_param_needs_init to detect loops that need init.        *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Event: memory events observable on a single sym                *)
(* ------------------------------------------------------------------ *)

module Event = struct
  type t = Pos_store | Neg_store | Load | Kill
  let is_neg_store = function Neg_store -> true | _ -> false
  let is_load = function Load -> true | _ -> false
  let compare x y =
    let num = function
    | Pos_store -> 0
    | Neg_store -> 1
    | Load -> 2
    | Kill -> 3 in
    Int.compare (num x) (num y)
end

module Event_set = Set.Make(Event)

(* env: initialization state of sym at a given program point          *)
(* Uninit      — no store observed yet on this path                   *)
(* Init        — sym was last stored with committed value pe          *)
(* Killed      — sym's allocation was freed                           *)
type env = Uninit | Init | Killed
let is_uninit = function Uninit -> true | _ -> false
let is_killed = function Killed -> true | _ -> false
let is_init   = function Init   -> true | _ -> false

exception Not_sequentialisable
exception Load_from_uninit

(* merges sequentialisable results from Eif/Ecase arms if they all agree
 * Note: this is fine for transforming too because we can use PEundef
 * as values for non-returning branches *)
let combine_branches arm_results =
  let branches = List.filter_map Fun.id arm_results in
  let all_evs, all_env = List.split branches in
  let all_evs = List.fold_left Event_set.union Event_set.empty all_evs in
  let combined_env =
    if List.for_all is_uninit all_env then
      Uninit
    else if List.for_all is_killed all_env then
      Killed
    else if List.for_all is_init all_env then
       Init
    else
       raise Not_sequentialisable in
  (all_evs, combined_env)

let is_init_env needs_init ~param_env ~env =
  if needs_init then
    (match env with
    | Killed -> raise Not_sequentialisable
    | Uninit -> raise Load_from_uninit
    | Init -> param_env)
  else
    (match param_env with
     | Uninit -> env            (* body didn't alter sym; outer state persists *)
     | Init | Killed -> param_env)

(* seq_memo: memoises sequentialisable results per (label_sym, param_sym).
   'a = bool * (Event_set.t * env) option
     fst = init_needed: body requires Init env on entry (true) or
           self-initialises (false)
     snd = None while in progress or all paths end in Erun;
           Some (ev, env') otherwise *)
type seq_memo = (bool * (Event_set.t * env) option) memo_save_info

let rec sequentialisable (seq_memo : seq_memo) sym env (Expr (_, e_))
    : (Event_set.t * env) option =
  let module Es = Event_set in
  let ( let* ) = Option.bind in
  let must_return = function
    | None -> raise Not_sequentialisable
    | Some (ev, env) -> (ev, env) in
  match e_ with
  | Eaction (Paction (polarity, Action (_, _, act_))) ->
      begin match act_ with
      | Store0 (_, _, addr_pe, val_pe, _) when is_pesym sym addr_pe ->
          let ev = match polarity with
            | Pos -> Event.Pos_store
            | Neg -> Event.Neg_store in
        Some (Es.singleton ev, Init)
      | Load0 (_, addr_pe, _) when is_pesym sym addr_pe ->
          (match env with
           | Init   -> Some (Es.singleton Event.Load, env)
           | Uninit  -> raise Load_from_uninit
           | Killed  -> raise Not_sequentialisable)
      | Kill (_, addr_pe) when is_pesym sym addr_pe ->
          Some (Es.singleton Event.Kill, Killed)
      | SeqRMW (_, _, addr_pe, tmp_sym, upd_pe) when is_pesym sym addr_pe ->
          (match env with
           | Init -> Some (Es.of_list [Event.Load; Event.Pos_store], Init)
           | Uninit -> raise Load_from_uninit
           | Killed -> raise Not_sequentialisable)
      | _ ->
        (* sym was verified to appear only as a direct address argument
         * (collect_info left it in creates), so non-address actions are
         * irrelevant and can be skipped. *)
        Some (Es.empty, env)
      end
  | Esseq (_, e1, e2) ->
      let* (ev1, env1) = sequentialisable seq_memo sym env e1 in
      let* (ev2, env2) = sequentialisable seq_memo sym env1 e2 in
      Some (Es.union ev1 ev2, env2)
  | Ewseq (_, e1, e2) ->
      (* race-condition analysis is invalid if e1/e2 don't return
       * or, assume definite race if either expression doesn't return *)
    let (ev1, env1) = must_return @@ sequentialisable seq_memo sym env e1 in
    let (ev2, env2) = must_return @@ sequentialisable seq_memo sym env1 e2 in
    if Es.exists Event.is_neg_store ev1
        && not (Es.is_empty ev2) then
      raise Not_sequentialisable
    else
      Some (Es.union ev1 ev2, env2)
  | Eif (pe, et, ef) ->
      let rt = sequentialisable seq_memo sym env et in
      let rf = sequentialisable seq_memo sym env ef in
      Some (combine_branches [rt; rf])
  | Ecase (pe, arms) ->
      let arm_results =
        List.map (fun (_, e) -> sequentialisable seq_memo sym env e) arms
      in
      Some (combine_branches arm_results)
  | End arms | Epar arms | Eunseq arms ->
      let eventful_arms = List.filter_map
        (fun arm ->
          (* race-condition analysis is invalid if e1/e2 don't return or,
           * assume definite race if either expression doesn't return *)
          let (ev, env') = must_return @@ sequentialisable seq_memo sym env arm in
          if Es.is_empty ev then None else Some (ev, env'))
        arms in
      let all_reads =
        List.for_all (fun (ev, _) ->
            Es.for_all Event.is_load ev) eventful_arms in
      if all_reads then
        (* All arms only load; env is unchanged. *)
        Some (Es.singleton Event.Load, env)
      else
        (* At most one write/kill arm, with no other arm having events. *)
        begin match eventful_arms with
          | [(ev, env')] -> Some (ev, env')
          | []           -> assert false (* handled by all_reads = true *)
          | _ :: _ :: _  -> raise Not_sequentialisable
        end
  | Esave ((label_sym, _), params, _body) ->
      (match find_single_direct_alias sym
               (List.map (fun (p, (_, pe)) -> (p, pe)) params) with
       | None           -> Some (Es.empty, env)
       | Some param_sym ->
         let (needs_init, result) =
             save_param_needs_init seq_memo sym label_sym param_sym in
         let* (ev, param_env) = result in
         Some (ev, is_init_env needs_init ~env ~param_env))
  | Erun (_, label_sym, args) ->
      let entry = Pmap.find label_sym seq_memo in
      (match find_single_direct_alias sym
               (List.combine (List.map fst entry.params) args) with
       | None           -> ()
       | Some param_sym ->
         let (needs_init, result) =
           save_param_needs_init seq_memo sym label_sym param_sym in
         Option.iter (fun (ev, param_env) ->
             ignore (is_init_env needs_init ~env ~param_env))
           result);
         None
  | Elet (_, _, e) | Eannot (_, e) ->
      sequentialisable seq_memo sym env e
  | Ebound e ->
    let* (_, env) = sequentialisable seq_memo sym env e in
    Some (Es.empty, env)
  | Epure _ | Ememop _ | Eccall _ | Eproc _ | Ewait _ | Eexcluded _ ->
      Some (Es.empty, env)

(* save_param_needs_init seq_memo sym env label_sym param_sym:
   Analyses the Esave body for (label_sym, param_sym) w.r.t. sym and
   memoises the result.  Returns the body's sequentialisable result
   (None if all paths end in Erun).

   - Sentinel (false, None) is written before recursing so that back-edge
     Erun calls find the entry and do not loop.
   - If Load_from_uninit is raised (body reads sym before any store):
       * If outer env = Init: mark init_needed=true, re-run with outer env.
       * Otherwise: re-raise Load_from_uninit.
   - If already memoised with init_needed=true and env ≠ Init: re-raise
     Load_from_uninit. *)
and save_param_needs_init seq_memo sym label_sym param_sym
    : bool * (Event_set.t * env) option =
  let entry = Pmap.find label_sym seq_memo in
  match Pmap.lookup param_sym !(entry.results) with
  | Some result -> result
  | None ->
      entry.results := Pmap.add param_sym (false, None) !(entry.results);
      (try
        let result = sequentialisable seq_memo param_sym Uninit entry.body in
        entry.results := Pmap.add param_sym (false, result) !(entry.results);
        (false, result)
      with Load_from_uninit ->
        let result = sequentialisable seq_memo param_sym Init entry.body in
        entry.results := Pmap.add param_sym (true, result) !(entry.results);
        (true, result))

(* ------------------------------------------------------------------ *)
(* Promotability analysis for a single procedure                       *)
(* ------------------------------------------------------------------ *)

let find_promotable ~also_fun_args f_sym body : Symbol.sym list =
  let esave_memo, creates = collect_info ~also_fun_args body in
  let seq_memo  : seq_memo =
    Pmap.map (fun { params; body; _ } ->
      { params; body; results = ref (Pmap.empty Symbol.compare_sym) }) esave_memo in
  let is_promotable s =
    match sequentialisable seq_memo s Uninit body with
    | None | Some _ -> true
    | exception Not_sequentialisable -> false
    | exception Load_from_uninit    -> false
  in
  let promotable = List.filter is_promotable (Pset.elements creates) in
  Cerb_debug.print_debug 3 [] (fun () ->
    Printf.sprintf "[mem2reg] %s: %d promotable: [%s]"
      (Pp_symbol.to_string_pretty f_sym)
      (List.length promotable)
      (String.concat ", " (List.map Pp_symbol.to_string promotable)));
  promotable

(* ------------------------------------------------------------------ *)
(* transform_file: analysis phase only — file returned unchanged       *)
(* ------------------------------------------------------------------ *)

let transform_file file =
  let also_fun_args = match file.calling_convention with
    | Inner_arg_callconv -> true
    | Normal_callconv    -> false
  in
  let funs = Pmap.mapi (fun f_sym decl ->
    match decl with
    | Proc (loc, env_marker, ret_bt, args, body, _) ->
        let promotable = find_promotable ~also_fun_args f_sym body in
        Proc (loc, env_marker, ret_bt, args, body, promotable)
    | Fun _ | ProcDecl _ | BuiltinDecl _ ->
        decl) file.funs in
  { file with funs }

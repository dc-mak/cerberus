open Core

(* ===== Helpers ===== *)

(* Pretty-print a PPrint document to a string with colours disabled.
   Takes a thunk so the document is built *after* do_colour is cleared,
   preventing fancystring ANSI codes from being embedded during construction. *)
let pp_to_string mk_doc =
  Cerb_colour.without_colour (fun () ->
    let buf = Buffer.create 256 in
    PPrint.ToBuffer.pretty 0.8 80 buf (mk_doc ());
    Buffer.contents buf
  ) ()

let pp_expr_str expr  = pp_to_string (fun () -> Pp_core.Basic.pp_expr expr)
let pp_pexpr_str pe   = pp_to_string (fun () -> Pp_core.Basic.pp_pexpr pe)
let pp_bty_str bty    = pp_to_string (fun () -> Pp_core.Basic.pp_core_base_type bty)

(* Format the Esave header: "save (k : bty) (x1 = e1; x2 = e2)" *)
let format_esave_header sym bty bindings =
  let label = Pp_symbol.to_string_pretty sym in
  let bty_str = pp_bty_str bty in
  let bindings_str =
    String.concat "; "
      (List.map (fun (var_sym, ((_var_bty, _ctype_opt), init_pe)) ->
        Pp_symbol.to_string_pretty var_sym ^ " = " ^ pp_pexpr_str init_pe
      ) bindings)
  in
  Printf.sprintf "save (%s : %s) (%s)" label bty_str bindings_str

(* ===== CFG types ===== *)

type node_id = Symbol.sym

type edge_label = Seq | IfTrue | IfFalse | Run

type stmt = { text : string; loc : string }

type node = {
  id    : node_id;
  label : string option;
  stmts : stmt list;
}

type edge = {
  from_id : node_id;
  to_id   : node_id;
  label   : edge_label;
}

type cfg = {
  fun_name : string;
  entry    : node_id;
  nodes    : node list;
  edges    : edge list;
}

(* ===== Mutable build context ===== *)

type ctx = {
  nodes : node list ref;
  edges : edge list ref;
}

let make_ctx () = { nodes = ref []; edges = ref [] }

let emit_node ctx n = ctx.nodes := n :: !(ctx.nodes)

let emit_edge ctx e = ctx.edges := e :: !(ctx.edges)

(* ===== Accumulator ===== *)

(* The open basic block currently being built.
   [incoming] holds node IDs whose Seq edges into this block are pending
   — they are emitted together when [flush_acc] is called.
   This allows us to forward pending edges through empty accs (at Esave
   sites) without creating empty intermediate nodes. *)
type acc = {
  id       : node_id;
  stmts    : stmt list;
  incoming : node_id list;
}

let fresh_acc () =
  { id = Symbol.fresh_pretty "cfg_node"; stmts = []; incoming = [] }

let add_stmt a s = { a with stmts = a.stmts @ [s] }

(* Emit the block as a node and flush all pending incoming Seq edges.
   PRECONDITION: acc.stmts <> [].  Callers must ensure this. *)
let flush_acc ?(label=None) ctx acc =
  assert (acc.stmts <> []);
  emit_node ctx { id = acc.id; label; stmts = acc.stmts };
  List.iter (fun src ->
    emit_edge ctx { from_id = src; to_id = acc.id; label = Seq }
  ) acc.incoming;
  acc.id

(* ===== Build result ===== *)

type result = {
  entry : node_id;
  exits : acc list;   (* open blocks at fall-through exit points *)
}

(* ===== Main traversal ===== *)

let rec build_expr ctx acc (Expr (annots, expr_) as expr) =
  let loc = Cerb_location.location_to_string (Annot.get_loc_ annots) in
  match expr_ with

  | Eannot (_, inner) ->
      build_expr ctx acc inner

  | Ebound inner ->
      build_expr ctx acc inner

  | Esave ((sym, bty), bindings, body) ->
      (* Only Esave may receive an empty-stmts acc (at the top of a function
         body or after a join point).  We check stmts and either flush acc as
         a predecessor block or forward its pending incoming edges. *)
      let save_incoming =
        if acc.stmts = [] then
          acc.incoming
        else
          [flush_acc ctx acc]
      in
      let header = format_esave_header sym bty bindings in
      let save_acc = { id = sym; stmts = [{ text = header; loc }]; incoming = save_incoming } in
      let r = build_expr ctx save_acc body in
      { entry = sym; exits = r.exits }

  | Esseq (_, e1, e2) | Ewseq (_, e1, e2) ->
      let r1 = build_expr ctx acc e1 in
      begin match r1.exits with
      | [] ->
          (* e1 doesn't fall through (e.g. ends in Erun).
             Still traverse e2 to emit any Esave nodes it contains,
             which may be targets of forward Erun edges. *)
          ignore (build_expr ctx (fresh_acc ()) e2);
          { entry = r1.entry; exits = [] }
      | [single] ->
          (* Straight-line code: carry the open acc into e2.
             The stmts from e1 and e2 will accumulate in the same block —
             this is the on-the-fly chain merge. *)
          let r2 = build_expr ctx single e2 in
          { entry = r1.entry; exits = r2.exits }
      | multiple ->
          (* Join point: flush all exit accs (invariant: always non-empty),
             create a fresh join acc and connect the flushed blocks to it. *)
          let ids = List.map (flush_acc ctx) multiple in
          let join_acc = { id = Symbol.fresh_pretty "cfg_join"; stmts = []; incoming = ids } in
          let r2 = build_expr ctx join_acc e2 in
          { entry = r1.entry; exits = r2.exits }
      end

  | Eif (cond, et, ef) ->
      let if_acc = add_stmt acc { text = "if " ^ pp_pexpr_str cond; loc } in
      let if_id  = flush_acc ctx if_acc in
      let r_t = build_expr ctx (fresh_acc ()) et in
      let r_f = build_expr ctx (fresh_acc ()) ef in
      emit_edge ctx { from_id = if_id; to_id = r_t.entry; label = IfTrue  };
      emit_edge ctx { from_id = if_id; to_id = r_f.entry; label = IfFalse };
      { entry = if_id; exits = r_t.exits @ r_f.exits }

  | Erun (_, sym, _args) ->
      let run_acc = add_stmt acc { text = pp_expr_str expr; loc } in
      let run_id  = flush_acc ctx run_acc in
      emit_edge ctx { from_id = run_id; to_id = sym; label = Run };
      { entry = run_id; exits = [] }

  | _ ->
      (* Atomic: Epure, Eaction, Ememop, Ecase, Elet, Eccall, Eproc,
                 Eunseq, End, Epar, Ewait, Eexcluded *)
      let s = { text = pp_expr_str expr; loc } in
      { entry = acc.id; exits = [add_stmt acc s] }

(* ===== Per-function analysis ===== *)

let analyse_cfg_for_fun fun_name body =
  let ctx = make_ctx () in
  let init_acc = fresh_acc () in
  let r = build_expr ctx init_acc body in
  (* Flush any open exits (fall-through at end of function body). *)
  List.iter (fun a -> ignore (flush_acc ctx a)) r.exits;
  { fun_name;
    entry = r.entry;
    nodes = List.rev !(ctx.nodes);
    edges = !(ctx.edges) }

(* ===== File-level entry point ===== *)

let analyse_file (file : unit Core.file) : cfg list =
  Pmap.fold (fun sym decl acc ->
    match decl with
    | Proc (_, _, _, _, body) ->
        let fun_name = Pp_symbol.to_string_pretty sym in
        analyse_cfg_for_fun fun_name body :: acc
    | _ ->
        acc
  ) file.funs []

(* ===== JSON output ===== *)

let json_escape s =
  let buf = Buffer.create (String.length s + 4) in
  String.iter (fun c ->
    match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c ->
        Buffer.add_char buf c
  ) s;
  Buffer.contents buf

let json_str s = "\"" ^ json_escape s ^ "\""

let json_str_opt = function
  | None   -> "null"
  | Some s -> json_str s

let edge_label_str = function
  | Seq     -> "seq"
  | IfTrue  -> "if-true"
  | IfFalse -> "if-false"
  | Run     -> "run"

let pp_json fmt cfgs =
  let buf = Buffer.create 4096 in
  let s str = Buffer.add_string buf str in
  let nl_indent indent = s "\n"; s (String.make indent ' ') in
  s "[";
  List.iteri (fun fi cfg ->
    if fi > 0 then s ",";
    nl_indent 2; s "{";
    nl_indent 4; s ("\"name\": " ^ json_str cfg.fun_name ^ ",");
    nl_indent 4; s ("\"entry\": " ^ json_str (Pp_symbol.to_string cfg.entry) ^ ",");
    nl_indent 4; s "\"nodes\": [";
    List.iteri (fun ni (nd : node) ->
      if ni > 0 then s ",";
      nl_indent 6; s "{";
      nl_indent 8; s ("\"id\": " ^ json_str (Pp_symbol.to_string nd.id) ^ ",");
      nl_indent 8; s ("\"label\": " ^ json_str_opt nd.label ^ ",");
      nl_indent 8; s "\"stmts\": [";
      List.iteri (fun si st ->
        if si > 0 then s ",";
        nl_indent 10; s "{";
        nl_indent 12; s ("\"text\": " ^ json_str st.text ^ ",");
        nl_indent 12; s ("\"loc\": " ^ json_str st.loc);
        nl_indent 10; s "}"
      ) nd.stmts;
      nl_indent 8; s "]";
      nl_indent 6; s "}"
    ) cfg.nodes;
    nl_indent 4; s "],";
    nl_indent 4; s "\"edges\": [";
    List.iteri (fun ei (ed : edge) ->
      if ei > 0 then s ",";
      nl_indent 6; s "{";
      nl_indent 8; s ("\"from\": " ^ json_str (Pp_symbol.to_string ed.from_id) ^ ",");
      nl_indent 8; s ("\"to\": " ^ json_str (Pp_symbol.to_string ed.to_id) ^ ",");
      nl_indent 8; s ("\"label\": " ^ json_str (edge_label_str ed.label));
      nl_indent 6; s "}"
    ) cfg.edges;
    nl_indent 4; s "]";
    nl_indent 2; s "}"
  ) cfgs;
  s "\n]";
  Format.pp_print_string fmt (Buffer.contents buf)

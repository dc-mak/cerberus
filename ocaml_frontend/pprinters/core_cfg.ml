open Core
open Cerb_pp_prelude

(* ===== Helpers ===== *)

(* Build a PPrint document with colours disabled.  All stmt text fields are
   constructed via mk_doc so no ANSI fancystring nodes are embedded. *)
let mk_doc f = Cerb_colour.without_colour f ()

(* Render a PPrint document to a plain string at JSON output time. *)
let doc_to_string doc =
  let buf = Buffer.create 256 in
  PPrint.ToBuffer.pretty 0.8 80 buf doc;
  Buffer.contents buf

(* Esave header: "save (sym : bty) (x1 = pe1; x2 = pe2)" *)
let format_esave_header sym bty bindings =
  mk_doc (fun () ->
    let label   = PPrint.string (Pp_symbol.to_string_pretty sym) in
    let bty_doc = Pp_core.Basic.pp_core_base_type bty in
    let bindings_doc =
      PPrint.separate (PPrint.string "; ")
        (List.map (fun (var_sym, ((_, _), init_pe)) ->
          PPrint.string (Pp_symbol.to_string_pretty var_sym) ^^
          PPrint.string " = " ^^
          Pp_core.Basic.pp_pexpr init_pe
        ) bindings)
    in
    PPrint.string "save (" ^^ label ^^
    PPrint.string " : "    ^^ bty_doc ^^
    PPrint.string ") ("    ^^ bindings_doc ^^ PPrint.string ")"
  )

(* ===== CFG types ===== *)

type node_id = Symbol.sym

type edge_label = Seq | IfTrue | IfFalse | Run

type stmt = { text : PPrint.document; loc : string }

type node = {
  id    : node_id;
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
let flush_acc ctx acc =
  assert (acc.stmts <> []);
  emit_node ctx { id = acc.id; stmts = acc.stmts };
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

  | Esseq (pat, e1, e2) | Ewseq (pat, e1, e2) ->
      let ctor = match expr_ with Ewseq _ -> "let weak" | _ -> "let strong" in
      let r1 = build_expr ctx acc e1 in
      (* Combine the pattern binding with e1's last stmt in each exit acc,
         following pp_let from pp_core.ml but omitting "in <body>":
           let strong/weak pat = e1_doc   (space or line-break before e1_doc) *)
      let bind_pat a =
        match List.rev a.stmts with
        | [] ->
            add_stmt a { text = mk_doc (fun () ->
              PPrint.string ctor ^^^ Pp_core.Basic.pp_pattern pat
            ); loc }
        | last :: rest ->
            let combined = mk_doc (fun () ->
              PPrint.group (
                (PPrint.string ctor ^^^ Pp_core.Basic.pp_pattern pat ^^^
                 PPrint.equals) ^//^ last.text
              )
            ) in
            { a with stmts = List.rev ({ last with text = combined } :: rest) }
      in
      let r1 = { r1 with exits = List.map bind_pat r1.exits } in
      begin match r1.exits with
      | [] ->
          (* e1 doesn't fall through (e.g. ends in Erun).
             Still traverse e2 to emit any Esave nodes it contains,
             which may be targets of forward Erun edges.
             Flush any open exits from that traversal so Esave nodes whose
             body falls through are not silently dropped. *)
          let r2 = build_expr ctx (fresh_acc ()) e2 in
          List.iter (fun a -> if a.stmts <> [] then ignore (flush_acc ctx a)) r2.exits;
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
      let if_acc = add_stmt acc { text = mk_doc (fun () ->
        PPrint.string "if " ^^ Pp_core.Basic.pp_pexpr cond
      ); loc } in
      let if_id  = flush_acc ctx if_acc in
      let r_t = build_expr ctx (fresh_acc ()) et in
      let r_f = build_expr ctx (fresh_acc ()) ef in
      emit_edge ctx { from_id = if_id; to_id = r_t.entry; label = IfTrue  };
      emit_edge ctx { from_id = if_id; to_id = r_f.entry; label = IfFalse };
      { entry = if_id; exits = r_t.exits @ r_f.exits }

  | Erun (_, sym, _args) ->
      let run_acc = add_stmt acc { text = mk_doc (fun () -> Pp_core.Basic.pp_expr expr); loc } in
      let run_id  = flush_acc ctx run_acc in
      emit_edge ctx { from_id = run_id; to_id = sym; label = Run };
      { entry = run_id; exits = [] }

  | _ ->
      (* Atomic: Epure, Eaction, Ememop, Ecase, Elet, Eccall, Eproc,
                 Eunseq, End, Epar, Ewait, Eexcluded *)
      let s = { text = mk_doc (fun () -> Pp_core.Basic.pp_expr expr); loc } in
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
      nl_indent 8; s "\"stmts\": [";
      List.iteri (fun si st ->
        if si > 0 then s ",";
        nl_indent 10; s "{";
        nl_indent 12; s ("\"text\": " ^ json_str (doc_to_string st.text) ^ ",");
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

(** Control-flow graph (CFG) analysis for Core programs.

    For each user-defined function in a Core file, builds a CFG where nodes are
    basic blocks and edges represent control-flow transitions.  The only
    control-flow constructs recognised are [Ewseq], [Esseq], [Eif], [Erun], and
    [Esave]; everything else (including [Ecase] and pure expressions) is treated
    as a single atomic statement.

    [Esave] expressions define labeled loop-header blocks.  Basic blocks are
    formed by accumulating sequential atomic statements on the fly; no separate
    merge pass is needed. *)

(** Stable, unique node identifier.  Esave nodes use their Esave symbol; all
    other nodes use a fresh symbol. *)
type node_id = Symbol.sym

type edge_label =
  | Seq      (** Sequential composition: Esseq or Ewseq *)
  | IfTrue   (** True branch of an Eif *)
  | IfFalse  (** False branch of an Eif *)
  | Run      (** Non-returning jump: Erun *)

(** A single statement within a basic block, retaining its original source
    location and verbatim pretty-printed text. *)
type stmt = {
  text : PPrint.document;
  loc  : string;
}

(** A basic block node.  After on-the-fly merging, [stmts] contains one or
    more statements. *)
type node = {
  id    : node_id;
  stmts : stmt list;
}

type edge = {
  from_id : node_id;
  to_id   : node_id;
  label   : edge_label;
  (** [dom] is [true] when this edge is a dominator-tree edge, i.e. when
      [from_id] is the immediate dominator of [to_id]. *)
  dom     : bool;
}

type cfg = {
  fun_name : string;
  entry    : node_id;
  nodes    : node list;
  edges    : edge list;
}

(** Analyse all [Proc] definitions in [file.funs] and return one [cfg] per
    function.  The stdlib and global initialisers are not analysed. *)
val analyse_file : unit Core.file -> cfg list

(** Pretty-print [cfgs] as a JSON array to [fmt].
    Node IDs in JSON are [Pp_symbol.to_string] strings (unique and stable). *)
val pp_json : Format.formatter -> cfg list -> unit

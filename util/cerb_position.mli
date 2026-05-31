type t

(** One step of a macro-expansion chain attached to a position by the internal
    preprocessor: the macro whose invocation produced the token ([macro_name =
    None] for tokens synthesised without a name), and the source region its
    "expanded from:" caret points at.  Empty for ordinary (external-cpp) tokens,
    so this field is invisible on the default path. *)
type macro_frame =
  { macro_name : string option
  ; caret      : Lexing.position * Lexing.position }

(** A placeholder position *)
val dummy: t

(** A position in the pre-processed file. The source file and line are
the same as the pre-processed file *)
val from_lexing: Lexing.position -> t

(** Change the column number by the given amount. *)
val change_cnum: t -> int -> t

(** Set the file and line in the original source file. *)
val set_source: (string * int) -> t -> t

(** Source file for position *)
val file: t -> string

(** Source line for the position. 1 based *)
val line: t -> int

(** Column of position, 1 based. *)
val column: t -> int


(** Location in the pre-processed file *)
val to_file_lexing: t -> Lexing.position


(** The macro-expansion chain (outermost first); [] for ordinary positions.
    Filled by the internal-preprocessor token feed; read by the diagnostic
    renderer to emit Clang-style "expanded from:" notes. *)
val provenance: t -> macro_frame list

(** Attach a macro-expansion chain to a position (functional update). *)
val with_provenance: macro_frame list -> t -> t

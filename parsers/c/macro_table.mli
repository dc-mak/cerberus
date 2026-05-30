(* The macro environment threaded through the engine: an immutable map from macro
   name to its definition (C11 §6.10.3).  Bodies are stored already lifted to the
   engine's location type, with empty hide sets and spellings pointing into the
   #define that introduced them. *)

type token = Preproc_location.t Preproc_token.t

type definition =
  | Object_like of token list
  | Function_like of
      { params   : string list  (* formal parameter names, in order *)
      ; variadic : bool         (* trailing "..."; __VA_ARGS__ usable in body *)
      ; body     : token list }

type t

val empty : t

(* §6.10.3#1-2: a name may be redefined only by an *identical* replacement list
   (same tokens, same spellings, same interior white-space) and, for
   function-like macros, the same parameter spellings and variadic flag.  A
   benign (identical) redefinition returns [Ok]; an incompatible one returns
   [Error old] with the previous, conflicting definition so the caller can
   diagnose it. *)
val define : string -> definition -> t -> (t, definition) result

val undef : string -> t -> t
val find : string -> t -> definition option
val mem : string -> t -> bool

val print : Format.formatter -> t -> unit

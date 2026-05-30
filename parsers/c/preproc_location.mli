(* Per-token source provenance for the internal preprocessor, expressed in the
   raw [Lexing.position]s its lexer's lexbuf produces.

   An ordinary (non-expanded) token carries just a [spelling] region — where its
   text lives in the original file — and an empty expansion chain.  A token
   produced by macro expansion keeps the spelling of the macro *body* it was
   copied from, plus an ordered [expansion] chain recording the invocation sites
   it passed through (outermost first), so diagnostics can render Clang-style
   "note: expanded from:" carets. *)

type position = Lexing.position * Lexing.position

(* One step of a macro-expansion chain: the macro whose invocation produced the
   token ([macro_name = None] for tokens synthesised without a name, e.g. by
   [##] pasting), and the source region of that invocation — the caret a
   "note: expanded from:" line points at. *)
type frame =
  { macro_name : string option
  ; use        : position }

type t

(* An ordinary token: [spelling] is the lexbuf region, expansion chain empty. *)
val of_lexing : position -> t

(* Record one more macro-invocation step, becoming the new innermost frame of
   the chain (closest to the spelling).  The [spelling] is unchanged. *)
val push_expansion : frame -> t -> t

(* The primary caret a diagnostic points at: the outermost invocation site if
   the token came from a macro expansion, otherwise its [spelling]. *)
val primary : t -> position

(* The region where the token's text is actually spelled: the original file for
   ordinary tokens, a macro body for expanded ones. *)
val spelling : t -> position

(* The expansion chain, outermost first; [] for ordinary tokens. *)
val expansion : t -> frame list

val compare : t -> t -> int

val print : Format.formatter -> t -> unit

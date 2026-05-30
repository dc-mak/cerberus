(* A phase-3 preprocessing token (C11 §6.4), the unit the internal preprocessor
   operates on.

   The type is parameterised over the kind of location it carries: the lexer
   produces [(Lexing.position * Lexing.position) t] (a bare spelling region),
   and once the engine lifts the stream it works in [Preproc_location.t t]
   (spelling + macro-expansion chain).  [map] rewrites just the location, which
   is how the lift and the per-step provenance pushes are done. *)

(* The hide set of a token (Prosser's [HS]): the macros whose names must not be
   re-expanded here, preventing infinite recursion.  Held functionally. *)
module Hide_set : Set.S with type elt = string

(* A CN "magic comment" delimited by [/*@ ... @*/] or [/*$ ... $*/].  The lexer
   emits it as a single token; [Cpp] later macro-expands its [payload]. *)
type magic =
  { delimiter : char     (* '@' or '$' *)
  ; payload   : string } (* raw text between the delimiters, sans the markers *)

type kind =
  | Header_name      (* <...> / "..."; produced only when a directive asks *)
  | Identifier
  | Pp_number        (* the lexically greedy pp-number of §6.4.8 *)
  | Char_const
  | String_literal
  | Punctuator
  | Magic of magic
  | Other            (* a lone character matching no other category (§6.4#1) *)
  | Newline          (* explicit line boundary; the engine is line-oriented *)

type 'loc t

val make :
  kind:kind ->
  spelling:string ->
  preceded_by_space:bool ->
  ?hide_set:Hide_set.t ->
  loc:'loc ->
  unit -> 'loc t

val kind : 'loc t -> kind
val spelling : 'loc t -> string

(* Whether whitespace (or a comment) separated this token from the previous one
   on its line; needed to reproduce significant spacing and the [#] stringizing
   rules. *)
val preceded_by_space : 'loc t -> bool

val hide_set : 'loc t -> Hide_set.t
val loc : 'loc t -> 'loc

(* Functional update of the hide set (Prosser's [hsadd]). *)
val with_hide_set : Hide_set.t -> 'loc t -> 'loc t

(* Rewrite only the location, e.g. lift [of_lexing] or push an expansion frame. *)
val map : ('a -> 'b) -> 'a t -> 'b t

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int

val print :
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit

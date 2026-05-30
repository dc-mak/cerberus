(* The parser seam for the internal preprocessor: turn the engine's expanded
   pp-token stream into a Menhir token supplier.

   Each ordinary token is decoded through the shared c_lexer decoder
   ([C_lexer.token_of_string]) so it is exactly the [Tokens.token] the external
   path would produce; a [Magic] token becomes [CERB_MAGIC] for the CN path; a
   [Newline] is dropped.  Source locations (with macro-expansion provenance) are
   carried through a side table: each emitted token's lexbuf positions get a
   synthetic [pos_cnum] key that [lookup] maps back to a [Cerb_position.t].

   Staged like [C_lexer.create_lexer]: [make] allocates the fresh per-parse state
   (token cursor + side table) and [lexer] layers the typedef deferral on top via
   [C_lexer.defer_typedef].  Use one [t] for exactly one parse. *)

type t

val make : Preproc_location.t Preproc_token.t list -> t

val lexer : t -> [ `LEXER of Lexing.lexbuf -> Tokens.token ]

(* The [Cerb_position.t] a synthetic [pos_cnum] keys to; the location seam
   consults this in internal-cpp mode.  [None] if the key is unknown. *)
val lookup : t -> int -> Cerb_position.t option

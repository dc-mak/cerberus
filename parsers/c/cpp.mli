(* The macro engine — translation phase 4 (C11 §6.10).

   [preprocess] lifts the lexer's bare-location tokens to the provenance-carrying
   [Preproc_location.t] (so rescanning can splice freshly produced tokens ahead
   of pending input), then runs Prosser's expand/subst/hsadd under a
   line-oriented directive loop.

   This commit (C6) handles object-like #define / #undef and their expansion,
   with macro-expansion provenance recorded on every produced token.
   Function-like macros, # / ##, conditionals and #include arrive in later
   commits; unrecognised directives are currently skipped. *)

val preprocess :
  (Lexing.position * Lexing.position) Preproc_token.t list ->
  Preproc_location.t Preproc_token.t list

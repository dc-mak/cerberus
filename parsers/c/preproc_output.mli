(* Reconstruct preprocessed source text from a pp-token stream.

   This is the test oracle ONLY — it is never on the parser path, which feeds
   located tokens straight to Menhir (reconstruct-then-relex would lose columns
   and macro provenance).  Spacing follows cscout's golden convention: leading
   indentation and blank lines are dropped, a single space is emitted exactly
   where a token is [preceded_by_space], and each non-empty logical line is
   newline-terminated. *)

val reconstruct : _ Preproc_token.t list -> string

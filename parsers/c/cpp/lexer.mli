(* Translation phase 3 (C11 §6.4): turn raw source bytes into the preprocessor's
   pp-token stream, each token carrying its exact (start, end) Lexing.position so
   columns survive untouched.

   The stream is explicitly line-oriented: a [Newline] token marks each logical
   line boundary (the directive loop scans for [#] at line starts).  Block and
   magic comments may span several physical lines — their internal newlines
   advance the line counter but emit no [Newline] token, so a directive or macro
   invocation can span them.  A comment becomes inter-token whitespace
   ([preceded_by_space] on the following token). *)

val tokens :
  Lexing.lexbuf -> (Lexing.position * Lexing.position) Token.t list

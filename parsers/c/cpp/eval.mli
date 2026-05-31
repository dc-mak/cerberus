(* Evaluator for the controlling constant expression of #if / #elif
   (C11 §6.10.1).

   The caller (the engine) is responsible for the preprocessing that precedes
   evaluation: replacing each [defined X] / [defined(X)] with 0 or 1, then
   macro-expanding the line.  [eval] takes the resulting token list, maps any
   identifier that survives to 0 (C23 [true]/[false] to 1/0), and evaluates the
   integer-constant-expression with intmax_t / uintmax_t semantics, returning
   whether it is non-zero.

   Arithmetic is done in 64-bit; an operand with an unsigned suffix (or a value
   that does not fit the signed range) makes the usual-arithmetic-conversion
   result unsigned, which changes /, %, >> and the comparisons.  A malformed
   expression (a float, an unbalanced paren, division by zero, …) yields an
   [Error] message rather than raising. *)

val eval : Location.t Token.t list -> (bool, string) result

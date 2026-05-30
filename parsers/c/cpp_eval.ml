(* A recursive-descent integer-constant-expression evaluator.  Values are carried
   as a 64-bit pattern plus a signedness flag ([u]); the "usual arithmetic
   conversions" make a result unsigned if either operand is, which selects the
   unsigned variants of /, %, >> and the comparisons.  Errors are threaded as a
   result rather than raised (per the project's no-exceptions guidance). *)

type value = { v : int64; u : bool }

let ( let* ) = Result.bind
let ok x = Ok x

let truth value = not (Int64.equal value.v 0L)
let unsigned a b = a.u || b.u

(* --- Local token predicates (kept independent of the engine) --------------- *)

let is_newline t =
  match Preproc_token.kind t with Preproc_token.Newline -> true | _ -> false

let is_punct s t =
  match Preproc_token.kind t with
  | Preproc_token.Punctuator -> String.equal (Preproc_token.spelling t) s
  | _ -> false

(* --- Decoding numeric and character constants ------------------------------ *)

(* Strip the integer suffix, reporting whether a u/U was present, and normalise
   the prefix so Int64.of_string can parse it (octal needs an explicit 0o). *)
let decode_number spelling =
  let n = String.length spelling in
  (* count trailing [uUlL] *)
  let rec suffix_start i =
    if i > 0 then
      match spelling.[i - 1] with
      | 'u' | 'U' | 'l' | 'L' -> suffix_start (i - 1)
      | _ -> i
    else i
  in
  let body_end = suffix_start n in
  let suffix = String.sub spelling body_end (n - body_end) in
  let unsigned =
    String.exists (fun c -> Char.equal c 'u' || Char.equal c 'U') suffix in
  let body = String.sub spelling 0 body_end in
  (* a '.' or a decimal exponent makes it a floating constant, illegal in #if *)
  let is_float =
    String.exists (fun c -> Char.equal c '.') body
    || (let lower = String.lowercase_ascii body in
        not (String.length lower >= 2
             && Char.equal lower.[0] '0'
             && (Char.equal lower.[1] 'x'))
        && String.exists (fun c -> Char.equal c 'e') lower)
  in
  if is_float then Error ("floating constant in #if: " ^ spelling)
  else
    let normalised =
      let lower = String.lowercase_ascii body in
      if String.length lower >= 2 && Char.equal lower.[0] '0'
         && (Char.equal lower.[1] 'x' || Char.equal lower.[1] 'b')
      then body
      else if String.length body >= 2 && Char.equal body.[0] '0' then
        (* octal: 0NNN -> 0oNNN *)
        "0o" ^ String.sub body 1 (String.length body - 1)
      else body
    in
    match Int64.of_string_opt normalised with
    | Some v -> ok { v; u = unsigned }
    | None ->
        (* a decimal too large for signed int64 is an unsigned intmax constant *)
        (match Int64.of_string_opt ("0u" ^ normalised) with
         | Some v -> ok { v; u = true }
         | None -> Error ("invalid integer constant in #if: " ^ spelling))

(* The value of a character constant: decode the (possibly escaped) first
   c-char.  Encoding prefixes (L/u/U) are ignored. *)
let decode_char spelling =
  let body =
    match String.index_opt spelling '\'' with
    | Some i -> String.sub spelling (i + 1) (String.length spelling - i - 2)
    | None -> spelling
  in
  let code =
    if String.length body >= 2 && Char.equal body.[0] '\\' then
      match body.[1] with
      | 'n' -> 10 | 't' -> 9 | 'r' -> 13 | '0' -> 0 | 'a' -> 7 | 'b' -> 8
      | 'f' -> 12 | 'v' -> 11 | '\\' -> 92 | '\'' -> 39 | '"' -> 34 | '?' -> 63
      | 'x' ->
          (try int_of_string ("0x" ^ String.sub body 2 (String.length body - 2))
           with _ -> 0)
      | c -> Char.code c
    else if String.length body >= 1 then Char.code body.[0]
    else 0
  in
  { v = Int64.of_int code; u = false }

let ident_value spelling =
  match spelling with
  | "true" -> { v = 1L; u = false }
  | _ -> { v = 0L; u = false }

(* --- Binary operators ------------------------------------------------------ *)

let bool_value b = { v = (if b then 1L else 0L); u = false }

(* additive/bitwise ops share two's-complement bit patterns regardless of sign *)
let wrap f a b = ok { v = f a.v b.v; u = unsigned a b }

let div_op a b =
  if Int64.equal b.v 0L then Error "division by zero in #if"
  else ok { v = (if unsigned a b then Int64.unsigned_div a.v b.v
                 else Int64.div a.v b.v); u = unsigned a b }

let rem_op a b =
  if Int64.equal b.v 0L then Error "division by zero in #if"
  else ok { v = (if unsigned a b then Int64.unsigned_rem a.v b.v
                 else Int64.rem a.v b.v); u = unsigned a b }

let shl a b = ok { v = Int64.shift_left a.v (Int64.to_int b.v); u = a.u }
let shr a b =
  ok { v = (if a.u then Int64.shift_right_logical a.v (Int64.to_int b.v)
            else Int64.shift_right a.v (Int64.to_int b.v)); u = a.u }

let cmp a b = if unsigned a b then Int64.unsigned_compare a.v b.v
              else Int64.compare a.v b.v

(* Map an operator spelling to its semantics for a given precedence level. *)
let mul_op t =
  if is_punct "*" t then Some (wrap Int64.mul)
  else if is_punct "/" t then Some div_op
  else if is_punct "%" t then Some rem_op
  else None

let add_op t =
  if is_punct "+" t then Some (wrap Int64.add)
  else if is_punct "-" t then Some (wrap Int64.sub)
  else None

let shift_op t =
  if is_punct "<<" t then Some shl
  else if is_punct ">>" t then Some shr
  else None

let rel_op t =
  if is_punct "<" t then Some (fun a b -> ok (bool_value (cmp a b < 0)))
  else if is_punct ">" t then Some (fun a b -> ok (bool_value (cmp a b > 0)))
  else if is_punct "<=" t then Some (fun a b -> ok (bool_value (cmp a b <= 0)))
  else if is_punct ">=" t then Some (fun a b -> ok (bool_value (cmp a b >= 0)))
  else None

let eq_op t =
  if is_punct "==" t then Some (fun a b -> ok (bool_value (cmp a b = 0)))
  else if is_punct "!=" t then Some (fun a b -> ok (bool_value (cmp a b <> 0)))
  else None

let band_op t = if is_punct "&" t then Some (wrap Int64.logand) else None
let bxor_op t = if is_punct "^" t then Some (wrap Int64.logxor) else None
let bor_op t = if is_punct "|" t then Some (wrap Int64.logor) else None
let land_op t =
  if is_punct "&&" t then Some (fun a b -> ok (bool_value (truth a && truth b)))
  else None
let lor_op t =
  if is_punct "||" t then Some (fun a b -> ok (bool_value (truth a || truth b)))
  else None

(* --- Recursive-descent parser ---------------------------------------------- *)

(* A left-associative binary level: parse one [sub], then fold in as many
   [op sub] as match. *)
let left_assoc sub opf toks =
  let* (l, toks) = sub toks in
  let rec loop l toks =
    match toks with
    | op :: toks' ->
        (match opf op with
         | Some f ->
             let* (r, toks'') = sub toks' in
             let* res = f l r in
             loop res toks''
         | None -> ok (l, toks))
    | [] -> ok (l, toks)
  in
  loop l toks

let rec parse_primary toks =
  match toks with
  | t :: toks' when is_punct "(" t ->
      let* (v, toks') = parse_cond toks' in
      (match toks' with
       | t2 :: toks'' when is_punct ")" t2 -> ok (v, toks'')
       | _ -> Error "expected ')' in #if expression")
  | t :: toks' ->
      (match Preproc_token.kind t with
       | Preproc_token.Pp_number ->
           let* v = decode_number (Preproc_token.spelling t) in ok (v, toks')
       | Preproc_token.Char_const -> ok (decode_char (Preproc_token.spelling t), toks')
       | Preproc_token.Identifier -> ok (ident_value (Preproc_token.spelling t), toks')
       | _ -> Error ("unexpected '" ^ Preproc_token.spelling t ^ "' in #if expression"))
  | [] -> Error "unexpected end of #if expression"

and parse_unary toks =
  match toks with
  | t :: toks' when is_punct "+" t -> parse_unary toks'
  | t :: toks' when is_punct "-" t ->
      let* (v, toks') = parse_unary toks' in ok ({ v with v = Int64.neg v.v }, toks')
  | t :: toks' when is_punct "!" t ->
      let* (v, toks') = parse_unary toks' in ok (bool_value (not (truth v)), toks')
  | t :: toks' when is_punct "~" t ->
      let* (v, toks') = parse_unary toks' in ok ({ v with v = Int64.lognot v.v }, toks')
  | _ -> parse_primary toks

and parse_mul toks = left_assoc parse_unary mul_op toks
and parse_add toks = left_assoc parse_mul add_op toks
and parse_shift toks = left_assoc parse_add shift_op toks
and parse_rel toks = left_assoc parse_shift rel_op toks
and parse_eq toks = left_assoc parse_rel eq_op toks
and parse_band toks = left_assoc parse_eq band_op toks
and parse_bxor toks = left_assoc parse_band bxor_op toks
and parse_bor toks = left_assoc parse_bxor bor_op toks
and parse_land toks = left_assoc parse_bor land_op toks
and parse_lor toks = left_assoc parse_land lor_op toks

and parse_cond toks =
  let* (c, toks) = parse_lor toks in
  match toks with
  | q :: toks' when is_punct "?" q ->
      let* (a, toks') = parse_cond toks' in
      (match toks' with
       | colon :: toks'' when is_punct ":" colon ->
           let* (b, toks'') = parse_cond toks'' in
           ok ((if truth c then a else b), toks'')
       | _ -> Error "expected ':' in #if ?: expression")
  | _ -> ok (c, toks)

let eval toks =
  let toks = List.filter (fun t -> not (is_newline t)) toks in
  match parse_cond toks with
  | Ok (v, []) -> Ok (truth v)
  | Ok (_, _ :: _) -> Error "trailing tokens in #if expression"
  | Error _ as e -> e

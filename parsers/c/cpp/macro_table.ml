module Env = Map.Make (String)

type token = Location.t Token.t

type definition =
  | Object_like of token list
  | Function_like of
      { params   : string list
      ; variadic : bool
      ; body     : token list }

type t = definition Env.t

let empty = Env.empty

(* Token equivalence for the §6.10.3 redefinition check: lexeme, kind, hide set
   and white-space flag must match; the location does not (it points into a
   different #define).  Bodies are freshly defined so hide sets are empty, and a
   replacement list's first token is always space-separated from the name, so
   comparing the flag verbatim does not spuriously reject the "ignore leading
   white-space" cases of the Standard. *)
let token_compat = Token.compare (fun _ _ -> 0)

let rec same_tokens a b =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> token_compat x y = 0 && same_tokens xs ys
  | _ -> false

let rec same_params a b =
  match a, b with
  | [], [] -> true
  | x :: xs, y :: ys -> String.equal x y && same_params xs ys
  | _ -> false

let compatible d1 d2 =
  match d1, d2 with
  | Object_like b1, Object_like b2 -> same_tokens b1 b2
  | Function_like f1, Function_like f2 ->
      Bool.equal f1.variadic f2.variadic
      && same_params f1.params f2.params
      && same_tokens f1.body f2.body
  | Object_like _, Function_like _
  | Function_like _, Object_like _ -> false

let define name def t =
  match Env.find_opt name t with
  | Some old when not (compatible old def) -> Error old
  | _ -> Ok (Env.add name def t)

let undef name t = Env.remove name t
let find name t = Env.find_opt name t
let mem name t = Env.mem name t

let print_tokens ppf toks =
  List.iter
    (fun tok -> Format.fprintf ppf "@ %s" (Token.lexeme tok))
    toks

let print_definition ppf = function
  | Object_like body ->
      Format.fprintf ppf "@[<h>%a@]" print_tokens body
  | Function_like { params; variadic; body } ->
      let params =
        if variadic then params @ ["..."] else params in
      Format.fprintf ppf "@[<h>(%s)%a@]"
        (String.concat ", " params) print_tokens body

let print ppf t =
  Format.fprintf ppf "@[<v>";
  List.iter
    (fun (name, def) ->
       Format.fprintf ppf "#define %s%a@," name print_definition def)
    (Env.bindings t);
  Format.fprintf ppf "@]"

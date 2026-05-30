module Hide_set = Set.Make (String)

type magic =
  { delimiter : char
  ; payload   : string }

type kind =
  | Header_name
  | Identifier
  | Pp_number
  | Char_const
  | String_literal
  | Punctuator
  | Magic of magic
  | Other
  | Newline

type 'loc t =
  { kind              : kind
  ; spelling          : string
  ; preceded_by_space : bool
  ; hide_set          : Hide_set.t
  ; loc               : 'loc }

let make ~kind ~spelling ~preceded_by_space ?(hide_set = Hide_set.empty) ~loc () =
  { kind; spelling; preceded_by_space; hide_set; loc }

let kind t = t.kind
let spelling t = t.spelling
let preceded_by_space t = t.preceded_by_space
let hide_set t = t.hide_set
let loc t = t.loc

let with_hide_set hide_set t = { t with hide_set }

let map f t = { t with loc = f t.loc }

(* A token-kind ordering used only to give [compare] a total order; the integer
   tags are arbitrary but must agree with the variant list below. *)
let kind_tag = function
  | Header_name    -> 0
  | Identifier     -> 1
  | Pp_number      -> 2
  | Char_const     -> 3
  | String_literal -> 4
  | Punctuator     -> 5
  | Magic _        -> 6
  | Other          -> 7
  | Newline        -> 8

let compare_kind k1 k2 =
  match k1, k2 with
  | Magic m1, Magic m2 ->
      let c = Char.compare m1.delimiter m2.delimiter in
      if c <> 0 then c else String.compare m1.payload m2.payload
  | _ -> Int.compare (kind_tag k1) (kind_tag k2)

let compare compare_loc t1 t2 =
  let c = compare_kind t1.kind t2.kind in
  if c <> 0 then c else
  let c = String.compare t1.spelling t2.spelling in
  if c <> 0 then c else
  let c = Bool.compare t1.preceded_by_space t2.preceded_by_space in
  if c <> 0 then c else
  let c = Hide_set.compare t1.hide_set t2.hide_set in
  if c <> 0 then c else
  compare_loc t1.loc t2.loc

let print print_loc ppf t =
  let space = if t.preceded_by_space then "_" else "" in
  Format.fprintf ppf "@[%s%S at %a@]" space t.spelling print_loc t.loc

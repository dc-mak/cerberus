type position = Lexing.position * Lexing.position

type frame =
  { macro_name : string option
  ; use        : position }

(* The expansion chain is held outermost-first.  [push_expansion] appends, so a
   freshly pushed frame is the innermost one (nearest the spelling), matching how
   the engine drives deeper into nested macro bodies. *)
type t =
  { spelling  : position
  ; expansion : frame list }

let of_lexing spelling = { spelling; expansion = [] }

let push_expansion frame t = { t with expansion = t.expansion @ [frame] }

let primary t =
  match t.expansion with
  | [] -> t.spelling
  | frame :: _ -> frame.use

let spelling t = t.spelling

let expansion t = t.expansion

(* [Lexing.position] is a plain record; compare it field-by-field rather than
   with the polymorphic comparison.  [pos_cnum] is an absolute byte offset, so
   it disambiguates within a file; [pos_fname] separates files. *)
let compare_lexing (p : Lexing.position) (q : Lexing.position) =
  let c = String.compare p.Lexing.pos_fname q.Lexing.pos_fname in
  if c <> 0 then c else
  let c = Int.compare p.Lexing.pos_lnum q.Lexing.pos_lnum in
  if c <> 0 then c else
  Int.compare p.Lexing.pos_cnum q.Lexing.pos_cnum

let compare_position (p1, p2) (q1, q2) =
  let c = compare_lexing p1 q1 in
  if c <> 0 then c else compare_lexing p2 q2

let compare_option cmp o1 o2 =
  match o1, o2 with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some x, Some y -> cmp x y

let compare_frame f1 f2 =
  let c = compare_option String.compare f1.macro_name f2.macro_name in
  if c <> 0 then c else compare_position f1.use f2.use

let rec compare_frames fs1 fs2 =
  match fs1, fs2 with
  | [], [] -> 0
  | [], _ :: _ -> -1
  | _ :: _, [] -> 1
  | f1 :: r1, f2 :: r2 ->
      let c = compare_frame f1 f2 in
      if c <> 0 then c else compare_frames r1 r2

let compare t1 t2 =
  let c = compare_position t1.spelling t2.spelling in
  if c <> 0 then c else compare_frames t1.expansion t2.expansion

let print_position ppf ((p, _) : position) =
  Format.fprintf ppf "%s:%d:%d"
    p.Lexing.pos_fname p.Lexing.pos_lnum
    (p.Lexing.pos_cnum - p.Lexing.pos_bol + 1)

let print_frame ppf frame =
  let name = match frame.macro_name with Some n -> n | None -> "<paste>" in
  Format.fprintf ppf "expanded from %s at %a" name print_position frame.use

let print ppf t =
  Format.fprintf ppf "@[<v>spelled at %a" print_position t.spelling;
  List.iter (fun f -> Format.fprintf ppf "@,%a" print_frame f) t.expansion;
  Format.fprintf ppf "@]"

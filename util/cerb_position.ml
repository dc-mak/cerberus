
(* The lexing position is the real location in the file parsed.
In particular, this is likely a file that was produced by the pre-processor.
The `source_file` and `source_line` refer to the locations in the original
source, if one is available, otherwise they should match what's in `file`.
*)
type macro_use =
  { macro_name : string option
  ; caret      : Lexing.position * Lexing.position }

type t = {
  file: Lexing.position; (* position in the pre-processed file *)
  source_file: string;   (* file containing the original source *)
  source_line: int;      (* line number in the original file *)
  expansions: macro_use list;
  (* Macro-expansion chain (outermost first) for tokens produced by the internal
     preprocessor; [] for ordinary tokens, so the external path is unaffected.
     change_cnum / set_source preserve it via functional record update. *)
}

let dummy = { file = Lexing.dummy_pos; source_file = ""; source_line = 0;
              expansions = [] }

let from_lexing p =
  { file = p; source_file = p.pos_fname; source_line = p.pos_lnum;
    expansions = [] }

let line pos = pos.source_line
let file pos = pos.source_file


(* Column for this position, 1 based *)
let column pos =
  let f = pos.file in
  Lexing.(1 + f.pos_cnum - f.pos_bol)

let to_file_lexing p = p.file

let change_cnum pos n =
  { pos with file = { pos.file with pos_cnum = pos.file.pos_cnum + n } }

let set_source (f,n) pos = { pos with source_file = f; source_line = n }

let expansions pos = pos.expansions
let with_expansions expansions pos = { pos with expansions }

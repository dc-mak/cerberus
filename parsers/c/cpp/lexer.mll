{
open Lexing

(* The outcome of reading one lexical unit.  Whitespace and comments produce
   [Skip] (recorded as "the next token is preceded by space"); everything that
   the preprocessor keeps — including explicit [Newline]s — produces [Tok]. *)
type lexeme =
  | Tok of (position * position) Token.t
  | Skip
  | Done

let mk space kind lexbuf =
  Token.make ~kind ~lexeme:(Lexing.lexeme lexbuf)
    ~preceded_by_space:space
    ~loc:(lexbuf.lex_start_p, lexbuf.lex_curr_p) ()
}

(* ========================================================================== *)

let digit    = ['0'-'9']
let octal_digit = ['0'-'7']
let hexadecimal_digit = ['0'-'9' 'A'-'F' 'a'-'f']

let hex_quad = hexadecimal_digit hexadecimal_digit
                 hexadecimal_digit hexadecimal_digit
let universal_character_name =
    "\\u" hex_quad
  | "\\U" hex_quad hex_quad

(* §6.4.2 identifiers *)
let nondigit = ['_' 'a'-'z' 'A'-'Z']
let identifier_nondigit = nondigit | universal_character_name
let identifier = identifier_nondigit (identifier_nondigit | digit)*

(* §6.4.8 pp-numbers: a deliberately permissive lexical category that need not be
   a valid numeric constant (e.g. [1e+], [0x.p]). *)
let pp_exponent = ['e' 'E' 'p' 'P'] ['+' '-']
let pp_number =
  ('.'? digit) (digit | identifier_nondigit | '.' | pp_exponent)*

(* §6.4.4.4 / §6.4.5 escape sequences, char- and string-literals *)
let simple_escape =
  '\\' ['\'' '"' '?' '\\' 'a' 'b' 'f' 'n' 'r' 't' 'v']
let octal_escape =
    '\\' octal_digit
  | '\\' octal_digit octal_digit
  | '\\' octal_digit octal_digit octal_digit
let hex_escape = "\\x" hexadecimal_digit+
let escape_sequence =
    simple_escape | octal_escape | hex_escape | universal_character_name

(* Lenient at phase 3: a backslash escapes any following character (even an
   invalid escape like \e), so the whole literal is one token.  c_lexer validates
   and decodes it when the feed re-lexes the lexeme — matching where the
   external path reports an invalid-string-character error. *)
let s_char = [^ '"' '\\' '\n'] | '\\' [^ '\n']
let c_char = [^ '\'' '\\' '\n'] | '\\' [^ '\n']

let string_encoding = "u8" | 'u' | 'U' | 'L'
let char_encoding = 'u' | 'U' | 'L'
let string_literal = string_encoding? '"' s_char* '"'
let char_const = char_encoding? "'" c_char+ "'"

(* §6.4.6 punctuators (including digraphs).  [#] and [##] matter to the engine;
   the rest are carried through verbatim by lexeme. *)
let punctuator =
    "%:%:" | "..." | "<<=" | ">>="
  (* Cerberus/CN extensions c_lexer also recognises (kept as single tokens so the
     feed's re-lex matches: :: scope, ?: GNU, {-{ ||| }-} thread syntax). *)
  | "{-{" | "}-}" | "|||" | "::" | "?:"
  | "->" | "++" | "--" | "<<" | ">>" | "<=" | ">=" | "==" | "!="
  | "&&" | "||" | "*=" | "/=" | "%=" | "+=" | "-=" | "&=" | "^=" | "|="
  | "##" | "<:" | ":>" | "<%" | "%>" | "%:"
  | "[" | "]" | "(" | ")" | "{" | "}" | "." | "&" | "*" | "+" | "-"
  | "~" | "!" | "/" | "%" | "<" | ">" | "^" | "|" | "?" | ":" | ";"
  | "=" | "," | "#"

let whitespace_char = [' ' '\t' '\012' '\r']

(* ========================================================================== *)

rule one space = parse
  (* CN magic comments — one [Magic] token carrying its raw payload.  Saved
     start position because the sub-rule moves [lex_start_p]. *)
  | "/*" (['@' '$'] as delim)
      { let start_p = lexbuf.lex_start_p in
        let inner = magic_body (Buffer.create 32) lexbuf in
        let n = String.length inner in
        if n >= 1 && inner.[n - 1] = delim then
          let payload = String.sub inner 0 (n - 1) in
          let lexeme = Printf.sprintf "/*%c%s*/" delim inner in
          Tok (Token.make
                 ~kind:(Token.Magic { delimiter = delim; payload })
                 ~lexeme ~preceded_by_space:space
                 ~loc:(start_p, lexbuf.lex_curr_p) ())
        else
          (* Not a well-formed magic comment: treat as ordinary whitespace. *)
          Skip }

  | "/*" { block_comment lexbuf; Skip }
  | "//" { line_comment lexbuf; Skip }

  | '\n' { let t = mk space Token.Newline lexbuf in
           new_line lexbuf; Tok t }
  | whitespace_char+ { Skip }

  | string_literal { Tok (mk space Token.String_literal lexbuf) }
  | char_const     { Tok (mk space Token.Char_const lexbuf) }
  | pp_number      { Tok (mk space Token.Pp_number lexbuf) }
  | identifier     { Tok (mk space Token.Identifier lexbuf) }
  (* C2x attribute opener: kept as one token (matching c_lexer's lbrack_lbrack)
     so the feed's re-lex yields LBRACK_LBRACK rather than two LBRACK, which the
     grammar needs to disambiguate from array declarators. *)
  | '[' whitespace_char* '[' { Tok (mk space Token.Punctuator lexbuf) }
  | punctuator     { Tok (mk space Token.Punctuator lexbuf) }

  | eof { Done }

  (* §6.4#1: any other single non-whitespace character is its own pp-token. *)
  | _   { Tok (mk space Token.Other lexbuf) }

(* A block comment is replaced by one space; its internal newlines are retained
   only for line counting (§5.1.1.2), so they do not break the logical line. *)
and block_comment = parse
  | "*/" { () }
  | '\n' { new_line lexbuf; block_comment lexbuf }
  | eof  { () }
  | _    { block_comment lexbuf }

(* A // comment runs to — but not over — the end of the line, so [one] still
   sees the newline. *)
and line_comment = parse
  | [^ '\n']* { () }

(* Collect a magic comment's inner text (delimiters excluded at the front by the
   caller's match, the trailing one left in [inner] for validation). *)
and magic_body buf = parse
  | "*/" { Buffer.contents buf }
  | '\n' { Buffer.add_char buf '\n'; new_line lexbuf; magic_body buf lexbuf }
  | eof  { Buffer.contents buf }
  | _ as c { Buffer.add_char buf c; magic_body buf lexbuf }

(* ========================================================================== *)

{
let tokens lexbuf =
  let rec loop space acc =
    match one space lexbuf with
    | Done   -> List.rev acc
    | Skip   -> loop true acc
    | Tok t  -> loop false (t :: acc)
  in
  loop false []
}

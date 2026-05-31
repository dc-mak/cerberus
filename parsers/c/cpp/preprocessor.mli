(* The macro engine — translation phase 4 (C11 §6.10).

   [preprocess ~include_dirs ~filename] reads and lexes [filename], lifts the
   tokens to the provenance-carrying [Location.t] (so rescanning can
   splice freshly produced tokens ahead of pending input), and runs Prosser's
   expand/subst/hsadd under a line-oriented directive loop.

   Handles object- and function-like #define / #undef, # and ##, the conditional
   directives (#if/#ifdef/#ifndef/#elif/#else/#endif with `defined` and constant
   expressions), and #include / #pragma once.  "..." includes search the current
   file's directory then [include_dirs]; <...> includes search only
   [include_dirs] (no system paths).  #line / #error are currently consumed
   without effect. *)

(* The raw-location map returned alongside the token stream.  Each output token's
   primary start position carries a unique synthetic [pos_bol] key (a counter,
   not a real byte offset); the other Lexing fields ([pos_fname], [pos_lnum],
   [pos_cnum]) stay accurate so the raw token is still useful for debugging.
   Looking up that key recovers the real [pos_bol] (so the column comes out
   right) and the token's macro-expansion chain and lexeme.

   The map is built during [preprocess] and is read-only here: callers can only
   [lookup], never extend it. *)
type entry =
  { actual_pos_bol : int            (* the real line-start byte offset *)
  ; expansions     : Location.frame list  (* outermost-first; [] if ordinary *)
  ; lexeme         : string         (* the token's spelling, for diagnostics *)
  }

type raw_loc_map

val lookup : raw_loc_map -> int -> entry option

(* The macro environment in scope at each top-level magic comment, so its CN
   payload can be macro-expanded on re-parse.  Immutable and keyed by the magic
   token's synthetic [pos_bol] key — the same key its CERB_MAGIC location carries
   into the AST, so the re-parser recovers the table from the parsed location.
   Only magic comments have an entry; ordinary tokens are absent. *)
type macro_defns

val find_macro_defns : macro_defns -> int -> Macro_table.t option

val preprocess :
  include_dirs:string list ->
  predefined:(string * string option) list ->
  undefs:string list ->
  forced_includes:string list ->
  filename:string ->
  Location.t Token.t list * raw_loc_map * macro_defns

(* Lex and macro-expand a magic comment's CN payload with the given in-scope
   macro table, yielding the located tokens + raw_loc_map the parser feed
   consumes.  [lexbuf] must already be positioned (filename + start) at the
   payload's place in the original file. *)
val expand_fragment :
  Macro_table.t -> Lexing.lexbuf -> Location.t Token.t list * raw_loc_map

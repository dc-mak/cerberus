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

val preprocess :
  include_dirs:string list ->
  predefined:(string * string option) list ->
  undefs:string list ->
  forced_includes:string list ->
  filename:string ->
  Location.t Token.t list

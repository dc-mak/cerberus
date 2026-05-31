(* Rewrite every source location (on Cabs nodes, Symbol.identifiers and inside
   Annot.attributes) of a translation unit by applying the given function to each
   Cerb_position.  Used to from_raw the internal preprocessor's raw, side-table-key
   positions into resolved ones after parsing; CN subtrees and constants are left
   untouched. *)
(* [traverse_cn] (default [false]) controls whether CN subtrees (EDecl_*CN) are
   rewritten.  The outer translation-unit pass leaves them alone (they are resolved
   separately, against the magic-comment fragment's own map); the fragment
   resolution sets it to [true]. *)
val from_raw :
  ?traverse_cn:bool ->
  (Cerb_position.t -> Cerb_position.t) ->
  Cabs.translation_unit -> Cabs.translation_unit

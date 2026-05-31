(* Rewrite every source location (on Cabs nodes, Symbol.identifiers and inside
   Annot.attributes) of a translation unit by applying the given function to each
   Cerb_position.  Used to from_raw the internal preprocessor's raw, side-table-key
   positions into resolved ones after parsing; CN subtrees and constants are left
   untouched. *)
val from_raw :
  (Cerb_position.t -> Cerb_position.t) ->
  Cabs.translation_unit -> Cabs.translation_unit

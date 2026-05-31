(* Eager post-parse location resolution.

   Rewrite every source location in a Cabs translation unit by applying [f] to
   each Cerb_position.  The internal preprocessor produces a parse tree whose
   positions carry a synthetic [pos_bol] key into its raw-location map (see
   Cpp.Preprocessor); this turns them into resolved positions.  The external
   path passes [Fun.id], so this is a no-op there (and the driver skips it).

   Locations live not only on the obvious Cabs nodes but on every
   [Symbol.identifier] and inside [Annot.attributes], so all three are rewritten.
   CN subtrees (EDecl_*CN) and Cabs constants are left untouched: CN locations
   come from the magic-comment re-parse (already resolved) and constants carry
   none.

   TODO(efficiency): this is a full structural traversal that rebuilds the tree.
   A lazy scheme that maps a position only when a location is printed — and/or a
   switch between eager and lazy — would avoid the rebuild.  Kept eager for now
   so existing library consumers (other backends) see resolved locations with no
   API change.  Also worth revisiting once the Menhir incremental API is in use.

   These types are generated from Lem specs and change rarely; this is a plain
   traversal over them, so the maintenance cost is low. *)

open Cabs

let from_raw f tu =
  let el = Cerb_location.map_positions f in
  let ident (Symbol.Identifier (loc, s)) = Symbol.Identifier (el loc, s) in
  let ident_opt = Option.map ident in
  let attribute (a : Annot.attribute) =
    { Annot.attr_ns = ident_opt a.Annot.attr_ns
    ; attr_id = ident a.Annot.attr_id
    ; attr_args =
        List.map
          (fun (loc, s, args) -> (el loc, s, List.map (fun (l, x) -> (el l, x)) args))
          a.Annot.attr_args }
  in
  let attributes (Annot.Attrs attrs) = Annot.Attrs (List.map attribute attrs) in
  let string_literal (prefix, chunks) =
    (prefix, List.map (fun (loc, strs) -> (el loc, strs)) chunks)
  in
  let rec expression (CabsExpression (loc, e_)) =
    CabsExpression (el loc, expression_ e_)
  and expression_ = function
    | CabsEident id -> CabsEident (ident id)
    | CabsEconst c -> CabsEconst c
    | CabsEstring sl -> CabsEstring (string_literal sl)
    | CabsEgeneric (e, gas) -> CabsEgeneric (expression e, List.map generic_assoc gas)
    | CabsEsubscript (e1, e2) -> CabsEsubscript (expression e1, expression e2)
    | CabsEcall (e, es, attrs) ->
        CabsEcall (expression e, List.map expression es, Option.map attributes attrs)
    | CabsEmemberof (e, id) -> CabsEmemberof (expression e, ident id)
    | CabsEmemberofptr (e, id) -> CabsEmemberofptr (expression e, ident id)
    | CabsEpostincr e -> CabsEpostincr (expression e)
    | CabsEpostdecr e -> CabsEpostdecr (expression e)
    | CabsEcompound (tn, items) -> CabsEcompound (type_name tn, List.map init_item items)
    | CabsEpreincr e -> CabsEpreincr (expression e)
    | CabsEpredecr e -> CabsEpredecr (expression e)
    | CabsEunary (op, e) -> CabsEunary (op, expression e)
    | CabsEsizeof_expr e -> CabsEsizeof_expr (expression e)
    | CabsEsizeof_type tn -> CabsEsizeof_type (type_name tn)
    | CabsEalignof tn -> CabsEalignof (type_name tn)
    | CabsEcast (tn, e) -> CabsEcast (type_name tn, expression e)
    | CabsEbinary (op, e1, e2) -> CabsEbinary (op, expression e1, expression e2)
    | CabsEcond (e1, e2, e3) -> CabsEcond (expression e1, expression e2, expression e3)
    | CabsEassign (op, e1, e2) -> CabsEassign (op, expression e1, expression e2)
    | CabsEcomma (e1, e2) -> CabsEcomma (expression e1, expression e2)
    | CabsEassert e -> CabsEassert (expression e)
    | CabsEoffsetof (tn, id) -> CabsEoffsetof (type_name tn, ident id)
    | CabsEva_start (e, id) -> CabsEva_start (expression e, ident id)
    | CabsEva_copy (e1, e2) -> CabsEva_copy (expression e1, expression e2)
    | CabsEva_arg (e, tn) -> CabsEva_arg (expression e, type_name tn)
    | CabsEva_end e -> CabsEva_end (expression e)
    | CabsEprint_type e -> CabsEprint_type (expression e)
    | CabsEbmc_assume e -> CabsEbmc_assume (expression e)
    | CabsEgcc_statement ss -> CabsEgcc_statement (List.map statement ss)
    | CabsEcondGNU (e1, e2) -> CabsEcondGNU (expression e1, expression e2)
    | CabsEbuiltinGNU b -> CabsEbuiltinGNU (gnu_builtin b)
  and gnu_builtin = function
    | GNUbuiltin_types_compatible_p (tn1, tn2) ->
        GNUbuiltin_types_compatible_p (type_name tn1, type_name tn2)
    | GNUbuiltin_choose_expr (e1, e2, e3) ->
        GNUbuiltin_choose_expr (expression e1, expression e2, expression e3)
  and generic_assoc = function
    | GA_type (tn, e) -> GA_type (type_name tn, expression e)
    | GA_default e -> GA_default (expression e)
  and init_item (designators, init) =
    (Option.map (List.map designator) designators, initializer_ init)
  and designator = function
    | Desig_array e -> Desig_array (expression e)
    | Desig_member id -> Desig_member (ident id)
  and initializer_ = function
    | Init_expr e -> Init_expr (expression e)
    | Init_list (loc, items) -> Init_list (el loc, List.map init_item items)
  and type_name (Type_name (tss, tqs, als, ad)) =
    Type_name (List.map type_specifier tss, tqs,
               List.map alignment_specifier als, Option.map abstract_declarator ad)
  and type_specifier (TSpec (loc, ts_)) = TSpec (el loc, type_specifier_ ts_)
  and type_specifier_ = function
    | (TSpec_void | TSpec_char | TSpec_short | TSpec_int | TSpec_long
      | TSpec_float | TSpec_double | TSpec_signed | TSpec_unsigned
      | TSpec_Bool | TSpec_Complex) as t -> t
    | TSpec_Atomic tn -> TSpec_Atomic (type_name tn)
    | TSpec_struct (attrs, id, sds) ->
        TSpec_struct (attributes attrs, ident_opt id,
                      Option.map (List.map struct_declaration) sds)
    | TSpec_union (attrs, id, sds) ->
        TSpec_union (attributes attrs, ident_opt id,
                     Option.map (List.map struct_declaration) sds)
    | TSpec_enum (id, enums) ->
        TSpec_enum (ident_opt id,
                    Option.map
                      (List.map (fun (i, e) -> (ident i, Option.map expression e)))
                      enums)
    | TSpec_name id -> TSpec_name (ident id)
    | TSpec_typeof_expr e -> TSpec_typeof_expr (expression e)
    | TSpec_typeof_type tn -> TSpec_typeof_type (type_name tn)
  and struct_declaration = function
    | Struct_declaration (attrs, tss, tqs, als, sds) ->
        Struct_declaration (attributes attrs, List.map type_specifier tss, tqs,
                            List.map alignment_specifier als,
                            List.map struct_declarator sds)
    | Struct_assert sad -> Struct_assert (static_assert sad)
  and struct_declarator = function
    | SDecl_simple d -> SDecl_simple (declarator d)
    | SDecl_bitfield (d, e) -> SDecl_bitfield (Option.map declarator d, expression e)
  and static_assert (Static_assert (e, sl)) =
    Static_assert (expression e, string_literal sl)
  and alignment_specifier = function
    | AS_type tn -> AS_type (type_name tn)
    | AS_expr e -> AS_expr (expression e)
  and declarator (Declarator (pd, dd)) =
    Declarator (Option.map pointer_declarator pd, direct_declarator dd)
  and direct_declarator = function
    | DDecl_identifier (attrs, id) -> DDecl_identifier (attributes attrs, ident id)
    | DDecl_declarator d -> DDecl_declarator (declarator d)
    | DDecl_array (dd, ad) -> DDecl_array (direct_declarator dd, array_declarator ad)
    | DDecl_function (dd, ptl) -> DDecl_function (direct_declarator dd, parameter_type_list ptl)
  and array_declarator (ADecl (loc, tqs, b, ads)) =
    ADecl (el loc, tqs, b, Option.map array_declarator_size ads)
  and array_declarator_size = function
    | ADeclSize_expression e -> ADeclSize_expression (expression e)
    | ADeclSize_asterisk -> ADeclSize_asterisk
  and pointer_declarator (PDecl (loc, tqs, pd)) =
    PDecl (el loc, tqs, Option.map pointer_declarator pd)
  and parameter_type_list (Params (pds, b)) =
    Params (List.map parameter_declaration pds, b)
  and parameter_declaration = function
    | PDeclaration_decl (specs, d) -> PDeclaration_decl (specifiers specs, declarator d)
    | PDeclaration_abs_decl (specs, ad) ->
        PDeclaration_abs_decl (specifiers specs, Option.map abstract_declarator ad)
  and abstract_declarator = function
    | AbsDecl_pointer pd -> AbsDecl_pointer (pointer_declarator pd)
    | AbsDecl_direct (pd, dad) ->
        AbsDecl_direct (Option.map pointer_declarator pd, direct_abstract_declarator dad)
  and direct_abstract_declarator = function
    | DAbs_abs_declarator ad -> DAbs_abs_declarator (abstract_declarator ad)
    | DAbs_array (dad, ad) ->
        DAbs_array (Option.map direct_abstract_declarator dad, array_declarator ad)
    | DAbs_function (dad, ptl) ->
        DAbs_function (Option.map direct_abstract_declarator dad, parameter_type_list ptl)
  and specifiers (s : specifiers) =
    { s with
      type_specifiers = List.map type_specifier s.type_specifiers
    ; alignment_specifiers = List.map alignment_specifier s.alignment_specifiers }
  and statement (CabsStatement (loc, attrs, s_)) =
    CabsStatement (el loc, attributes attrs, statement_ s_)
  and statement_ = function
    | CabsSlabel (id, s) -> CabsSlabel (ident id, statement s)
    | CabsScase (e, s) -> CabsScase (expression e, statement s)
    | CabsSdefault s -> CabsSdefault (statement s)
    | CabsSblock ss -> CabsSblock (List.map statement ss)
    | CabsSdecl d -> CabsSdecl (declaration d)
    | CabsSnull -> CabsSnull
    | CabsSexpr e -> CabsSexpr (expression e)
    | CabsSif (e, s, s') -> CabsSif (expression e, statement s, Option.map statement s')
    | CabsSswitch (e, s) -> CabsSswitch (expression e, statement s)
    | CabsSwhile (e, s) -> CabsSwhile (expression e, statement s)
    | CabsSdo (e, s) -> CabsSdo (expression e, statement s)
    | CabsSfor (fc, e1, e2, s) ->
        CabsSfor (Option.map for_clause fc, Option.map expression e1,
                  Option.map expression e2, statement s)
    | CabsSgoto id -> CabsSgoto (ident id)
    | CabsScontinue -> CabsScontinue
    | CabsSbreak -> CabsSbreak
    | CabsSreturn e -> CabsSreturn (Option.map expression e)
    | CabsSpar ss -> CabsSpar (List.map statement ss)
    | CabsSasm (b1, b2, items) ->
        CabsSasm (b1, b2, List.map (fun (loc, strs) -> (el loc, strs)) items)
    | CabsScaseGNU (e1, e2, s) -> CabsScaseGNU (expression e1, expression e2, statement s)
    | CabsSmarker s -> CabsSmarker (statement s)
  and for_clause = function
    | FC_expr e -> FC_expr (expression e)
    | FC_decl (loc, d) -> FC_decl (el loc, declaration d)
  and declaration = function
    | Declaration_base (attrs, specs, ids) ->
        Declaration_base (attributes attrs, specifiers specs, List.map init_declarator ids)
    | Declaration_static_assert sad -> Declaration_static_assert (static_assert sad)
  and init_declarator (InitDecl (loc, d, init)) =
    InitDecl (el loc, declarator d, Option.map initializer_ init)
  in
  let function_definition (FunDef (loc, attrs, specs, decl, stmt)) =
    FunDef (el loc, attributes attrs, specifiers specs, declarator decl, statement stmt)
  in
  let external_declaration = function
    | EDecl_func fd -> EDecl_func (function_definition fd)
    | EDecl_decl d -> EDecl_decl (declaration d)
    | EDecl_magic (loc, s) -> EDecl_magic (el loc, s)
    (* CN external declarations carry locations from the magic-comment re-parse
       (already resolved); leave them untouched. *)
    | (EDecl_funcCN _ | EDecl_lemmaCN _ | EDecl_predCN _ | EDecl_datatypeCN _
      | EDecl_type_synCN _ | EDecl_fun_specCN _) as ed -> ed
  in
  let (TUnit eds) = tu in
  TUnit (List.map external_declaration eds)

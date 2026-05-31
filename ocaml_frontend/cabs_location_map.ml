(* Eager post-parse location resolution.

   Rewrite every source location in a Cabs translation unit by applying [f] to
   each Cerb_position.  The internal preprocessor produces a parse tree whose
   positions carry a synthetic [pos_bol] key into its raw-location map (see
   Cpp.Preprocessor); this turns them into resolved positions.  The external
   path passes [Fun.id], so this is a no-op there (and the driver skips it).

   Locations live not only on the obvious Cabs nodes but on every
   [Symbol.identifier] and inside [Annot.attributes], so all three are rewritten.
   CN subtrees (EDecl_*CN) are traversed only when [~traverse_cn:true].  Under the
   internal preprocessor a magic comment's CN payload is re-parsed from positions
   keyed into the *fragment's* own map, so it must be resolved against that map
   (which is when its macro-expansion chains are attached) — by the caller, right
   after the re-parse.  The outer translation-unit pass therefore *skips* CN
   (the default): those subtrees are already fully resolved, and re-applying the
   outer map would be wrong (a resolved real pos_bol can collide with an outer
   synthetic key).  Cabs constants carry no location and are left untouched.

   TODO(efficiency): this is a full structural traversal that rebuilds the tree.
   A lazy scheme that maps a position only when a location is printed — and/or a
   switch between eager and lazy — would avoid the rebuild.  Kept eager for now
   so existing library consumers (other backends) see resolved locations with no
   API change.  Also worth revisiting once the Menhir incremental API is in use.

   These types are generated from Lem specs and change rarely; this is a plain
   traversal over them, so the maintenance cost is low. *)

open Cabs

let from_raw ?(traverse_cn = false) f tu =
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
  (* CN subtrees.  The symbol parameter ['a] is [Symbol.identifier] and the type
     parameter ['ty] is [type_name], so they are rewritten with the [ident] and
     [type_name] functions already in scope.  A plain structural traversal over
     the (generated, rarely-changing) Cn types. *)
  let external_declaration =
    let open Cn in
    let rec cn_base_type = function
      | (CN_unit | CN_bool | CN_integer | CN_real | CN_loc | CN_alloc_id
        | CN_bits _) as t -> t
      | CN_struct a -> CN_struct (ident a)
      | CN_record fields ->
          CN_record (List.map (fun (i, bt) -> (ident i, cn_base_type bt)) fields)
      | CN_datatype a -> CN_datatype (ident a)
      | CN_map (bt1, bt2) -> CN_map (cn_base_type bt1, cn_base_type bt2)
      | CN_list bt -> CN_list (cn_base_type bt)
      | CN_tuple bts -> CN_tuple (List.map cn_base_type bts)
      | CN_set bt -> CN_set (cn_base_type bt)
      | CN_user_type_name a -> CN_user_type_name (ident a)
      | CN_c_typedef_name a -> CN_c_typedef_name (ident a)
    in
    (* A bound-argument list: rewrite the name and its base type. *)
    let cn_args xs =
      List.map (fun (a, bt) -> (ident a, cn_base_type bt)) xs in
    let rec cn_pat (CNPat (loc, p_)) = CNPat (el loc, cn_pat_ p_)
    and cn_pat_ = function
      | CNPat_sym a -> CNPat_sym (ident a)
      | CNPat_wild -> CNPat_wild
      | CNPat_constructor (a, fields) ->
          CNPat_constructor (ident a,
            List.map (fun (i, p) -> (ident i, cn_pat p)) fields)
    in
    let rec cn_expr (CNExpr (loc, e_)) = CNExpr (el loc, cn_expr_ e_)
    and cn_expr_ = function
      | CNExpr_const _ as e -> e
      | CNExpr_var a -> CNExpr_var (ident a)
      | CNExpr_list es -> CNExpr_list (List.map cn_expr es)
      | CNExpr_memberof (e, i) -> CNExpr_memberof (cn_expr e, ident i)
      | CNExpr_arrow (e, i) -> CNExpr_arrow (cn_expr e, ident i)
      | CNExpr_record fields ->
          CNExpr_record (List.map (fun (i, e) -> (ident i, cn_expr e)) fields)
      | CNExpr_struct (a, fields) ->
          CNExpr_struct (ident a,
            List.map (fun (i, e) -> (ident i, cn_expr e)) fields)
      | CNExpr_memberupdates (e, fields) ->
          CNExpr_memberupdates (cn_expr e,
            List.map (fun (i, e) -> (ident i, cn_expr e)) fields)
      | CNExpr_arrayindexupdates (e, upds) ->
          CNExpr_arrayindexupdates (cn_expr e,
            List.map (fun (e1, e2) -> (cn_expr e1, cn_expr e2)) upds)
      | CNExpr_binop (op, e1, e2) -> CNExpr_binop (op, cn_expr e1, cn_expr e2)
      | CNExpr_sizeof ty -> CNExpr_sizeof (type_name ty)
      | CNExpr_offsetof (a, i) -> CNExpr_offsetof (ident a, ident i)
      | CNExpr_membershift (e, ty_opt, i) ->
          CNExpr_membershift (cn_expr e, Option.map type_name ty_opt, ident i)
      | CNExpr_addr a -> CNExpr_addr (ident a)
      | CNExpr_cast (bt, e) -> CNExpr_cast (cn_base_type bt, cn_expr e)
      | CNExpr_array_shift (e1, ty_opt, e2) ->
          CNExpr_array_shift (cn_expr e1, Option.map type_name ty_opt, cn_expr e2)
      | CNExpr_call (a, es) -> CNExpr_call (ident a, List.map cn_expr es)
      | CNExpr_cons (a, fields) ->
          CNExpr_cons (ident a,
            List.map (fun (i, e) -> (ident i, cn_expr e)) fields)
      | CNExpr_each (a, bt, range, e) ->
          CNExpr_each (ident a, cn_base_type bt, range, cn_expr e)
      | CNExpr_let (a, e1, e2) -> CNExpr_let (ident a, cn_expr e1, cn_expr e2)
      | CNExpr_match (e, cases) ->
          CNExpr_match (cn_expr e,
            List.map (fun (p, e) -> (cn_pat p, cn_expr e)) cases)
      | CNExpr_ite (e1, e2, e3) -> CNExpr_ite (cn_expr e1, cn_expr e2, cn_expr e3)
      | CNExpr_good (ty, e) -> CNExpr_good (type_name ty, cn_expr e)
      | CNExpr_deref e -> CNExpr_deref (cn_expr e)
      | CNExpr_value_of_c_atom (a, k) -> CNExpr_value_of_c_atom (ident a, k)
      | CNExpr_unchanged e -> CNExpr_unchanged (cn_expr e)
      | CNExpr_at_env (e, s) -> CNExpr_at_env (cn_expr e, s)
      | CNExpr_not e -> CNExpr_not (cn_expr e)
      | CNExpr_negate e -> CNExpr_negate (cn_expr e)
      | CNExpr_default bt -> CNExpr_default (cn_base_type bt)
      | CNExpr_bnot e -> CNExpr_bnot (cn_expr e)
    in
    let cn_pred = function
      | CN_owned ty_opt -> CN_owned (Option.map type_name ty_opt)
      | CN_block ty_opt -> CN_block (Option.map type_name ty_opt)
      | CN_named a -> CN_named (ident a)
    in
    let cn_resource = function
      | CN_pred (loc, p, es) -> CN_pred (el loc, cn_pred p, List.map cn_expr es)
      | CN_each (a, bt, e, loc, p, es) ->
          CN_each (ident a, cn_base_type bt, cn_expr e, el loc, cn_pred p,
                   List.map cn_expr es)
    in
    let cn_assertion = function
      | CN_assert_exp e -> CN_assert_exp (cn_expr e)
      | CN_assert_qexp (a, bt, e1, e2) ->
          CN_assert_qexp (ident a, cn_base_type bt, cn_expr e1, cn_expr e2)
    in
    let rec cn_clause = function
      | CN_letResource (loc, a, r, c) ->
          CN_letResource (el loc, ident a, cn_resource r, cn_clause c)
      | CN_letExpr (loc, a, e, c) ->
          CN_letExpr (el loc, ident a, cn_expr e, cn_clause c)
      | CN_assert (loc, asrt, c) ->
          CN_assert (el loc, cn_assertion asrt, cn_clause c)
      | CN_return (loc, e) -> CN_return (el loc, cn_expr e)
    in
    let rec cn_clauses = function
      | CN_clause (loc, c) -> CN_clause (el loc, cn_clause c)
      | CN_if (loc, e, c, cs) ->
          CN_if (el loc, cn_expr e, cn_clause c, cn_clauses cs)
    in
    let cn_condition = function
      | CN_cletResource (loc, a, r) -> CN_cletResource (el loc, ident a, cn_resource r)
      | CN_cletExpr (loc, a, e) -> CN_cletExpr (el loc, ident a, cn_expr e)
      | CN_cconstr (loc, asrt) -> CN_cconstr (el loc, cn_assertion asrt)
    in
    let cn_function f =
      { cn_func_magic_loc = el f.cn_func_magic_loc
      ; cn_func_loc = el f.cn_func_loc
      ; cn_func_name = ident f.cn_func_name
      ; cn_func_attrs = List.map ident f.cn_func_attrs
      ; cn_func_args = cn_args f.cn_func_args
      ; cn_func_body = Option.map cn_expr f.cn_func_body
      ; cn_func_return_bty = cn_base_type f.cn_func_return_bty }
    in
    let cn_lemma l =
      { cn_lemma_magic_loc = el l.cn_lemma_magic_loc
      ; cn_lemma_loc = el l.cn_lemma_loc
      ; cn_lemma_name = ident l.cn_lemma_name
      ; cn_lemma_args = cn_args l.cn_lemma_args
      ; cn_lemma_requires = List.map cn_condition l.cn_lemma_requires
      ; cn_lemma_ensures = List.map cn_condition l.cn_lemma_ensures }
    in
    let cn_predicate p =
      { cn_pred_magic_loc = el p.cn_pred_magic_loc
      ; cn_pred_loc = el p.cn_pred_loc
      ; cn_pred_name = ident p.cn_pred_name
      ; cn_pred_attrs = List.map ident p.cn_pred_attrs
      ; cn_pred_output =
          (let (loc, bt) = p.cn_pred_output in (el loc, cn_base_type bt))
      ; cn_pred_iargs = cn_args p.cn_pred_iargs
      ; cn_pred_clauses = Option.map cn_clauses p.cn_pred_clauses }
    in
    let cn_datatype d =
      { cn_dt_magic_loc = el d.cn_dt_magic_loc
      ; cn_dt_loc = el d.cn_dt_loc
      ; cn_dt_name = ident d.cn_dt_name
      ; cn_dt_cases =
          List.map
            (fun (a, fields) ->
               (ident a, List.map (fun (i, bt) -> (ident i, cn_base_type bt)) fields))
            d.cn_dt_cases }
    in
    let cn_type_synonym t =
      { cn_tysyn_magic_loc = el t.cn_tysyn_magic_loc
      ; cn_tysyn_loc = el t.cn_tysyn_loc
      ; cn_tysyn_name = ident t.cn_tysyn_name
      ; cn_tysyn_rhs = cn_base_type t.cn_tysyn_rhs }
    in
    let cn_acc_func = function
      | CN_accesses ids -> CN_accesses (List.map ident ids)
      | CN_mk_function a -> CN_mk_function (ident a)
    in
    let cn_func_spec s =
      { cn_func_trusted = Option.map el s.cn_func_trusted
      ; cn_func_acc_func =
          Option.map (fun (loc, af) -> (el loc, cn_acc_func af)) s.cn_func_acc_func
      ; cn_func_requires =
          Option.map
            (fun (loc, (args, conds)) ->
               (el loc, (cn_args args, List.map cn_condition conds)))
            s.cn_func_requires
      ; cn_func_ensures =
          Option.map
            (fun (loc, (args, conds)) ->
               (el loc, (cn_args args, List.map cn_condition conds)))
            s.cn_func_ensures }
    in
    let cn_decl_spec s =
      { cn_decl_loc = el s.cn_decl_loc
      ; cn_decl_name = ident s.cn_decl_name
      ; cn_decl_args = cn_args s.cn_decl_args
      ; cn_func_spec = cn_func_spec s.cn_func_spec }
    in
    function
    | EDecl_func fd -> EDecl_func (function_definition fd)
    | EDecl_decl d -> EDecl_decl (declaration d)
    | EDecl_magic (loc, s) -> EDecl_magic (el loc, s)
    (* Skip already-resolved CN subtrees unless explicitly asked (the fragment
       resolution pass). *)
    | (EDecl_funcCN _ | EDecl_lemmaCN _ | EDecl_predCN _ | EDecl_datatypeCN _
      | EDecl_type_synCN _ | EDecl_fun_specCN _) as ed when not traverse_cn -> ed
    | EDecl_funcCN f -> EDecl_funcCN (cn_function f)
    | EDecl_lemmaCN l -> EDecl_lemmaCN (cn_lemma l)
    | EDecl_predCN p -> EDecl_predCN (cn_predicate p)
    | EDecl_datatypeCN d -> EDecl_datatypeCN (cn_datatype d)
    | EDecl_type_synCN t -> EDecl_type_synCN (cn_type_synonym t)
    | EDecl_fun_specCN s -> EDecl_fun_specCN (cn_decl_spec s)
  in
  let (TUnit eds) = tu in
  TUnit (List.map external_declaration eds)

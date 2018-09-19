open HolKernel boolLib boolSimps bossLib lcsymtacs holSyntaxTheory holSyntaxExtraTheory setSpecTheory

val _ = new_theory"holSemantics"

val mem = ``mem:'U->'U->bool``

fun type_rec_tac proj =
(WF_REL_TAC(`measure (type_size o `@[QUOTE proj]@`)`) >> simp[] >>
 gen_tac >> Induct >> simp[DB.fetch"holSyntax""type_size_def"] >> rw[] >>
 simp[] >> res_tac >> simp[])

val _ = Parse.overload_on("inhabited",``λs. ∃x. x <: s``)

val (builtin_closure_rules,builtin_closure_ind,builtin_closure_cases) = Hol_reln `
  (!T ty. T ty ==> builtin_closure T ty)
  /\ (!T. builtin_closure T Bool)
  /\ (!T ty1 ty2. builtin_closure T ty1 /\ builtin_closure T ty2
        ==> builtin_closure T (Fun ty1 ty2))`

val [builtin_closure_inj,builtin_closure_bool,builtin_closure_fun] =
    map2 (curry save_thm)
         ["builtin_closure_inj","builtin_closure_bool","builtin_closure_fun"]
         (CONJUNCTS builtin_closure_rules);

(* TODO: change definition in holSyntaxScript *)
val is_builtin_type_def = Q.prove(
  `(∀v0. is_builtin_type (Tyvar v0) ⇔ F) ∧
     ∀m ty. is_builtin_type (Tyapp m ty) ⇔
        ((m = strlit "fun" /\ LENGTH ty = 2) \/
         (m = strlit "bool" /\ LENGTH ty = 0))`,
  cheat);

val ground_types_def = Define `
  ground_types (sig:sig) =
  {ty | tyvars ty = [] /\ type_ok (tysof sig) ty}
  `

val ground_consts_def = Define `
  ground_consts sig =
  {(n,ty) | ty ∈ ground_types sig /\ term_ok sig (Const n ty)}
  `

val nonbuiltin_types_def = Define `nonbuiltin_types = {ty | ¬is_builtin_type ty}`

val builtin_consts =
  Define `builtin_consts = {(s,ty) | s = strlit "=" /\ ?ty'. ty = Fun ty' (Fun ty' Bool)}`

val nonbuiltin_constinsts_def =
  Define `nonbuiltin_constinsts = {c | c ∉ builtin_consts}`

val consts_of_term_def = Define
  `(consts_of_term(Abs x y) = consts_of_term x ∪ consts_of_term y) /\
   (consts_of_term(Comb x y) = consts_of_term x ∪ consts_of_term y) /\
   (consts_of_term(Const n ty) = {(n,ty)}) /\
   (consts_of_term _ = {})`

val is_sig_fragment_def = Define
  `is_sig_fragment sig (tys,consts) =
   (tys ⊆ ground_types sig ∧ tys ⊆ nonbuiltin_types
    ∧ consts ⊆ ground_consts sig ∧ consts ⊆ nonbuiltin_constinsts
    ∧ (!s c. (s,c) ∈ consts ==> c ∈ builtin_closure tys)
   )
  `

val terms_of_frag_def = Define
  `terms_of_frag (tys,consts) =
   {t | consts_of_term t ∩ nonbuiltin_constinsts ⊆ consts
        /\ set(allTypes t) ⊆ tys /\ welltyped t}
  `

val ground_terms_def = Define
  `ground_terms sig = {t | ?ty. t has_type ty /\ ty ∈ ground_types sig}`

val types_of_frag_def = Define
  `types_of_frag (tys,consts) = builtin_closure tys`

(* Lemma 8 from Andrei&Ondra, should go elsewhere*)

val builtin_closure_idem = Q.store_thm("builtin_closure_idem",
  `!tyfrag. builtin_closure (builtin_closure tyfrag) = builtin_closure tyfrag`,
  rw[FUN_EQ_THM]
  >> W (curry Q.SPEC_TAC) `x`
  >> ho_match_mp_tac type_ind
  >> rpt strip_tac
  >- simp[Once builtin_closure_cases]
  >> simp[Once builtin_closure_cases]
  >> rw[EQ_IMP_THM]
  >> rfs[]
  >> simp[Once builtin_closure_cases]);

val allTypes_no_tyvars_and_ok = Q.prove(
  `!ty. (∀x. x ∈ q ⇒ tyvars x = [] /\ type_ok (tysof sig) x)
        /\ (∀x. MEM x (allTypes' ty) ⇒ x ∈ q)
        /\ is_std_sig sig
        ==> tyvars ty = [] /\ type_ok (tysof sig) ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >> fs[allTypes'_def]
  >- (BasicProvers.PURE_FULL_CASE_TAC >- fs[tyvars_def]
      >> qpat_x_assum `!x. _` mp_tac >> simp[] >> strip_tac
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- (Cases_on `l` >- fs[tyvars_def]
          >> rename1 `ty::tys` >> Cases_on `tys` >> fs[]
          >> qmatch_goalsub_abbrev_tac `a1 = a2`
          >> `set a1 = set a2` suffices_by(unabbrev_all_tac >> simp[])
          >> unabbrev_all_tac
          >> simp[tyvars_def])
      >> fs[])
  \\ BasicProvers.PURE_FULL_CASE_TAC >- fs[type_ok_def,is_std_sig_def]
  \\ qpat_x_assum `!x. _` mp_tac >> simp[] >> strip_tac
  >> BasicProvers.PURE_FULL_CASE_TAC
  >- (fs[quantHeuristicsTheory.LIST_LENGTH_2,is_std_sig_def,type_ok_def]
      \\ fs[])
  \\ fs[type_ok_def]);

val allTypes_no_tyvars2 = Q.prove(
  `!tm ty1 ty2. tm has_type ty1 /\
           MEM ty2 (allTypes' ty1)
           ==> MEM ty2 (allTypes tm)`,
  simp[GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac has_type_strongind
  >> rw[allTypes_def,allTypes'_def] >> fs[]);

val builtin_closure_tyvars = Q.prove(
  `∀q x. x ∈ builtin_closure q /\ (∀x. x ∈ q ⇒ tyvars x = []) ==> tyvars x = []`,
  simp [IN_DEF,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac builtin_closure_ind
  >> rw[tyvars_def]);

val builtin_closure_type_ok = Q.prove(
  `∀q x. x ∈ builtin_closure q /\ (∀x. x ∈ q ⇒ type_ok (tysof sig) x)
   /\ is_std_sig sig
   ==> type_ok (tysof sig) x`,
  simp [IN_DEF,GSYM AND_IMP_INTRO]
  >> ho_match_mp_tac builtin_closure_ind
  >> rw[is_std_sig_def,type_ok_def]);

val builtin_closure_allTypes' = Q.prove(
  `!ty q. (∀x. MEM x (allTypes' ty) ⇒ x ∈ q) ==> ty ∈ builtin_closure q`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[allTypes'_def,boolTheory.IN_DEF] >> metis_tac[builtin_closure_rules])
  >- (fs[allTypes'_def,listTheory.EVERY_MEM]
      >> BasicProvers.PURE_FULL_CASE_TAC
      >- fs[builtin_closure_rules,boolTheory.IN_DEF]
      >> qpat_x_assum `!x. _` mp_tac >> simp[]
      >> BasicProvers.PURE_FULL_CASE_TAC >> simp[builtin_closure_rules,boolTheory.IN_DEF]
      >> Cases_on `l` >- fs[tyvars_def]
      >> rename1 `ty::tys` >> Cases_on `tys` >> fs[] >> rpt strip_tac
      >> metis_tac[builtin_closure_rules,boolTheory.IN_DEF]));

val allTypes'_builtin_closure = Q.prove(
  `!q ty x. ty ∈ builtin_closure q /\ q ⊆ nonbuiltin_types /\ MEM x (allTypes' ty) ⇒ x ∈ q`,
  simp[boolTheory.IN_DEF,GSYM AND_IMP_INTRO,GSYM PULL_FORALL]
  >> ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >- (fs[nonbuiltin_types_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> first_x_assum drule >> strip_tac >> Cases_on `ty`
      >> fs[is_builtin_type_def,is_builtin_name_def]
      >> fs[allTypes'_def])
  >- fs[allTypes'_def]
  >- (fs[allTypes'_def,boolTheory.IN_DEF] >> rpt(first_x_assum drule >> strip_tac)));

val consts_of_free_const = Q.prove(
  `!tm x v. x ∈ consts_of_term v /\ VFREE_IN v tm
            ==> v = Const (FST x) (SND x)`,
  Induct >> rpt strip_tac
  >> fs[consts_of_term_def,VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[consts_of_term_def]);

val VFREEs_IN_consts = Q.prove(
  `!tm s ty. VFREE_IN (Const s ty) tm
            ==> (s,ty) ∈ consts_of_term tm`,
  Induct >> rpt strip_tac
  >> fs[consts_of_term_def,VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[consts_of_term_def]);

val var_type_in_types = Q.prove(
  `!tm ty v. VFREE_IN v tm /\ MEM ty (allTypes v)
            ==> MEM ty (allTypes tm)`,
  Induct >> rpt strip_tac
  >> fs[VFREE_IN_def,allTypes_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[allTypes_def]
  >> rpt(qpat_x_assum `!x. _` imp_res_tac) >> fs[]);

val VFREE_type = Q.prove(
  `!tm v. VFREE_IN v tm ==> v has_type typeof v`,
  Induct >> rpt strip_tac
  >> fs[VFREE_IN_def]
  >> rpt(BasicProvers.VAR_EQ_TAC)
  >> fs[typeof_def,has_type_rules]);

val RTC_lifts_invariants_inv = Q.prove(
  `(∀x y. P x ∧ R y x ⇒ P y) ⇒ ∀x y. P x ∧ R^* y x ⇒ P y`,
  rpt strip_tac
  >> Q.ISPECL_THEN [`inv R`,`P`] assume_tac (GEN_ALL relationTheory.RTC_lifts_invariants)
  >> fs[relationTheory.inv_DEF,relationTheory.inv_MOVES_OUT]
  >> metis_tac[])

val terms_of_frag_combE = Q.store_thm("terms_of_frag_combE",
  `!f a b sig. is_sig_fragment sig f /\ Comb a b ∈ terms_of_frag f ==> 
   a ∈ terms_of_frag f /\ b ∈ terms_of_frag f`,
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[]);

val terms_of_frag_AbsE = Q.store_thm("terms_of_frag_combE",
  `!f a b sig. is_sig_fragment sig f /\ Abs a b ∈ terms_of_frag f ==> 
   a ∈ terms_of_frag f /\ b ∈ terms_of_frag f`,
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
  >> fs[] >> metis_tac[has_type_rules]);

val terms_of_frag_combI = Q.store_thm("terms_of_frag_combI",
  `!f a b sig. is_sig_fragment sig f /\ a ∈ terms_of_frag f /\ b ∈ terms_of_frag f
           /\ welltyped(Comb a b)==> 
   Comb a b ∈ terms_of_frag f`,
  Cases
  >> rw[terms_of_frag_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,welltyped_def,
        consts_of_term_def,allTypes_def]
  >> rpt(first_x_assum drule >> strip_tac)
  >> imp_res_tac WELLTYPED_LEMMA
  >> metis_tac[has_type_rules]);

(* TODO: unify these two lemmas *)
val consts_of_term_REV_ASSOCD = Q.prove(
  `!x t ilist d. x ∈ consts_of_term (REV_ASSOCD t ilist d)
   ==> x ∈ consts_of_term d \/ EXISTS ($IN x) (MAP (consts_of_term o FST) ilist)`,
  Induct_on `ilist`
  >> rw[holSyntaxLibTheory.REV_ASSOCD_def]
  >> metis_tac[]);

val allTypes_REV_ASSOCD = Q.prove(
  `!x t ilist d. MEM x (allTypes (REV_ASSOCD t ilist d))
   ==> MEM x (allTypes d) \/ EXISTS ($MEM x) (MAP (allTypes o FST) ilist)`,
  Induct_on `ilist`
  >> rw[holSyntaxLibTheory.REV_ASSOCD_def]
  >> metis_tac[]);

val consts_of_term_VSUBST = Q.prove(
  `!x n ty tm1 ilist. x ∈ consts_of_term (VSUBST ilist tm1)
   ==> x ∈ consts_of_term tm1 \/ EXISTS ($IN x) (MAP (consts_of_term o FST) ilist)`,
  Induct_on `tm1`
  >> rw[VSUBST_def]
  >- (imp_res_tac consts_of_term_REV_ASSOCD >> simp[])
  >- (fs[consts_of_term_def] >> first_x_assum drule >> strip_tac >> fs[])
  >- (fs[consts_of_term_def,pairTheory.ELIM_UNCURRY,VSUBST_def]
      >> first_x_assum drule
      >> strip_tac >> fs[consts_of_term_def]
      >> disj2_tac
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[])
  >- (fs[consts_of_term_def]
      >> first_x_assum drule
      >> strip_tac >> fs[consts_of_term_def]
      >> disj2_tac
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[]));

val allTypes_VSUBST = Q.prove(
  `!x tm1 ilist. MEM x (allTypes (VSUBST ilist tm1))
                      /\ welltyped tm1
                      ==> MEM x (allTypes tm1) \/ EXISTS ($MEM x) (MAP (allTypes o FST) ilist)`,
  Induct_on `tm1`
  >> rw[VSUBST_def]
  >- (imp_res_tac allTypes_REV_ASSOCD >> simp[])
  >- (fs[allTypes_def] >> first_x_assum drule >> strip_tac >> fs[])
  >- (fs[allTypes_def]
      >> first_x_assum drule >> strip_tac >> fs[allTypes_def]
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[])
  >- (fs[allTypes_def]
      >> first_x_assum drule >> strip_tac >> fs[allTypes_def]
      >> fs[listTheory.EXISTS_MEM,listTheory.MEM_MAP,listTheory.MEM_FILTER]
      >> metis_tac[]));

(* 8(1) *)
val types_of_frag_ground = Q.store_thm("types_of_frag_ground",
  `!f sig. is_sig_fragment sig f /\ is_std_sig sig ==> types_of_frag f ⊆ ground_types sig`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def]
  >- metis_tac[builtin_closure_tyvars]
  >- metis_tac[builtin_closure_type_ok]);

(* 8(2) *)
val terms_of_frag_ground = Q.store_thm("terms_of_frag_ground",
  `!f. is_sig_fragment sig f /\ is_std_sig sig ==> terms_of_frag f ⊆ ground_terms sig`,
  Cases
  >> rw[terms_of_frag_def,ground_terms_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        ground_types_def,welltyped_def]
  >> qexists_tac `ty` >> simp[]
  >> qpat_x_assum `_ has_type _` (fn thm => rpt(pop_assum mp_tac) >> mp_tac thm)
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`ty`,`x`] (* TODO: generated names *)
  >> ho_match_mp_tac has_type_strongind
  >> rpt conj_tac >> rpt gen_tac >> rpt(disch_then strip_assume_tac)
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars_and_ok
      >> fs[])
  >- (fs[allTypes_def] >> match_mp_tac allTypes_no_tyvars_and_ok
      >> fs[])
  >- (match_mp_tac allTypes_no_tyvars_and_ok >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules])
  >- (match_mp_tac allTypes_no_tyvars_and_ok >> fs[] >> rw[]
      >> first_x_assum match_mp_tac
      >> match_mp_tac allTypes_no_tyvars2
      >> metis_tac[has_type_rules]));

(* 8(3) *)
val term_frag_in_type_frag = Q.store_thm("term_frag_in_type_frag",
  `!f tm ty sig. is_sig_fragment sig f /\ tm ∈ terms_of_frag f ==>
          typeof tm ∈ types_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >> metis_tac[WELLTYPED_LEMMA,allTypes_no_tyvars2,builtin_closure_allTypes']);

(* 8(4) *)
val term_vars_in_term_frag = Q.store_thm("term_vars_in_term_frag",
  `!f tm v sig. is_sig_fragment sig f /\ tm ∈ terms_of_frag f /\ VFREE_IN v tm ==>
          v ∈ terms_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def]
  >- (imp_res_tac consts_of_free_const >> fs[consts_of_term_def]
      >> first_x_assum match_mp_tac >> imp_res_tac VFREEs_IN_consts >> fs[])
  >- (imp_res_tac var_type_in_types >> rpt(qpat_x_assum `!x. _` imp_res_tac))
  >- (imp_res_tac VFREE_type >> metis_tac[]));

(* 8(5) *)
val subterm1_in_term_frag = Q.store_thm("subterm1_in_term_frag",
  `!f tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ subterm1 tm2 tm1 ==>
          tm2 ∈ terms_of_frag f`,
  Cases
  >> rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
        welltyped_def,terms_of_frag_def,Once subterm1_cases]
  >> fs[consts_of_term_def,allTypes_def]
  >> (imp_res_tac WELLTYPED_LEMMA >> rpt(BasicProvers.VAR_EQ_TAC)
      >> qhdtm_x_assum `$has_type` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> metis_tac[has_type_rules]));

val subterm_in_term_frag = Q.store_thm("subterm_in_term_frag",
  `!f tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
          tm2 ∈ terms_of_frag f`,
  `!f sig. is_sig_fragment sig f ==> !tm1 tm2. tm1 ∈ terms_of_frag f /\ tm2 subterm tm1 ==>
       tm2 ∈ terms_of_frag f` suffices_by metis_tac[]
  >> ntac 3 strip_tac
  >> ho_match_mp_tac RTC_lifts_invariants_inv
  >> rpt strip_tac >> imp_res_tac subterm1_in_term_frag);

(* 8(6) *)
val term_frag_subst_clos = Q.store_thm("subterm_in_term_frag",
  `!f n ty tm1 tm2 sig. is_sig_fragment sig f /\ tm1 ∈ terms_of_frag f /\ tm2 ∈ terms_of_frag f
                    /\ ty ∈ types_of_frag f
                    /\ tm2 has_type ty ==>
          VSUBST [(tm2, Var n ty)] tm1 ∈ terms_of_frag f`,
  Cases >> Induct_on `tm1`
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def])
  >- (rw[VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def])
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def]
      >> imp_res_tac consts_of_term_VSUBST
      >> fs[consts_of_term_def]
      >> TRY(qmatch_goalsub_abbrev_tac `_ IN _`
             >> drule allTypes_VSUBST >> simp[GSYM PULL_EXISTS]
             >> impl_tac
             >- (fs[Once has_type_cases] >> fs[welltyped_def] >> metis_tac[])
             >> strip_tac >> fs[])
      >> rename1 `Comb _ _ has_type cty`
      >> qexists_tac `cty`
      >> qpat_x_assum `Comb _ _ has_type _` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[]
      >> MAP_FIRST match_mp_tac (CONJUNCTS has_type_rules)
      >> qexists_tac `dty`
      >> conj_tac >> match_mp_tac VSUBST_HAS_TYPE
      >> fs[])
  >- (rw[types_of_frag_def,ground_types_def,pred_setTheory.SUBSET_DEF,is_sig_fragment_def,
         welltyped_def,terms_of_frag_def,VSUBST_def,holSyntaxLibTheory.REV_ASSOCD_def,consts_of_term_def,allTypes_def]
      >> qpat_x_assum `Abs _ _ has_type _` (assume_tac o PURE_ONCE_REWRITE_RULE [has_type_cases])
      >> fs[] >> rpt(BasicProvers.VAR_EQ_TAC) >> fs[dest_var_def,consts_of_term_def]
      >> imp_res_tac consts_of_term_VSUBST >> fs[consts_of_term_def,allTypes_def]
      >> TRY(qmatch_goalsub_abbrev_tac `_ IN _`
             >> drule allTypes_VSUBST >> simp[GSYM PULL_EXISTS]
             >> impl_tac
             >- (fs[welltyped_def] >> metis_tac[])
             >> strip_tac >> fs[allTypes_def])
      >> qexists_tac `Fun dty rty`
      >> MAP_FIRST match_mp_tac (CONJUNCTS has_type_rules)
      >> match_mp_tac VSUBST_HAS_TYPE
      >> rw[] >> MAP_FIRST MATCH_ACCEPT_TAC (CONJUNCTS has_type_rules)));

val is_type_frag_interpretation_def = xDefine "is_type_frag_interpretation"`
  is_type_frag_interpretation0 ^mem (tyfrag: type -> bool) (δ: type -> 'U) ⇔
    (∀ty. ty ∈ tyfrag ⇒ inhabited(δ ty))`

val _ = Parse.overload_on("is_type_frag_interpretation",``is_type_frag_interpretation0 ^mem``)

(* Todo: grotesque patterns *)
val ext_type_frag_builtins_def = xDefine "ext_type_frag_builtins"`
  ext_type_frag_builtins0 ^mem (δ: type -> 'U) ty ⇔
  case ty of Bool => boolset
    |  Fun dom rng => Funspace (ext_type_frag_builtins0 ^mem δ dom)
                               (ext_type_frag_builtins0 ^mem δ rng)
    | _ => δ ty`

val _ = Parse.overload_on("ext_type_frag_builtins",``ext_type_frag_builtins0 ^mem``)

val is_type_frag_interpretation_ext = Q.store_thm("is_type_frag_interpretation_ext",
  `!tyfrag tmfrag δ sig. is_sig_fragment sig (tyfrag,tmfrag) /\ is_set_theory ^mem /\ is_type_frag_interpretation tyfrag δ ==>
   is_type_frag_interpretation (builtin_closure tyfrag) (ext_type_frag_builtins δ)`,
  rw[] >> rw[is_type_frag_interpretation_def]
  >> qhdtm_x_assum `is_type_frag_interpretation0` mp_tac
  >> qhdtm_x_assum `is_sig_fragment` mp_tac    
  >> pop_assum mp_tac
  >> simp[boolTheory.IN_DEF]
  >> MAP_EVERY (W(curry Q.SPEC_TAC)) [`ty`,`tyfrag`]
  >> ho_match_mp_tac builtin_closure_ind >> rpt strip_tac
  >- (fs[is_type_frag_interpretation_def,Once ext_type_frag_builtins_def,boolTheory.IN_DEF,
         is_sig_fragment_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> fs[nonbuiltin_types_def,is_builtin_type_def,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]
      >> rpt(first_x_assum drule) >> fs[is_builtin_type_def,is_builtin_name_def])
  >- (fs[is_type_frag_interpretation_def,Once ext_type_frag_builtins_def,boolTheory.IN_DEF,
         is_sig_fragment_def]
      >> metis_tac[boolean_in_boolset])
  >- (rpt(first_x_assum drule >> disch_then drule >> strip_tac)
      >> drule funspace_inhabited
      >> rename1 `Fun dty rty`
      >> disch_then(qspecl_then [`ext_type_frag_builtins δ dty`,
                                 `ext_type_frag_builtins δ rty`] mp_tac)
      >> impl_tac >- metis_tac[]
      >> disch_then assume_tac >> simp[Once ext_type_frag_builtins_def]));

val is_frag_interpretation_def = xDefine "is_frag_interpretation"`
  is_frag_interpretation0 ^mem (tyfrag,tmfrag)
                               (δ: type -> 'U) (γ: mlstring # type -> 'U) ⇔
  (is_type_frag_interpretation tyfrag δ /\
   ∀(c,ty). (c,ty) ∈ tmfrag ⇒ γ(c,ty) ⋲ ext_type_frag_builtins δ ty)
  `

val _ = Parse.overload_on("is_frag_interpretation",``is_frag_interpretation0 ^mem``)

(* TODO: grotesque patterns *)
val ext_term_frag_builtins_def = xDefine "ext_term_frag_builtins"`
  ext_term_frag_builtins0 ^mem (δ: type -> 'U) (γ: mlstring # type -> 'U) tm =
  if ?ty. tm = (strlit "=",Fun ty (Fun ty Bool)) then
    case tm of (_, Fun ty _) =>
      Abstract (δ ty) (Funspace (δ ty) boolset)
        (λx. Abstract (δ ty) boolset (λy. Boolean (x = y)))
    | _ => γ tm
  else γ tm
  `

val _ = Parse.overload_on("ext_term_frag_builtins",``ext_term_frag_builtins0 ^mem``)

val builtin_terms_def = Define
  `builtin_terms tyfrag = builtin_consts ∩ {const | SND const ∈ tyfrag}`

val ext_type_frag_idem = Q.store_thm("ext_type_frag_idem",
  `!ty δ.
    (ext_type_frag_builtins (ext_type_frag_builtins δ) ty)
     = ext_type_frag_builtins δ ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (rw[Once ext_type_frag_builtins_def])
  >> rw[Once ext_type_frag_builtins_def]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]);

val ext_type_frag_mono_eq = Q.store_thm("ext_type_frag_mono_eq",
  `!ty δ1 δ2.
    (!ty'. MEM ty' (allTypes' ty) ==> δ1 ty' = δ2 ty')
    ==> ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (fs[ext_type_frag_builtins_def,allTypes'_def])
  >> rw[Once ext_type_frag_builtins_def]
  >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[allTypes'_def])
  >> CONV_TAC(RHS_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
  >> simp[]
  >> qmatch_goalsub_abbrev_tac `Funspace a1 a2 = Funspace a3 a4`
  >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
  >> unabbrev_all_tac >> conj_tac >> first_x_assum match_mp_tac
  >> metis_tac[]);

val is_frag_interpretation_ext = Q.store_thm("is_frag_interpretation_ext",
  `!tyfrag tmfrag sig δ γ. is_sig_fragment sig (tyfrag,tmfrag) /\ is_set_theory ^mem
           /\ is_frag_interpretation (tyfrag,tmfrag) δ γ==>
   is_frag_interpretation (builtin_closure tyfrag,
                           tmfrag ∪ builtin_terms(builtin_closure tyfrag))
                          (ext_type_frag_builtins δ)
                          (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)`,
  rw[is_frag_interpretation_def]
  >- (match_mp_tac is_type_frag_interpretation_ext >> metis_tac[])
  >> fs[pairTheory.ELIM_UNCURRY,is_sig_fragment_def] >> rw[]
  >> Cases_on `x` (* TODO: generated name *)
  >> rw[ext_term_frag_builtins_def] >> fs[]
  >- (fs[nonbuiltin_constinsts_def,builtin_consts,pred_setTheory.SUBSET_DEF]
      >> rpt(first_x_assum drule) >> simp[])
  >- (first_x_assum drule >> fs[]
      >> CONV_TAC(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> disch_then(mp_tac o PURE_ONCE_REWRITE_RULE [ext_type_frag_builtins_def])
      >> fs[ext_type_frag_idem])
  >- (simp[ext_type_frag_idem]
      >> CONV_TAC(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))
      >> CONV_TAC(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def])))
      >> CONV_TAC(RAND_CONV(RAND_CONV(RAND_CONV(SIMP_CONV (srw_ss()) [Once ext_type_frag_builtins_def]))))
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[]
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[] >> metis_tac[boolean_in_boolset])
  >- (rfs[builtin_terms_def,builtin_consts] >> metis_tac[]));

val _ = Parse.type_abbrev("valuation",``:mlstring # type -> 'U``)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (δ: type -> 'U) (γ: mlstring # type -> 'U) (v:'U valuation) (Var x ty)
   = v (x,ty)) ∧
  (termsem0 ^mem δ γ v (Const name ty) = γ(name,ty)) ∧
  (termsem0 ^mem δ γ v (Comb t1 t2) =
   termsem0 ^mem δ γ v t1 ' (termsem0 ^mem δ γ v t2)) ∧
  (termsem0 ^mem δ γ v (Abs (Var x ty) b) =
   Abstract (δ ty) (δ (typeof b))
     (λm. termsem0 ^mem δ γ (((x,ty)=+m)v) b))`

val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ: type -> 'U) ⇔
    (∀dom rng. δ(Fun dom rng) = Funspace (δ dom) (δ rng)) ∧
    (δ(Bool) = boolset)`
val _ = Parse.overload_on("is_std_type_assignment",``is_std_type_assignment0 ^mem``)

val ext_std_type_assignment = Q.store_thm("ext_std_type_assignment",
  `!ty δ. is_std_type_assignment δ ==> ext_type_frag_builtins δ ty = δ ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- fs[ext_type_frag_builtins_def]
  >- (simp[Once ext_type_frag_builtins_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >> fs[is_std_type_assignment_def]));

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem tyfrag δ γ ⇔
    is_std_type_assignment δ ∧
    builtin_closure tyfrag = tyfrag ∧
    !ty. ty ∈ tyfrag ==> γ(strlit "=", Fun ty (Fun ty Bool)) = Abstract (δ ty) (Funspace (δ ty) boolset)
          (λx. Abstract (δ ty) boolset (λy. Boolean (x = y)))`

val _ = Parse.overload_on("is_std_interpretation",``is_std_interpretation0 ^mem``);
                                         
val termsem_in_type = Q.store_thm("termsem_in_type",
  `!tyfrag tmfrag δ γ v tm.
  is_set_theory ^mem /\
  is_std_interpretation tyfrag δ γ /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag (tyfrag,tmfrag) /\
  (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ δ ty)
  ==> termsem δ γ v tm ⋲ δ (typeof tm)`,
  Induct_on `tm` >> rpt strip_tac
  >- (fs[VFREE_IN_def,termsem_def])
  >- (fs[termsem_def,is_frag_interpretation_def,terms_of_frag_def,consts_of_term_def]
      >> rfs[is_std_interpretation_def,ext_std_type_assignment]
      >> fs[nonbuiltin_constinsts_def,builtin_consts,pred_setTheory.SUBSET_DEF]
      >> fs[allTypes_def]
      >> drule builtin_closure_allTypes'
      >> simp[] >> strip_tac
      >> reverse(Cases_on `?ty. Const m t = Equal ty`)
      >- (fs[pairTheory.ELIM_UNCURRY]
          >> rename1 `γ (name,ty)`
          >> first_x_assum(qspec_then `(name,ty)` mp_tac)
          >> impl_tac
          >- (first_x_assum match_mp_tac >> metis_tac[])
          >> simp[])
          >> fs[is_std_type_assignment_def]
      >- (fs[] >> rpt(BasicProvers.VAR_EQ_TAC) >> fs[allTypes'_def]
           >> drule builtin_closure_allTypes' >> simp[]
           >> strip_tac >> first_x_assum drule >> fs[is_std_type_assignment_def]
           >> strip_tac >> drule abstract_in_funspace
           >> disch_then match_mp_tac >> rw[]
           >> drule abstract_in_funspace
           >> disch_then match_mp_tac >> rw[]
           >> match_mp_tac boolean_in_boolset >> simp[]))
  >- (fs[termsem_def,typeof_def,is_frag_interpretation_def,terms_of_frag_def,
         is_std_type_assignment_def,is_std_interpretation_def]
      >> drule apply_in_rng >> disch_then(match_mp_tac)
      >> rpt(first_x_assum drule >> rpt(disch_then drule) >> strip_tac)
      >> rfs[allTypes_def,consts_of_term_def,
             PURE_ONCE_REWRITE_RULE [pred_setTheory.INTER_COMM] (pred_setTheory.UNION_OVER_INTER)]
      >> rpt(first_x_assum(qspec_then `v` assume_tac)) >> rfs[]
      >> metis_tac[])
  >- (fs[termsem_def,typeof_def,is_frag_interpretation_def,terms_of_frag_def,
         is_std_type_assignment_def,is_std_interpretation_def]
      >> drule abstract_in_funspace >> disch_then match_mp_tac
      >> rw[]
      >> first_x_assum match_mp_tac
      >> MAP_EVERY qexists_tac [`tyfrag`,`tmfrag`]
      >> fs[consts_of_term_def,allTypes_def]
      >> rw[]
      >> rw[combinTheory.UPDATE_def] >> fs[]));

val termsem_in_type_ext = Q.store_thm("termsem_in_type_ext",
  `!tyfrag tmfrag δ γ v tm sig.
  is_set_theory ^mem /\ is_sig_fragment sig (tyfrag,tmfrag) /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag (tyfrag,tmfrag) /\
  (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ) ty)
  ==> termsem (ext_type_frag_builtins δ) (ext_term_frag_builtins (ext_type_frag_builtins δ) γ) v tm ⋲ ext_type_frag_builtins δ (typeof tm)`,
  rpt strip_tac
  >> drule termsem_in_type >> disch_then match_mp_tac
  >> MAP_EVERY qexists_tac [`builtin_closure tyfrag`,`tmfrag ∪ builtin_terms(builtin_closure tyfrag)`]
  >> conj_tac
  >- (simp[is_std_interpretation_def,is_std_type_assignment_def]
      >> simp[Once ext_term_frag_builtins_def, Once ext_type_frag_builtins_def]
      >> simp[Once ext_type_frag_builtins_def]
      >> simp[builtin_closure_idem])
  >> conj_tac
  >- (match_mp_tac is_frag_interpretation_ext >> qexists_tac `sig` >> simp[])
  >> conj_tac
  >- (fs[terms_of_frag_def] >> fs[boolTheory.IN_DEF,pred_setTheory.SUBSET_DEF]
      >> metis_tac[builtin_closure_rules])
  >> rw[]);

val termsem_in_type_closed = Q.store_thm("termsem_in_type_closed",
  `!tyfrag tmfrag δ γ v tm.
  is_set_theory ^mem /\
  is_std_interpretation tyfrag δ γ /\
  is_frag_interpretation (tyfrag,tmfrag) δ γ /\
  tm ∈ terms_of_frag (tyfrag,tmfrag) /\
  CLOSED tm
  ==> termsem δ γ v tm ⋲ δ (typeof tm)`,
  rpt strip_tac >> drule termsem_in_type
  >> rpt(disch_then drule)
  >> disch_then match_mp_tac
  >> fs[CLOSED_def]);

(* todo: useless? *)
val empty_valuation = xDefine "empty_valuation"
  `empty_valuation0 ^mem = (K One):(mlstring # type -> 'U)`;

val _ = Parse.overload_on("empty_valuation",``empty_valuation0 ^mem``);

val fleq_def = xDefine "fleq"
  `fleq0 ^mem ((tyfrag1,tmfrag1),(δ1: type -> 'U,γ1: mlstring # type -> 'U)) ((tyfrag2,tmfrag2),(δ2,γ2)) =
   (tmfrag1 ⊆ tmfrag2 /\ tyfrag1 ⊆ tyfrag2
    /\ (!c ty. (c,ty) ∈ tmfrag1 ==> γ1(c,ty) = γ2(c,ty))
    /\ (!ty. ty ∈ tyfrag1 ==> δ1 ty = δ2 ty))`

val _ = Parse.overload_on("fleq",``fleq0 ^mem``);

val builtin_closure_mono_lemma = Q.prove(
  `!tys1 ty. builtin_closure tys1 ty ==> !tys2. tys1 ⊆ tys2 ==> builtin_closure tys2 ty`,
  ho_match_mp_tac builtin_closure_ind
  >> rpt strip_tac
  >> metis_tac[builtin_closure_rules,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]);

val builtin_closure_mono = Q.store_thm("builtin_closure_mono",
  `!tys1 tys2. tys1 ⊆ tys2 ==> builtin_closure tys1 ⊆ builtin_closure tys2`,
  metis_tac[builtin_closure_mono_lemma,pred_setTheory.SUBSET_DEF,boolTheory.IN_DEF]);

(* LEMMA 9 *)

(* 9(1) *)
val fleq_types_le = Q.prove(
  `!frag1 i1 frag2 i2. fleq (frag1,i1) (frag2,i2)
   ==> types_of_frag frag1 ⊆ types_of_frag frag2`,
  rpt Cases
  >> rw[fleq_def,types_of_frag_def]
  >> imp_res_tac builtin_closure_mono);

(* 9(2) *)
val fleq_terms_le = Q.store_thm("fleq_terms_le",
  `!frag1 i1 frag2 i2. fleq (frag1,i1) (frag2,i2)
   ==> terms_of_frag frag1 ⊆ terms_of_frag frag2`,
  rpt Cases
  >> rw[fleq_def,terms_of_frag_def,pred_setTheory.SUBSET_DEF]);

(* 9(3) *)
val fleq_type_interp_le = Q.store_thm("fleq_type_interp_le",
  `!ty frag1 δ1 γ1 frag2 δ2 γ2 sig. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
    is_sig_fragment sig frag1 /\ ty ∈ types_of_frag frag1
   ==> ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty`,
  ho_match_mp_tac type_ind >> rpt strip_tac
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[fleq_def,types_of_frag_def]
      >> ONCE_REWRITE_TAC [ext_type_frag_builtins_def]
      >> fs[boolTheory.IN_DEF,Once builtin_closure_cases])
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[types_of_frag_def]
      >> qpat_assum `fleq _ _` (strip_assume_tac o SIMP_RULE (srw_ss()) [fleq_def])
      >> fs[boolTheory.IN_DEF,Once builtin_closure_cases]
      >> ONCE_REWRITE_TAC [ext_type_frag_builtins_def]
      >> rpt(BasicProvers.PURE_TOP_CASE_TAC >> fs[])
      >- (fs[is_sig_fragment_def,nonbuiltin_types_def,pred_setTheory.SUBSET_DEF,
             boolTheory.IN_DEF] >> rpt(first_x_assum drule)
          >> simp[is_builtin_type_def,is_builtin_name_def])
      >> qmatch_goalsub_abbrev_tac `Funspace a1 a2 = Funspace a3 a4`
      >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
      >> unabbrev_all_tac
      >> rpt(first_x_assum drule >> rpt(disch_then drule))
      >> simp[types_of_frag_def]));

(* 9(4) *)
val fleq_term_interp_le = Q.store_thm("fleq_term_interp_le",
  `!tm v frag1 δ1 γ1 frag2 δ2 γ2 sig. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
   is_sig_fragment sig frag1 /\ tm ∈ terms_of_frag frag1 /\ is_set_theory ^mem /\
   is_frag_interpretation frag1 δ1 γ1 /\
   (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ1 ty))
   ==>
   termsem (ext_type_frag_builtins δ1) (ext_term_frag_builtins (ext_type_frag_builtins δ1) γ1) v tm
   = termsem (ext_type_frag_builtins δ2) (ext_term_frag_builtins (ext_type_frag_builtins δ2) γ2) v tm`,
  Induct >> rpt strip_tac
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[termsem_def,VFREE_IN_def])
  >- (MAP_EVERY Cases_on [`frag1`,`frag2`]
      >> fs[termsem_def,fleq_def]
      >> fs[terms_of_frag_def,consts_of_term_def,allTypes_def]
      >> fs[nonbuiltin_constinsts_def,builtin_consts]
      >> fs[pred_setTheory.SUBSET_DEF]
      >> rw[ext_term_frag_builtins_def]
      >> fs[]
      >- (`ext_type_frag_builtins δ1 ty = ext_type_frag_builtins δ2 ty` suffices_by simp[]
          >> match_mp_tac ext_type_frag_mono_eq >> fs[allTypes'_def])
      >> first_x_assum match_mp_tac
      >> first_x_assum match_mp_tac
      >> simp[] >> metis_tac[])
  >- (fs[termsem_def]
      >> qmatch_goalsub_abbrev_tac `a1 ' a2 = a3 ' a4`
      >> `a1 = a3 /\ a2 = a4` suffices_by simp[]
      >> unabbrev_all_tac
      >> rpt(first_x_assum drule >> disch_then drule)
      >> rpt(disch_then(qspec_then `v` assume_tac))
      >> fs[terms_of_frag_def]
      >> imp_res_tac terms_of_frag_combE
      >> fs[])
  >- (rename1 `Abs ratortm randtm`
      >> `welltyped(Abs ratortm randtm)` by(Cases_on `frag1` >> fs[terms_of_frag_def])
      >> fs[termsem_def]
      >> qmatch_goalsub_abbrev_tac `Abstract a1 _ _ = Abstract a2 _ _`
      >> `a1 = a2`
         by(unabbrev_all_tac >> fs[termsem_def]
            >> drule fleq_type_interp_le
            >> disch_then drule >> disch_then match_mp_tac
            >> Cases_on `frag1` >> fs[types_of_frag_def,is_sig_fragment_def,terms_of_frag_def]
            >> fs[allTypes_def] >> match_mp_tac builtin_closure_allTypes'
            >> fs[pred_setTheory.SUBSET_DEF])
      >> simp[] >> drule abstract_eq >> disch_then match_mp_tac
      >> rw[]
      >- (match_mp_tac termsem_in_type_ext
          >> MAP_EVERY qexists_tac [`FST frag1`,`SND frag1`,`sig`]
          >> simp[]
          >> imp_res_tac terms_of_frag_AbsE
          >> rw[combinTheory.UPDATE_def]
          >> unabbrev_all_tac >> simp[]
          >> first_x_assum match_mp_tac >> fs[])
      >- (imp_res_tac terms_of_frag_AbsE
          >> first_x_assum drule >> rpt(disch_then drule)
          >> disch_then(qspec_then `((n,ty) =+ x) v` mp_tac)
          >> impl_tac
          >- (rw[combinTheory.UPDATE_def] >> unabbrev_all_tac >> simp[]
              >> first_x_assum match_mp_tac >> fs[])
          >> disch_then (strip_assume_tac o GSYM)
          >> simp[]
          >> `ext_type_frag_builtins δ1 (typeof randtm) = ext_type_frag_builtins δ2 (typeof randtm)`
               by(drule fleq_type_interp_le >> disch_then match_mp_tac >> qexists_tac `sig` >> simp[]
                  >> match_mp_tac term_frag_in_type_frag \\ metis_tac[])
          >> pop_assum(fn thm => PURE_ONCE_REWRITE_TAC [GSYM thm])
          >> match_mp_tac termsem_in_type_ext
          >> MAP_EVERY qexists_tac [`FST frag1`,`SND frag1`,`sig`]
          >> simp[]
          >> imp_res_tac terms_of_frag_AbsE
          >> rw[combinTheory.UPDATE_def]
          >> unabbrev_all_tac >> simp[]
          >> first_x_assum match_mp_tac >> fs[])
      >- (imp_res_tac terms_of_frag_AbsE
          >> first_x_assum drule >> rpt(disch_then drule)
          >> disch_then(qspec_then `((n,ty) =+ x) v` mp_tac)
          >> impl_tac
          >- (rw[combinTheory.UPDATE_def] >> unabbrev_all_tac >> simp[]
              >> first_x_assum match_mp_tac >> fs[])
          >> disch_then (strip_assume_tac o GSYM)
          >> simp[])));

val fleq_term_interp_le_closed = Q.store_thm("fleq_term_interp_le_closed",
  `!tm v frag1 δ1 γ1 frag2 δ2 γ2 sig. fleq (frag1,(δ1,γ1)) (frag2,(δ2,γ2)) /\
   is_sig_fragment sig frag1 /\ tm ∈ terms_of_frag frag1 /\ is_set_theory ^mem /\
   is_frag_interpretation frag1 δ1 γ1 /\
   CLOSED tm
   ==>
   termsem (ext_type_frag_builtins δ1) (ext_term_frag_builtins (ext_type_frag_builtins δ1) γ1) v tm
   = termsem (ext_type_frag_builtins δ2) (ext_term_frag_builtins (ext_type_frag_builtins δ2) γ2) v tm`,
  rpt strip_tac >> drule fleq_term_interp_le
  >> rpt(disch_then drule) >> disch_then match_mp_tac
  >> fs[CLOSED_def]);

val valuates_term_def = xDefine "valuates_term"`
  valuates_term0 ^mem δ v tm = (!x ty. VFREE_IN (Var x ty) tm ==> v(x,ty) ⋲ (ext_type_frag_builtins δ ty))`;
val _ = Parse.overload_on("valuates_term",``valuates_term0 ^mem``)

(*val is_valuation_def = xDefine "is_valuation"`
  is_valuation0 ^mem frag δ v ⇔
    ∀var ty. ty ∈ types_of_frag frag ⇒ v (var,ty) <: ext_type_frag_builtins δ ty`
val _ = Parse.overload_on("is_valuation",``is_valuation0 ^mem``)*)

val models_def = xDefine "models"`
  models0 ^mem frag δ γ v tm =
  (valuates_term δ v tm /\ tm ∈ terms_of_frag frag /\ termsem δ γ v tm = True)`
val _ = Parse.overload_on("models",``models0 ^mem``)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem frag δ γ (h,c) ⇔
    ∀v. valuates_term δ v c ∧ EVERY (valuates_term δ v) h ∧ c ∈ terms_of_frag frag ∧ EVERY (λt. t ∈ terms_of_frag frag) h ∧
      EVERY (λt. termsem δ γ v t = True) h
      ⇒ termsem δ γ v c = True`
(*val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)*)
val _ = Parse.overload_on("satisfies",``satisfies0 ^mem``)

(* TODO: move to syntax *)
val LIST_UNION_EQ_NIL = Q.store_thm("LIST_UNION_EQ_NIL",
  `LIST_UNION a1 a2 = [] <=> (a1 = [] /\ a2 = [])`,
  rw[EQ_IMP_THM]
  \\ `set(LIST_UNION a1 a2) = set []` by(simp_tac list_ss [] \\ pop_assum ACCEPT_TAC)
  \\ fs[]);
                         
val total_fragment_def = Define `
  total_fragment sig = (ground_types sig ∩ nonbuiltin_types, ground_consts sig ∩ nonbuiltin_constinsts)`

val ground_types_builtin_closure = Q.store_thm("ground_types_builtin_closure",
  `!c sig. c ∈ ground_types sig ==> c ∈ builtin_closure (ground_types sig ∩ nonbuiltin_types)`,
  ho_match_mp_tac type_ind
  \\ rpt strip_tac
  >- (fs[boolTheory.IN_DEF] \\ match_mp_tac builtin_closure_inj
      \\ fs[pred_setTheory.INTER_DEF,boolTheory.IN_DEF,nonbuiltin_types_def,is_builtin_type_def,
            is_builtin_name_def])
  \\ Cases_on `Tyapp m l ∈ nonbuiltin_types`
  >- (fs[boolTheory.IN_DEF] \\ match_mp_tac (builtin_closure_inj) \\
      simp[boolTheory.IN_DEF])
  \\ fs[nonbuiltin_types_def,builtin_types_def,is_builtin_type_def,is_builtin_name_def,
        quantHeuristicsTheory.LIST_LENGTH_2,boolTheory.IN_DEF]
  \\ fs[tyvars_def,ground_types_def,LIST_UNION_EQ_NIL,type_ok_def]
  \\ metis_tac[builtin_closure_rules]);

val total_fragment_is_fragment = Q.store_thm("total_fragment_is_fragment",
  `!sig. is_sig_fragment sig (total_fragment sig)`,
  rw[total_fragment_def,is_sig_fragment_def,ground_consts_def,nonbuiltin_constinsts_def]
  \\ imp_res_tac ground_types_builtin_closure);

val total_fragment_is_top_fragment = Q.store_thm("total_fragment_is_top_fragment",
  `!sig frag. is_sig_fragment sig frag
   ==> FST frag ⊆ FST(total_fragment sig) /\ SND frag ⊆ SND(total_fragment sig)
  `,
  CONV_TAC(SWAP_FORALL_CONV) \\ Cases \\ rw[total_fragment_def,is_sig_fragment_def]);

(* type substitutions as functions *)
(*val type_subst_def = tDefine "type_subst"
  `type_subst f (Tyvar v) = f v /\
   type_subst f (Tyapp v tys) = Tyapp v (MAP (λa. type_subst f a) tys)`
  (WF_REL_TAC `measure(type_size o SND)` \\ rw[type_size_def]
  \\ drule type1_size_append \\ simp[]);

val inst_def = tDefine "type_subst"
  `type_subst f (Tyvar v) = f v /\
   type_subst f (Tyapp v tys) = Tyapp v (MAP (λa. type_subst f a) tys)`
  (WF_REL_TAC `measure(type_size o SND)` \\ rw[type_size_def]
  \\ drule type1_size_append \\ simp[]);*)

(*val ground_type_subst_def = Define `ground_type_subst f =
   !v. f v ∈ ground_types sig`*)

val satisfies_t_def = xDefine"satisfies_t"`
  satisfies_t0 ^mem sig δ γ (h,c) ⇔
  !sigma.
  let h' = MAP (INST sigma) h; c' = INST sigma c in
    EVERY (λtm. tm ∈ ground_terms sig) h' /\ c' ∈ ground_terms sig
    ==> satisfies (total_fragment sig) δ γ (h',c')
  `
val _ = Parse.overload_on("satisfies_t",``satisfies_t0 ^mem``)
(*val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)*)

(*val frag_of_sig = Define
  `frag_of_sig (tysig,tmsig) =
    ({ty | type_ok ty} ∩ nonbuiltin_types ∩ ground_types sig,
     )`*)

val models_def = xDefine"models"`
  models0 ^mem δ γ (thy:thy) ⇔
    is_frag_interpretation (total_fragment (sigof thy)) δ γ ∧
    ∀p. p ∈ (axsof thy) ⇒
    satisfies_t (sigof thy)
                (ext_type_frag_builtins δ)
                (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
                ([],p)`
val _ = Parse.overload_on("models",``models0 ^mem``)

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀δ γ. models δ γ thy
      ⇒ satisfies_t (sigof thy)
                    (ext_type_frag_builtins δ)
                    (ext_term_frag_builtins (ext_type_frag_builtins δ) γ)
                    (h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)
                         
(*

(* A type assignment is a map from type operator names to semantic functions.
   Each function takes a list of sets representing the meanings of the
   arguments and returns the meaning of the applied operator. The assignment is
   with respect to a type signature, and is only constrained for defined type
   operators applied to the right number of non-empty arguments. *)

val _ = Parse.type_abbrev("tyass",``:mlstring -> 'U list -> 'U``)

val is_type_assignment_def = xDefine "is_type_assignment"`
  is_type_assignment0 ^mem tysig (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tysig`
val _ = Parse.overload_on("is_type_assignment",``is_type_assignment0 ^mem``)
                         
(* A type valuation is a map from type variable names to non-empty sets. *)

val _ = Parse.type_abbrev("tyval",``:mlstring -> 'U``)

val is_type_valuation_def = xDefine "is_type_valuation"`
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)`
val _ = Parse.overload_on("is_type_valuation",``is_type_valuation0 ^mem``)

(* Semantics of types. Simply applies the valuation and assignment. *)

val typesem_def = tDefine "typesem"`
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))`
  (type_rec_tac "SND o SND")

(* A term assignment is a map from a constant name and a list of values for the
   free type variables to a value for the constant. The assignment is with
   respect to a signature and is only constrained for defined constants. *)

val _ = Parse.type_abbrev("tmass",``:mlstring -> 'U list -> 'U``)

val is_term_assignment_def = xDefine "is_term_assignment"`
  is_term_assignment0 ^mem tmsig δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty))))) <: typesem δ τ ty)
      tmsig`
val _ = Parse.overload_on("is_term_assignment",``is_term_assignment0 ^mem``)

(* A term valuation is a map from a variable to an element of its type. The
   result is not polymorphic: term valuations are specialised for particular
   type valuations. *)

val _ = Parse.type_abbrev("tmval",``:mlstring # type -> 'U``)

val is_term_valuation_def = xDefine "is_term_valuation"`
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty`
val _ = Parse.overload_on("is_term_valuation",``is_term_valuation0 ^mem``)

(* An interpretation is a pair of assignments.
   A valuation is a pair of valuations. *)

val _ = Parse.type_abbrev("interpretation",``:'U tyass # 'U tmass``)
val _ = Parse.overload_on("tyaof",``FST:'U interpretation->'U tyass``)
val _ = Parse.overload_on("tmaof",``SND:'U interpretation->'U tmass``)
val _ = Parse.type_abbrev("valuation",``:'U tyval # 'U tmval``)
val _ = Parse.overload_on("tyvof",``FST:'U valuation->'U tyval``)
val _ = Parse.overload_on("tmvof",``SND:'U valuation->'U tmval``)

val is_valuation_def = xDefine"is_valuation"`
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)`
val _ = Parse.overload_on("is_valuation",``is_valuation0 ^mem``)

(* term assignment for instances of constants *)

val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`,
    simp[GSYM SKOLEM_THM] >> rw[] >>
    Cases_on`FLOOKUP tmsig name`>>simp[] >>
    qmatch_assum_rename_tac`FLOOKUP tmsig name = SOME ty0` >>
    Cases_on`is_instance ty0 ty` >> fs[] >>
    qmatch_assum_rename_tac`ty = TYPE_SUBST tyin ty0` >>
    qho_match_abbrev_tac`∃f. ∀tyin. P tyin ⇒ f = Q tyin` >>
    qexists_tac`Q tyin` >>
    rw[Abbr`P`,Abbr`Q`,FUN_EQ_THM] >> rpt AP_TERM_TAC >>
    rw[listTheory.MAP_EQ_f] >> rw[] >>
    fs[listTheory.MEM_MAP,mlstringTheory.implode_explode] >>
    metis_tac[TYPE_SUBST_tyvars]))

(* Semantics of terms. *)

val termsem_def = xDefine "termsem"`
  (termsem0 ^mem (tmsig:tmsig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem tmsig i v (Const name ty) = instance tmsig i name ty (tyvof v)) ∧
  (termsem0 ^mem tmsig i v (Comb t1 t2) =
   termsem0 ^mem tmsig i v t1 ' (termsem0 ^mem tmsig i v t2)) ∧
  (termsem0 ^mem tmsig i v (Abs (Var x ty) b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem tmsig i (tyvof v, ((x,ty)=+m)(tmvof v)) b))`
val _ = Parse.overload_on("termsem",``termsem0 ^mem``)

(* Satisfaction of sequents. *)

val satisfies_def = xDefine"satisfies"`
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True`
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
val _ = Parse.overload_on("satisfies",``satisfies0 ^mem``)

(* A interpretation of a theory is a pair of assignments to the constants and
   types in the theory. *)

val is_interpretation_def = xDefine "is_interpretation"`
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)`
val _ = Parse.overload_on("is_interpretation",``is_interpretation0 ^mem``)

(* The assignments are standard if they interpret fun, bool, and = according
   to the standard model. *)

val is_std_type_assignment_def = xDefine "is_std_type_assignment"`
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (∀dom rng. δ (strlit "fun") [dom;rng] = Funspace dom rng) ∧
    (δ (strlit "bool") [] = boolset)`
val _ = Parse.overload_on("is_std_type_assignment",``is_std_type_assignment0 ^mem``)

local
  open Parse
  val hs = HardSpace 1
  fun bs n = BreakSpace(1,n)
in
val _ = Parse.add_rule{term_name = "interprets",
                       fixity = Infix (NONASSOC,450),
                       pp_elements = [TOK "interprets", hs, TM, hs, TOK "on", bs 2, TM, hs, TOK "as", bs 2],
                       paren_style = OnlyIfNecessary,
                       block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0))}
end
val interprets_def = xDefine"interprets"`
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)`
val _ = Parse.overload_on("interprets",``interprets0 ^mem``)

val is_std_interpretation_def = xDefine "is_std_interpretation"`
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets (strlit "=") on [(strlit "A")] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))`
val _ = Parse.overload_on("is_std_interpretation",``is_std_interpretation0 ^mem``)

(* A model of a theory is a standard interpretation that satisfies all the
   axioms. *)

val models_def = xDefine"models"`
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)`
val _ = Parse.add_infix("models",450,Parse.NONASSOC)
val _ = Parse.overload_on("models",``models0 ^mem``)

(* Validity of sequents. *)

val entails_def = xDefine"entails"`
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)`
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
val _ = Parse.overload_on("|=",``entails0 ^mem``)

(* Collect standard signature, standard interpretation and valuation up in one
   predicate *)

val is_structure_def = xDefine"is_structure"`
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val`
val _ = Parse.overload_on("is_structure",``is_structure0 ^mem``)
*)
val _ = export_theory()

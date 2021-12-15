(*
  Prove that kernel functions maintain Candle prover's invariants
 *)

open preamble helperLib;
open semanticPrimitivesTheory semanticPrimitivesPropsTheory
     terminationTheory namespacePropsTheory evaluatePropsTheory
     sptreeTheory ml_hol_kernelProgTheory;
open permsTheory candle_kernel_valsTheory candle_prover_invTheory ast_extrasTheory;
local open ml_progLib in end

val _ = new_theory "candle_kernel_funs";

val _ = set_grammar_ancestry [
  "candle_kernel_vals", "candle_prover_inv", "ast_extras", "termination",
  "namespaceProps", "perms", "semanticPrimitivesProps", "misc"];

Theorem inferred_ok:
  inferred ctxt f ∧
  state_ok ctxt s ∧
  v_ok ctxt v ∧
  do_opapp [f; v] = SOME (env, exp) ∧
  evaluate s env [exp] = (s', res) ⇒
    ∃ctxt'.
      state_ok ctxt' s' ∧
      (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
      (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
      (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
      (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once inferred_cases]
  >~ [‘f ∈ kernel_funs’] >- cheat (* (
    gs [kernel_funs_def]
    >~ [‘conj_v’] >- (
      gvs [conj_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘conj_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, conj_v_def])
    >~ [‘imp_v’] >- (
      gvs [imp_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘imp_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, imp_v_def])
    >~ [‘disj1_v’] >- (
      gvs [disj1_v_def, do_opapp_def, evaluate_def]
      \\ first_assum (irule_at Any) \\ simp []
      \\ irule v_ok_KernelVals
      \\ irule v_ok_PartialApp
      \\ Q.LIST_EXISTS_TAC [‘disj1_v’, ‘v’]
      \\ irule_at Any v_ok_Inferred
      \\ irule_at Any inferred_KernelFuns
      \\ simp [kernel_funs_def]
      \\ simp [Once do_partial_app_def, disj1_v_def])
    >~ [‘not_not_v’] >- (
      cheat)) *)
  >~ [‘TYPE ctxt ty’] >- (
    Cases_on ‘ty’ \\ gs [TYPE_TYPE_def, do_opapp_cases])
  >~ [‘TERM ctxt tm’] >- (
    Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_opapp_cases])
  >~ [‘THM ctxt th’] >- (
    Cases_on ‘th’ \\ gs [THM_TYPE_def, do_opapp_cases])
QED

Theorem v_ok_THM_TYPE_HEAD:
  v_ok ctxt v ∧
  THM_TYPE_HEAD v ⇒
    ∃th. THM_TYPE th v
Proof
  rw [Once v_ok_cases, kernel_types_def, THM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem v_ok_TERM_TYPE_HEAD:
  v_ok ctxt v ∧
  TERM_TYPE_HEAD v ⇒
    ∃tm. TERM_TYPE tm v
Proof
  rw [Once v_ok_cases, kernel_types_def, TERM_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

Theorem v_ok_TYPE_TYPE_HEAD:
  v_ok ctxt v ∧
  TYPE_TYPE_HEAD v ⇒
    ∃ty. TYPE_TYPE ty v
Proof
  rw [Once v_ok_cases, kernel_types_def, TYPE_TYPE_HEAD_def]
  \\ gs [Once v_ok_cases, do_partial_app_def, AllCaseEqs ()]
  \\ gs [Once inferred_cases, SF SFY_ss, Conv_NOT_IN_kernel_funs]
  \\ TRY (rename [‘TYPE ctxt ty’] \\ Cases_on ‘ty’ \\ gs [TYPE_TYPE_def])
  \\ TRY (rename [‘TERM ctxt tm’] \\ Cases_on ‘tm’ \\ gs [TERM_TYPE_def])
  \\ TRY (rename [‘THM ctxt th’] \\ Cases_on ‘th’ \\ gs [THM_TYPE_def])
QED

(*
 * TODO Move elsewhere
 *)

Theorem Arrow2:
  (A --> B --> C) f fv ∧
  do_partial_app fv av = SOME gv ∧
  do_opapp [gv; bv] = SOME (env, exp) ∧
  evaluate (s:'ffi semanticPrimitives$state) env [exp] = (s', res) ∧
  A a av ∧ B b bv ∧
  DoEval ∉ ps ∧
  RefAlloc ∉ ps ∧
  W8Alloc ∉ ps ∧
  (∀n. RefMention n ∉ ps) ∧
  perms_ok ps av ∧
  perms_ok ps bv ∧
  perms_ok ps fv ⇒
    s.ffi = s'.ffi ∧
    ((res = Rerr (Rabort Rtimeout_error)) ∨
     (res = Rerr (Rabort Rtype_error)) ∨
     s.refs = s'.refs ∧
     s.next_type_stamp = s'.next_type_stamp ∧
     ∃rv. res = Rval [rv] ∧
          C (f a b) rv)
Proof
  strip_tac
  \\ ‘LENGTH s'.refs = LENGTH s.refs’
    by (gvs [do_partial_app_def, CaseEqs ["v", "exp"], do_opapp_cases,
             perms_ok_def]
        \\ drule_at_then (Pat ‘evaluate’)
                         (qspec_then ‘ps’ mp_tac)
                         evaluate_perms_ok_exp
        \\ impl_tac \\ simp []
        \\ gs [perms_ok_state_def, perms_ok_env_def]
        \\ Cases \\ simp [ml_progTheory.nsLookup_nsBind_compute]
        \\ rw [] \\ gs []
        \\ first_x_assum irule
        \\ first_assum (irule_at (Pos last)) \\ gs [])
  \\ qabbrev_tac ‘env' = write "a" av (write "b" bv (write "f" fv ARB))’
  \\ ‘Eval env' (Var (Short "a")) (A a)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "b")) (B b)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ ‘Eval env' (Var (Short "f")) ((A --> B --> C) f)’
    by simp [Abbr ‘env'’, ml_translatorTheory.Eval_Var_SIMP]
  \\ qpat_x_assum ‘(_ --> _) _ _’ kall_tac
  \\ qpat_x_assum ‘A _ _’ kall_tac
  \\ qpat_x_assum ‘B _ _’ kall_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow \\ strip_tac
  \\ dxrule_all ml_translatorTheory.Eval_Arrow
  \\ simp [ml_translatorTheory.Eval_def]
  \\ disch_then (qspec_then ‘s.refs’ strip_assume_tac)
  \\ dxrule ml_translatorTheory.evaluate_empty_state_IMP
  \\ simp [ml_progTheory.eval_rel_def, evaluate_def, Abbr ‘env'’,
           ml_progTheory.nsLookup_write]
  \\ qpat_x_assum ‘do_partial_app _ _ = _’ mp_tac
  \\ simp [do_partial_app_def, Once do_opapp_def, AllCaseEqs (), PULL_EXISTS]
  \\ rpt gen_tac \\ strip_tac
  \\ rpt gen_tac \\ strip_tac \\ gvs []
  \\ qpat_x_assum ‘do_opapp _ = SOME (env,exp)’ mp_tac
  \\ simp [do_opapp_cases]
  \\ strip_tac \\ gvs [evaluate_def, do_opapp_cases,
                       evaluateTheory.dec_clock_def]
  \\ dxrule_then (qspec_then ‘s.clock’ mp_tac) evaluate_set_init_clock
  \\ simp [with_same_clock]
  \\ strip_tac \\ gvs []
  \\ mp_tac (CONJUNCT1 is_clock_io_mono_evaluate)
  \\ qmatch_asmsub_abbrev_tac ‘evaluate s env1 [e]’
  \\ disch_then (qspecl_then [`s`,`env1`,`[e]`] mp_tac)
  \\ rw [is_clock_io_mono_def]
  \\ gs [io_events_mono_antisym]
QED

Theorem v_ok_TYPE:
  v_ok ctxt v ∧
  TYPE_TYPE ty v ⇒
    TYPE ctxt ty
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule TYPE_from_TYPE_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘ty’ \\ gvs [TYPE_TYPE_def, v_ok_def, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_TERM:
  v_ok ctxt v ∧
  TERM_TYPE tm v ⇒
    TERM ctxt tm
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule TERM_from_TERM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘tm’ \\ gvs [TERM_TYPE_def, v_ok_def, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_THM:
  v_ok ctxt v ∧
  THM_TYPE th v ⇒
    THM ctxt th
Proof
  strip_tac
  \\ Cases_on ‘inferred ctxt v’
  >- (
    irule THM_from_THM_TYPE
    \\ gs [SF SFY_ss])
  \\ Cases_on ‘th’ \\ gvs [THM_TYPE_def, v_ok_def, kernel_types_def]
  \\ gvs [Once v_ok_cases, do_partial_app_def, CaseEqs ["exp", "v"]]
QED

Theorem v_ok_bind_exn_v[simp]:
  v_ok ctxt bind_exn_v
Proof
  rw [v_ok_def, bind_exn_v_def]
  \\rw [Once v_ok_cases, bind_stamp_def, kernel_types_def]
QED

Theorem v_ok_sub_exn_v[simp]:
  v_ok ctxt sub_exn_v
Proof
  rw [v_ok_def, sub_exn_v_def]
  \\ rw [Once v_ok_cases, subscript_stamp_def, kernel_types_def]
QED

Theorem kernel_vals_max_app:
  kernel_vals ctxt f ∧
  do_partial_app f v = SOME g ∧
  do_opapp [g; w] = SOME (env, exp) ⇒
    f ∈ kernel_funs
Proof
  cheat
QED

Theorem LIST_TYPE_perms_ok:
  ∀xs xsv.
    (∀x v. A x v ∧ MEM x xs ⇒ perms_ok ps v) ∧
    LIST_TYPE A xs xsv ⇒
      perms_ok ps xsv
Proof
  Induct \\ rw []
  \\ gs [ml_translatorTheory.LIST_TYPE_def, perms_ok_def, SF SFY_ss]
QED

Theorem TYPE_TYPE_perms_ok:
  ∀ty v. TYPE_TYPE ty v ⇒ perms_ok ps v
Proof
  recInduct TYPE_TYPE_ind \\ rw [TYPE_TYPE_def]
  \\ rename [‘STRING_TYPE m _’]
  \\ Cases_on ‘m’
  \\ gvs [ml_translatorTheory.STRING_TYPE_def, perms_ok_def]
  \\ metis_tac [LIST_TYPE_perms_ok]
QED

Theorem TERM_TYPE_perms_ok:
  ∀tm v. TERM_TYPE tm v ⇒ perms_ok ps v
Proof
  Induct \\ rw [TERM_TYPE_def]
  \\ res_tac \\ fs [perms_ok_def]
  \\ rename [‘STRING_TYPE m _’]
  \\ Cases_on ‘m’ \\ imp_res_tac TYPE_TYPE_perms_ok
  \\ gvs [ml_translatorTheory.STRING_TYPE_def, perms_ok_def]
QED

Theorem THM_TYPE_perms_ok:
  ∀th v. THM_TYPE th v ⇒ perms_ok ps v
Proof
  Cases \\ rw [THM_TYPE_def] \\ imp_res_tac TERM_TYPE_perms_ok
  \\ fs [perms_ok_def]
  \\ drule_at (Pos last) LIST_TYPE_perms_ok
  \\ disch_then irule \\ rw []
  \\ imp_res_tac TERM_TYPE_perms_ok \\ fs []
QED

(*
Theorem perms_ok_member_v:
  perms_ok ps member_v
Proof
  rw [member_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
QED

Theorem perms_ok_list_union_v:
  perms_ok ps list_union_v
Proof
  rw [list_union_v_def, perms_ok_def, perms_ok_exp_def,
      astTheory.pat_bindings_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "member"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_member_v]
QED

Theorem conj_v_perms_ok:
  perms_ok ps conj_v
Proof
  rw [conj_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = {Short "list_union"}’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs [])
  \\ gs [perms_ok_env_def]
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ CONV_TAC (DEPTH_CONV ml_progLib.nsLookup_conv) \\ simp []
  \\ simp [perms_ok_list_union_v]
QED

Theorem disj1_v_perms_ok:
  perms_ok ps disj1_v
Proof
  rw [disj1_v_def, perms_ok_def, perms_ok_exp_def]
  \\ qmatch_goalsub_abbrev_tac ‘perms_ok_env ps fvs’
  \\ ‘fvs = EMPTY’
    by (rw [Abbr ‘fvs’, EXTENSION, astTheory.pat_bindings_def]
        \\ rw [DISJ_EQ_IMP, EQ_IMP_THM] \\ gs []
        \\ CCONTR_TAC \\ gs [])
  \\ gs [perms_ok_env_def]
QED
*)

Theorem trans_v_perms_ok: (* TODO: move *)
  perms_ok ps trans_v
Proof
  cheat
QED

Theorem kernel_vals_ok:
  ∀ctxt f.
    kernel_vals ctxt f ⇒
      ∀s v env exp s' res.
        do_opapp [f; v] = SOME (env, exp) ∧
        state_ok ctxt s ∧
        v_ok ctxt v ∧
        evaluate s env [exp] = (s', res) ⇒
          (∃abort. s'.ffi = s.ffi ∧ res = Rerr (Rabort abort)) ∨
          ∃ctxt'.
            state_ok ctxt' s' ∧
            (∀v. v_ok ctxt v ⇒ v_ok ctxt' v) ∧
            (∀v. kernel_vals ctxt v ⇒ kernel_vals ctxt' v) ∧
            (∀vs. res = Rval vs ⇒ EVERY (v_ok ctxt') vs) ∧
            (∀v. res = Rerr (Rraise v) ⇒ v_ok ctxt' v)
Proof
  rw [Once v_ok_cases]
  >~ [‘inferred ctxt f’] >- (
    rw [DISJ_EQ_IMP]
    \\ irule_at Any inferred_ok
    \\ first_assum (irule_at Any)
    \\ first_assum (irule_at Any) \\ gs []
    \\ first_assum (irule_at Any) \\ gs [])
  \\ rename [‘do_partial_app f v = SOME g’]
  \\ rw [DISJ_EQ_IMP]
  \\ reverse (Cases_on ‘f ∈ kernel_funs’)
  >- (gs [Once v_ok_cases, Once inferred_cases]
      >- (Cases_on ‘ty’ \\ gs [TYPE_TYPE_def, do_partial_app_def])
      >- (Cases_on ‘tm’ \\ gs [TERM_TYPE_def, do_partial_app_def])
      >- (Cases_on ‘th’ \\ gs [THM_TYPE_def, do_partial_app_def])
      \\ ‘kernel_vals ctxt f’
        by (irule v_ok_PartialApp
            \\ first_assum (irule_at (Pos hd))
            \\ gs [])
      \\ drule_all kernel_vals_max_app
      \\ rw [kernel_funs_def])
  \\ Cases_on ‘f = trans_v’ \\ gvs []
  >- (
    drule_all_then strip_assume_tac trans_v_head \\ gvs []
    >- (first_assum (irule_at Any) \\ gs [])
    \\ rename1 ‘do_opapp [g; w]’
    \\ ‘∃th1. THM_TYPE th1 v’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘∃th2. THM_TYPE th2 w’
      by (irule_at Any v_ok_THM_TYPE_HEAD \\ gs [SF SFY_ss])
    \\ ‘∃ps. DoEval ∉ ps ∧
             RefAlloc ∉ ps ∧
             W8Alloc ∉ ps ∧
             (∀n. RefMention n ∉ ps) ∧
             perms_ok ps trans_v’
      by (irule_at Any trans_v_perms_ok
          \\ qexists_tac ‘EMPTY’ \\ gs [])
    \\ ‘perms_ok ps v ∧ perms_ok ps w’
      by gs [SF SFY_ss, THM_TYPE_perms_ok]
    \\ assume_tac trans_v_thm (*
    \\ drule_all Arrow2
    \\ strip_tac \\ gvs []
    \\ irule_at (Pos last) v_ok_KernelVals
    \\ irule_at Any v_ok_Inferred
    \\ irule_at Any inferred_THM
    \\ first_assum (irule_at (Pos (el 2)))
    \\ irule_at Any conj_thm
    \\ imp_res_tac v_ok_THM
    \\ first_assum (irule_at Any) \\ gs []
    \\ gs [state_ok_def] *) \\ cheat)
  \\ cheat (* the other kernel functions *)
QED

val _ = export_theory ();

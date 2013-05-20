open HolKernel Parse boolLib bossLib; val _ = new_theory "std_prelude";

open arithmeticTheory listTheory combinTheory pairTheory sumTheory;
open optionTheory oneTheory bitTheory stringTheory whileTheory;
open finite_mapTheory pred_setTheory;
open AstTheory LibTheory AltBigStepTheory SemanticPrimitivesTheory;
open terminationTheory alistTheory;

open ml_translatorLib ml_translatorTheory mini_preludeTheory;;

val _ = translation_extends "mini_prelude"; (* HD, TL, APPEND, REV, REVERSE *)


(* pair *)

val res = translate FST;
val res = translate SND;
val res = translate CURRY_DEF;
val res = translate UNCURRY;

(* combin *)

val res = translate o_DEF;
val res = translate I_THM;
val res = translate C_DEF;
val res = translate K_DEF;
val res = translate S_DEF;
val res = translate UPDATE_def;
val res = translate W_DEF;

(* option *)

val res = translate THE_DEF;
val res = translate IS_NONE_DEF;
val res = translate IS_SOME_DEF;
val res = translate OPTION_MAP_DEF;
val res = translate OPTION_MAP2_DEF;

val THE_side_def = prove(
  ``THE_side = IS_SOME``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "THE_side_def"])
  |> update_precondition;

val OPTION_MAP2_side_def = prove(
  ``!f x y. OPTION_MAP2_side f x y = T``,
  FULL_SIMP_TAC (srw_ss()) [fetch "-" "OPTION_MAP2_side_def",THE_side_def])
  |> update_precondition;

(* sum *)

val res = translate ISL;
val res = translate ISR;
val res = translate OUTL;
val res = translate OUTR;
val res = translate SUM_MAP_def;

val OUTL_side_def = prove(
  ``OUTL_side = ISL``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "OUTL_side_def"])
  |> update_precondition;

val OUTR_side_def = prove(
  ``OUTR_side = ISR``,
  FULL_SIMP_TAC std_ss [FUN_EQ_THM] THEN Cases
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "OUTR_side_def"])
  |> update_precondition;

(* list *)

val LENGTH_AUX_def = Define `
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))`;

val LENGTH_AUX_THM = prove(
  ``!xs n. LENGTH_AUX xs n = LENGTH xs + n``,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];

val SUC_LEMMA = prove(``SUC = \x. x+1``,SIMP_TAC std_ss [FUN_EQ_THM,ADD1]);

val res = translate LENGTH_AUX_def;
val res = translate LENGTH_AUX_THM;
val res = translate MAP;
val res = translate FILTER;
val res = translate FOLDR;
val res = translate FOLDL;
val res = translate SUM;
val res = translate UNZIP;
val res = translate FLAT;
val res = translate TAKE_def;
val res = translate DROP_def;
val res = translate SNOC;
val res = translate EVERY_DEF;
val res = translate EXISTS_DEF;
val res = translate GENLIST;
val res = translate PAD_RIGHT;
val res = translate PAD_LEFT;
val res = translate MEMBER_def;
val res = translate (ALL_DISTINCT |> REWRITE_RULE [MEMBER_INTRO]);
val res = translate isPREFIX;
val res = translate FRONT_DEF;
val res = translate ZIP;
val res = translate EL;
val res = translate LAST_DEF;
val res = translate (splitAtPki_DEF |> REWRITE_RULE [SUC_LEMMA])

val FRONT_side_def = prove(
  ``!xs. FRONT_side xs = ~(xs = [])``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "FRONT_side_def",CONTAINER_def])
  |> update_precondition;

val ZIP_side_def = prove(
  ``!x. ZIP_side x = (LENGTH (FST x) = LENGTH (SND x))``,
  Cases THEN Q.SPEC_TAC (`r`,`r`) THEN Induct_on `q` THEN Cases_on `r`
  THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "ZIP_side_def"])
  |> update_precondition;

val EL_side_def = prove(
  ``!n xs. EL_side n xs = (n < LENGTH xs)``,
  Induct THEN Cases_on `xs` THEN FULL_SIMP_TAC (srw_ss())
    [fetch "-" "EL_side_def",CONTAINER_def])
  |> update_precondition;

val LAST_side_def = prove(
  ``!xs. LAST_side xs = ~(xs = [])``,
  Induct THEN FULL_SIMP_TAC (srw_ss()) [fetch "-" "LAST_side_def",CONTAINER_def])
  |> update_precondition;

(* sorting *)

val res = translate sortingTheory.PART_DEF;
val res = translate sortingTheory.PARTITION_DEF;
val res = translate sortingTheory.QSORT_DEF;

(* arithmetic *)

val EXP_AUX_def = Define `
  EXP_AUX m n k = if n = 0 then k else EXP_AUX m (n-1:num) (m * k:num)`;

val EXP_AUX_THM = prove(
  ``!n k. EXP_AUX m n (m**k) = m**(k+n)``,
  Induct THEN SIMP_TAC std_ss [EXP,Once EXP_AUX_def,ADD1]
  THEN ASM_SIMP_TAC std_ss [GSYM EXP]
  THEN FULL_SIMP_TAC std_ss [ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`n`,`0`] |> SIMP_RULE std_ss [EXP] |> GSYM;

val res = translate EXP_AUX_def;
val res = translate EXP_AUX_THM; (* tailrec version of EXP *)
val res = translate MIN_DEF;
val res = translate MAX_DEF;
val res = translate EVEN_MOD2;
val res = translate (REWRITE_RULE [EVEN_MOD2,DECIDE ``~(n = 0) = (0 < n:num)``] ODD_EVEN);
val res = translate FUNPOW;
val res = translate ABS_DIFF_def;
val res = translate (DECIDE ``PRE n = n-1``);

(* string *)

val CHAR_def = Define `
  CHAR (c:char) = NUM (ORD c)`;

val _ = add_type_inv ``CHAR`` ``:num``

val EqualityType_CHAR = prove(
  ``EqualityType CHAR``,
  EVAL_TAC THEN SRW_TAC [] [] THEN EVAL_TAC)
  |> store_eq_thm;

val Eval_Val_CHAR = prove(
  ``n < 256 ==> Eval env (Lit (IntLit (&n))) (CHAR (CHR n))``,
  SIMP_TAC (srw_ss()) [Eval_Val_NUM,CHAR_def])
  |> store_eval_thm;

val Eval_ORD = prove(
  ``!v. ((NUM --> NUM) (\x.x)) v ==> ((CHAR --> NUM) ORD) v``,
  SIMP_TAC std_ss [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\x.x:num``))
  |> store_eval_thm;

val Eval_CHR = prove(
  ``!v. ((NUM --> NUM) (\n. n MOD 256)) v ==>
        ((NUM --> CHAR) (\n. CHR (n MOD 256))) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\n. n MOD 256``))
  |> store_eval_thm;

val Eval_CHAR_LT = prove(
  ``!v. ((NUM --> NUM --> BOOL) (\m n. m < n)) v ==>
        ((CHAR --> CHAR --> BOOL) char_lt) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,CHAR_def,char_lt_def]
  THEN METIS_TAC [])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN (hol2deep ``\m n. m < n:num``))
  |> store_eval_thm;

val res = translate string_lt_def;
val res = translate string_le_def;
val res = translate string_gt_def;
val res = translate string_ge_def;

(* finite maps *)

val FMAP_EQ_ALIST_def = Define `
  FMAP_EQ_ALIST f l <=> (ALOOKUP l = FLOOKUP f)`;

val FMAP_TYPE_def = Define `
  FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) (f:'a|->'b) =
    \v. ?l. LIST_TYPE (PAIR_TYPE a b) l v /\ FMAP_EQ_ALIST f l`;

val _ = add_type_inv ``FMAP_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool)``
                     ``:('a # 'b) list``;

val ALOOKUP_eval = translate ALOOKUP_def;

val Eval_FLOOKUP = prove(
  ``!v. ((LIST_TYPE (PAIR_TYPE (b:'b -> v -> bool) (a:'a -> v -> bool)) -->
          b --> OPTION_TYPE a) ALOOKUP) v ==>
        ((FMAP_TYPE b a --> b --> OPTION_TYPE a) FLOOKUP) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS,FMAP_EQ_ALIST_def] THEN METIS_TAC [])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN ALOOKUP_eval)
  |> store_eval_thm;

(*

val FAPPLY_ALT_def = Define `FAPPLY_ALT f x = THE (FLOOKUP f x)`;
val FAPPLY_ALT_eval = translate FAPPLY_ALT_def;

val decl_assum =
  FAPPLY_ALT_eval |> hyp |> first (can (match_term ``DeclAssum x y``))

val Eval_FAPPLY_ALT = prove(
  ``!(b:'b -> v -> bool) (a:'a -> v -> bool).
      ^decl_assum /\
      PRECONDITION (IS_SOME (FLOOKUP v1 v2)) /\
      EqualityType b ==>
      Eval env (Var (Short "FAPPLY_ALT"))
        ((Eq (FMAP_TYPE b a) v1 --> Eq b v2 --> a) $')``,
  REPEAT STRIP_TAC
  THEN MATCH_MP_TAC (MATCH_MP Eval_WEAKEN FAPPLY_ALT_eval |> DISCH_ALL |>
                     REWRITE_RULE [AND_IMP_INTRO])
  THEN FULL_SIMP_TAC std_ss [PRECONDITION_def] THEN REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [fetch "-" "FAPPLY_ALT_side_def"]
  THEN FULL_SIMP_TAC std_ss [Arrow_def,AppReturns_def,Eq_def,FAPPLY_ALT_def]
  THEN FULL_SIMP_TAC std_ss [FLOOKUP_DEF]
  THEN Cases_on `v2 IN FDOM v1` THEN FULL_SIMP_TAC std_ss [])
  |> SPEC_ALL |> UNDISCH_ALL |> store_eval_thm;

*)

val AUPDATE_def = Define `AUPDATE l (x:'a,y:'b) = (x,y)::l`;
val AUPDATE_eval = translate AUPDATE_def;

val FMAP_EQ_ALIST_UPDATE = prove(
  ``FMAP_EQ_ALIST f l ==> FMAP_EQ_ALIST (FUPDATE f (x,y)) (AUPDATE l (x,y))``,
  SIMP_TAC (srw_ss()) [FMAP_EQ_ALIST_def,AUPDATE_def,ALOOKUP_def,FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_DEF,finite_mapTheory.FAPPLY_FUPDATE_THM]
  THEN METIS_TAC []);

val Eval_FUPDATE = prove(
  ``!v. ((LIST_TYPE (PAIR_TYPE a b) -->
          PAIR_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool) -->
          LIST_TYPE (PAIR_TYPE a b)) AUPDATE) v ==>
        ((FMAP_TYPE a b --> PAIR_TYPE a b --> FMAP_TYPE a b) FUPDATE) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS] THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN Q.EXISTS_TAC `u` THEN FULL_SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC THEN RES_TAC
  THEN Q.LIST_EXISTS_TAC [`u'`,`AUPDATE l x'`]
  THEN FULL_SIMP_TAC std_ss [] THEN METIS_TAC [FMAP_EQ_ALIST_UPDATE,PAIR])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN AUPDATE_eval)
  |> store_eval_thm;

val NIL_eval = hol2deep ``[]:('a # 'b) list``

val Eval_FEMPTY = prove(
  ``!v. (LIST_TYPE (PAIR_TYPE (a:'a -> v -> bool) (b:'b -> v -> bool)) []) v ==>
        ((FMAP_TYPE a b) FEMPTY) v``,
  SIMP_TAC (srw_ss()) [Arrow_def,AppReturns_def,FMAP_TYPE_def,
    PULL_EXISTS,FMAP_EQ_ALIST_def] THEN REPEAT STRIP_TAC THEN Q.EXISTS_TAC `[]`
  THEN FULL_SIMP_TAC (srw_ss()) [ALOOKUP_def,FUN_EQ_THM,
         finite_mapTheory.FLOOKUP_DEF])
  |> MATCH_MP (MATCH_MP Eval_WEAKEN NIL_eval)
  |> store_eval_thm;

(* while, owhile and least *)

val IS_SOME_OWHILE_THM = prove(
  ``!g f x. (IS_SOME (OWHILE g f x)) =
            ?n. ~ g (FUNPOW f n x) /\ !m. m < n ==> g (FUNPOW f m x)``,
  REPEAT STRIP_TAC THEN Cases_on `OWHILE g f x`
  THEN FULL_SIMP_TAC (srw_ss()) [OWHILE_EQ_NONE]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def]
  THEN Q.EXISTS_TAC `LEAST n. ~g (FUNPOW f n x)`
  THEN (Q.INST [`P`|->`\n. ~g (FUNPOW f n x)`] FULL_LEAST_INTRO
      |> SIMP_RULE std_ss [] |> IMP_RES_TAC)
  THEN ASM_SIMP_TAC std_ss [] THEN REPEAT STRIP_TAC
  THEN IMP_RES_TAC LESS_LEAST THEN FULL_SIMP_TAC std_ss []);

val evaluate_closure_INTRO = prove(
  ``(?env' e3. (do_app empty_store env Opapp v2 v3 = SOME (empty_store,env',e3)) /\
               evaluate' empty_store env' e3 (empty_store,Rval (v2'))) =
    evaluate_closure v3 v2 v2'``,
  SIMP_TAC (srw_ss()) [evaluate_closure_def,do_app_def]);

val EXISTS_SWAP = METIS_PROVE [] ``(?x y. P x y) ==> (?y x. P x y)``

val tac =
  REPEAT STRIP_TAC
  THEN FULL_SIMP_TAC std_ss [PRECONDITION_def,IS_SOME_OWHILE_THM,Eval_def]
  THEN SIMP_TAC (srw_ss()) [Once evaluate'_cases,build_rec_env_def]
  THEN SIMP_TAC (srw_ss()) [Once Arrow_def,AppReturns_def]
  THEN SIMP_TAC (srw_ss()) [evaluate_closure_def,do_app_def,
                            find_recfun_def,bind_def,build_rec_env_def]
  THEN SIMP_TAC std_ss [Once Eq_def]
  THEN NTAC 2 STRIP_TAC
  THEN SIMP_TAC (srw_ss()) [Once evaluate'_cases,build_rec_env_def]
  THEN SIMP_TAC (srw_ss()) [Once Arrow_def,AppReturns_def]
  THEN SIMP_TAC (srw_ss()) [evaluate_closure_def,do_app_def,
                            find_recfun_def,bind_def,build_rec_env_def]
  THEN SIMP_TAC std_ss [Once Eq_def]
  THEN NTAC 2 STRIP_TAC
  THEN SIMP_TAC (srw_ss()) [Once evaluate'_cases,build_rec_env_def]
  THEN Q.ABBREV_TAC `gv = v'` THEN Q.ABBREV_TAC `fv = v''`
  THEN POP_ASSUM (K ALL_TAC) THEN POP_ASSUM (K ALL_TAC)
  THEN SIMP_TAC (srw_ss()) [Once evaluate'_cases,build_rec_env_def]
  THEN SIMP_TAC (srw_ss()) [lookup_def,bind_def]
  THEN SIMP_TAC (srw_ss()) [Once Arrow_def,AppReturns_def]
  THEN SIMP_TAC std_ss [Once Eq_def] THEN REPEAT STRIP_TAC
  THEN SIMP_TAC (srw_ss()) [evaluate_closure_def,do_app_def,
                            find_recfun_def,bind_def,build_rec_env_def]
  THEN Q.ABBREV_TAC `xv = v'` THEN POP_ASSUM (K ALL_TAC)
  THEN REPEAT (POP_ASSUM MP_TAC)
  THEN Q.SPEC_TAC (`x`,`x`) THEN Q.SPEC_TAC (`xv`,`xv`)
  THEN SIMP_TAC std_ss [GSYM Eval_def]
  THEN CONV_TAC (DEPTH_CONV ETA_CONV)
  THEN Induct_on `n` THEN1
   (FULL_SIMP_TAC std_ss [FUNPOW] THEN REPEAT STRIP_TAC
    THEN ONCE_REWRITE_TAC [OWHILE_THM,WHILE]
    THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] Eval_If |> GEN_ALL)
    THEN Q.LIST_EXISTS_TAC [`T`,`F`,`T`]
    THEN FULL_SIMP_TAC std_ss [CONTAINER_def]
    THEN REVERSE STRIP_TAC THEN1
      (NTAC 6 (ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,
                 EVAL ``OPTION_TYPE a (SOME x) v``,Eval_def,do_app_def]))
    THEN `F = g x` by METIS_TAC []
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] Eval_Arrow)
    THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
    THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def])
  THEN FULL_SIMP_TAC std_ss [FUNPOW] THEN REPEAT STRIP_TAC
  THEN ONCE_REWRITE_TAC [OWHILE_THM,WHILE]
  THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] Eval_If |> GEN_ALL)
  THEN Q.LIST_EXISTS_TAC [`F`,`T`,`T`]
  THEN `g x` by
   (Q.PAT_ASSUM `!m.bbb` (MP_TAC o Q.SPEC `0`) THEN FULL_SIMP_TAC std_ss [FUNPOW])
  THEN ASM_SIMP_TAC std_ss [CONTAINER_def]
  THEN STRIP_TAC THEN1
   (`T = g x` by FULL_SIMP_TAC std_ss []
    THEN POP_ASSUM (fn th => ONCE_REWRITE_TAC [th])
    THEN MATCH_MP_TAC (REWRITE_RULE [AND_IMP_INTRO] Eval_Arrow)
    THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
    THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def])
  THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
  THEN ONCE_REWRITE_TAC [evaluate'_empty_store] THEN FULL_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [do_app_empty_store] THEN FULL_SIMP_TAC std_ss []
  THEN ONCE_REWRITE_TAC [evaluate'_empty_store] THEN FULL_SIMP_TAC std_ss []
  THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
  THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
  THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
  THEN ASM_SIMP_TAC (srw_ss()) [Once evaluate'_cases,lookup_def,Eval_def]
  THEN ONCE_REWRITE_TAC [evaluate'_empty_store] THEN FULL_SIMP_TAC std_ss []
  THEN SIMP_TAC std_ss [evaluate_closure_INTRO]
  THEN FULL_SIMP_TAC (srw_ss()) [do_app_def,find_recfun_def,
         bind_def,build_rec_env_def]
  THEN FULL_SIMP_TAC std_ss [PULL_EXISTS,PULL_FORALL]
  THEN HO_MATCH_MP_TAC EXISTS_SWAP
  THEN `?v_fx. evaluate_closure xv fv v_fx /\ a (f x) v_fx` by ALL_TAC THEN1
       (FULL_SIMP_TAC std_ss [Arrow_def,AppReturns_def] THEN METIS_TAC [])
  THEN Q.EXISTS_TAC `v_fx` THEN FULL_SIMP_TAC std_ss [GSYM Eval_def]
  THEN FULL_SIMP_TAC std_ss [AND_IMP_INTRO] THEN CONV_TAC (DEPTH_CONV ETA_CONV)
  THEN Q.PAT_ASSUM `!x1 x2. bbb` MATCH_MP_TAC THEN ASM_SIMP_TAC std_ss []
  THEN REPEAT STRIP_TAC
  THEN Q.PAT_ASSUM `!m. bbb` (MP_TAC o Q.SPEC `SUC m`)
  THEN FULL_SIMP_TAC (srw_ss()) [FUNPOW]

val Eval_WHILE = prove(
  ``PRECONDITION (IS_SOME (OWHILE g f (x:'a))) ==>
    Eval env (Fun "g" (Fun "f" (Letrec
         [("w","x",
             (If (App Opapp (Var (Short "g")) (Var (Short "x")))
                 (App Opapp (Var (Short "w"))
                   (App Opapp (Var (Short "f")) (Var (Short "x"))))
               (Var (Short "x"))))] (Var (Short "w")))))
      ((Eq (a --> BOOL) g --> Eq (a --> a) f --> Eq a x --> a) WHILE)``,
  tac) |> UNDISCH_ALL |> store_eval_thm;

val Eval_OWHILE = prove(
  ``PRECONDITION (IS_SOME (OWHILE g f (x:'a))) ==>
    Eval env (Fun "g" (Fun "f" (Letrec
         [("w","x",
             (If (App Opapp (Var (Short "g")) (Var (Short "x")))
                 (App Opapp (Var (Short "w"))
                   (App Opapp (Var (Short "f")) (Var (Short "x"))))
               (Con (Short "Some") [Var (Short "x")])))] (Var (Short "w")))))
      ((Eq (a --> BOOL) g --> Eq (a --> a) f --> Eq a x --> OPTION_TYPE a) OWHILE)``,
  tac) |> UNDISCH_ALL |> store_eval_thm;

val LEAST_LEMMA = prove(
  ``$LEAST P = WHILE (\x. ~(P x)) (\x. x + 1) 0``,
  SIMP_TAC std_ss [LEAST_DEF,o_DEF,SUC_LEMMA]);

val res = translate LEAST_LEMMA;

val FUNPOW_LEMMA = prove(
  ``!n m. FUNPOW (\x. x + 1) n m = n + m``,
  Induct THEN FULL_SIMP_TAC std_ss [FUNPOW,ADD1,AC ADD_COMM ADD_ASSOC]);

val LEAST_side_thm = prove(
  ``!s. LEAST_side s = ~(s = {})``,
  SIMP_TAC std_ss [fetch "-" "LEAST_side_def"]
  THEN FULL_SIMP_TAC std_ss [OWHILE_def,FUNPOW_LEMMA,FUN_EQ_THM,EMPTY_DEF]
  THEN METIS_TAC [IS_SOME_DEF])
  |> update_precondition;

val _ = export_theory();

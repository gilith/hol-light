(* ========================================================================= *)
(* STREAM TYPES                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for stream types.                                         *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/stream/stream.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of stream types.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "stream-def";;

let (snth_stream,stream_snth) =
  let exists = prove (`?(s : num -> A). T`, REWRITE_TAC []) in
  let tybij =
      REWRITE_RULE []
        (new_type_definition "stream" ("stream","snth") exists) in
  let th1 = prove
    (`!(s : A stream). stream (snth s) = s`, REWRITE_TAC [tybij])
  and th2 = prove
    (`!(f : num -> A). snth (stream f) = f`, REWRITE_TAC [tybij]) in
  (th1,th2);;

export_thm snth_stream;;
export_thm stream_snth;;

let stream_tybij = CONJ snth_stream stream_snth;;

let shd_def = new_definition
  `!s : A stream. shd s = snth s 0`;;

export_thm shd_def;;

let sdrop_def = new_definition
  `!(s : A stream) n. sdrop s n = stream (\m. snth s (m + n))`;;

export_thm sdrop_def;;

let stl_def = new_definition
  `!s : A stream. stl s = sdrop s 1`;;

export_thm stl_def;;

let scons_def = new_definition
  `!h (t : A stream).
     scons h t = stream (\n. if n = 0 then h else snth t (n - 1))`;;

export_thm scons_def;;

let (stake_zero,stake_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(s : A stream). stake s 0 = []) /\
     (!(s : A stream) n. stake s (SUC n) = CONS (shd s) (stake (stl s) n))` in
  CONJ_PAIR def;;

export_thm stake_zero;;
export_thm stake_suc;;

let stake_def = CONJ stake_zero stake_suc;;

let ssplit_def = new_definition
  `!s : A stream.
     ssplit s =
     (stream (\n. snth s (2 * n)),
      stream (\n. snth s (2 * n + 1)))`;;

export_thm ssplit_def;;

let sinterleave_def = new_definition
  `!s1 s2 : A stream.
     sinterleave s1 s2 =
     stream (\n. if EVEN n then snth s1 (n DIV 2) else snth s2 (n DIV 2))`;;

export_thm sinterleave_def;;

let sappend_def = new_definition
  `!l (s : A stream).
     sappend l s =
     stream (\n. if n < LENGTH l then nth l n else snth s (n - LENGTH l))`;;

export_thm sappend_def;;

let smap_def = new_definition
  `!(f : A -> B) (s : A stream).
     smap f s = stream (f o snth s)`;;

export_thm smap_def;;

let sunfold_def = new_definition
  `!(f : B -> A # B) b.
     sunfold f b =
     stream (\n. FST (f (funpow (SND o f) n b)))`;;

export_thm sunfold_def;;

let siterate_def = new_definition
  `!(f : A -> A). siterate f = sunfold (\a. (a, f a))`;;

export_thm siterate_def;;

let sreplicate_def = new_definition
  `sreplicate = siterate (I : A -> A)`;;

export_thm sreplicate_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of stream types.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "stream-thm";;

let snth_eq_imp = prove
  (`!(s1 : A stream) s2.
      (!n. snth s1 n = snth s2 n) ==>
      s1 = s2`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM snth_stream] THEN
   AP_TERM_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM]);;

export_thm snth_eq_imp;;

let snth_eq = prove
  (`!(s1 : A stream) s2.
      (!n. snth s1 n = snth s2 n) <=>
      s1 = s2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC snth_eq_imp;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC []]);;

export_thm snth_eq;;

let snth_add = prove
  (`!(s : A stream) m n. snth s (m + n) = snth (sdrop s n) m`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [sdrop_def; stream_tybij]);;

export_thm snth_add;;

let snth_suc = prove
  (`!(s : A stream) n. snth s (SUC n) = snth (stl s) n`,
   REWRITE_TAC [ADD1; snth_add; stl_def]);;

export_thm snth_suc;;

let shd_scons = prove
  (`!(h : A) t. shd (scons h t) = h`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [shd_def; scons_def; stream_snth]);;

export_thm shd_scons;;

let stl_scons = prove
  (`!(h : A) t. stl (scons h t) = t`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC
     [stl_def; scons_def; sdrop_def; stream_snth; GSYM ADD1;
      NOT_SUC; SUC_SUB1]);;

export_thm stl_scons;;

let snth_scons_zero = prove
  (`!h (t : A stream). snth (scons h t) 0 = h`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM shd_def; shd_scons]);;

export_thm snth_scons_zero;;

let snth_scons_suc = prove
  (`!h (t : A stream) n. snth (scons h t) (SUC n) = snth t n`,
   REWRITE_TAC [snth_suc; stl_scons]);;

export_thm snth_scons_suc;;

let snth_sappend = prove
  (`!l (s : A stream) n.
      snth (sappend l s) n =
      if n < LENGTH l then nth l n else snth s (n - LENGTH l)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [sappend_def; stream_snth]);;

export_thm snth_sappend;;

let sappend_assoc = prove
  (`!l1 l2 (s : A stream).
      sappend (APPEND l1 l2) s = sappend l1 (sappend l2 s)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [snth_sappend; LENGTH_APPEND] THEN
   ASM_CASES_TAC `n < LENGTH (l1 : A list)` THENL
   [SUBGOAL_THEN
      `n < LENGTH (l1 : A list) + LENGTH (l2 : A list)` ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `LENGTH (l1 : A list)` THEN
     ASM_REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`l1 : A list`; `l2 : A list`; `n : num`] nth_append) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
   REWRITE_TAC [LT_ADD_LCANCEL; ADD_SUB2] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`l1 : A list`; `l2 : A list`;
                   `LENGTH (l1 : A list) + d`] nth_append) THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL; ADD_SUB2] THEN
    DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [NOT_LT; LE_ADD];
     REFL_TAC];
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [ADD_ASSOC; ADD_SUB2]);;

export_thm sappend_assoc;;

let nil_sappend = prove
  (`!s : A stream. sappend [] s = s`,
   GEN_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [sappend_def; LENGTH; LT; SUB_0; stream_snth]);;

export_thm nil_sappend;;

let cons_sappend = prove
  (`!h t (s : A stream). sappend (CONS h t) s = scons h (sappend t s)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [sappend_def; stream_snth; scons_def; LENGTH] THEN
   NUM_CASES_TAC `n : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LT_NZ; NOT_SUC; nth_zero];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [NOT_SUC; LT_SUC; SUC_SUB1] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [] THEN
    MATCH_MP_TAC nth_suc THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [] THEN
    AP_TERM_TAC THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [GSYM SUC_ADD; ADD_SUB2]]);;

export_thm cons_sappend;;

let smap_id = prove
  (`smap (I : A -> A) = I`,
   REWRITE_TAC [FUN_EQ_THM; smap_def; I_O; stream_tybij; I_THM]);;

export_thm smap_id;;

let smap_o = prove
 (`!(f : B -> C) (g : A -> B) s. smap (f o g) s = smap f (smap g s)`,
  REWRITE_TAC [smap_def; stream_tybij; o_ASSOC]);;

export_thm smap_o;;

let smap_o' = prove
  (`!(f : B -> C) (g : A -> B). smap f o smap g = smap (f o g)`,
   REWRITE_TAC [FUN_EQ_THM; smap_o; o_THM]);;

export_thm smap_o';;

let sdrop_zero = prove
  (`!s : A stream. sdrop s 0 = s`,
   GEN_TAC THEN
   REWRITE_TAC [sdrop_def; ADD_0] THEN
   CONV_TAC (LAND_CONV (RAND_CONV ETA_CONV)) THEN
   MATCH_ACCEPT_TAC snth_stream);;

export_thm sdrop_zero;;

let sdrop_suc' = prove
  (`!(s : A stream) n. sdrop s (SUC n) = sdrop (stl s) n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [sdrop_def; ADD_SUC; stl_def; GSYM ADD1; stream_tybij]);;

export_thm sdrop_suc';;

let sdrop_funpow = prove
  (`!(s : A stream) n. sdrop s n = funpow stl n s`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [funpow_zero; sdrop_zero; I_THM];
    ASM_REWRITE_TAC [sdrop_suc'; funpow_suc_x']]);;

export_thm sdrop_funpow;;

let sdrop_suc = prove
  (`!(s : A stream) n. sdrop s (SUC n) = stl (sdrop s n)`,
   REWRITE_TAC [sdrop_funpow; funpow_suc_x]);;

export_thm sdrop_suc;;

let sdrop_one = prove
  (`!s : A stream. sdrop s 1 = stl s`,
   REWRITE_TAC [ONE; sdrop_suc; sdrop_zero]);;

export_thm sdrop_one;;

let shd_sdrop = prove
  (`!(s : A stream) n. shd (sdrop s n) = snth s n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [sdrop_zero; shd_def];
    ASM_REWRITE_TAC [sdrop_suc'; snth_suc]]);;

export_thm shd_sdrop;;

let stake_one = prove
  (`!(s : A stream). stake s 1 = [shd s]`,
   REWRITE_TAC [ONE; stake_suc; stake_zero]);;

export_thm stake_one;;

let length_stake = prove
  (`!(s : A stream) n. LENGTH (stake s n) = n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; stake_zero];
    ASM_REWRITE_TAC [LENGTH; stake_suc]]);;

export_thm length_stake;;

let stake_add = prove
  (`!(s : A stream) m n.
      stake s (m + n) = APPEND (stake s m) (stake (sdrop s m) n)`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`s : A stream`, `s : A stream`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [stake_zero; sdrop_zero; ZERO_ADD; NIL_APPEND];
    GEN_TAC THEN
    ASM_REWRITE_TAC [stake_suc; sdrop_suc'; SUC_ADD; CONS_APPEND]]);;

export_thm stake_add;;

let stake_suc' = prove
  (`!(s : A stream) n. stake s (SUC n) = APPEND (stake s n) [snth s n]`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [ADD1; stake_add; stake_one; shd_sdrop]);;

export_thm stake_suc';;

let mem_stake = prove
  (`!(s : A stream) n x. MEM x (stake s n) = ?i. i < n /\ x = snth s i`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`s : A stream`, `s : A stream`) THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [MEM_NIL; stake_zero; LT];
    GEN_TAC THEN
    ASM_REWRITE_TAC [MEM_CONS; stake_suc; GSYM snth_suc; shd_def] THEN
    POP_ASSUM (K ALL_TAC) THEN
    EQ_TAC THENL
    [STRIP_TAC THENL
     [EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC [LT_0];
      EXISTS_TAC `SUC i` THEN
      ASM_REWRITE_TAC [LT_SUC]];
     DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
     MP_TAC (SPEC `i : num` num_CASES) THEN
     DISCH_THEN
       (DISJ_CASES_THEN2
          SUBST1_TAC
          (X_CHOOSE_THEN `m : num` SUBST1_TAC)) THENL
     [STRIP_TAC THEN
      DISJ1_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC [LT_SUC] THEN
      STRIP_TAC THEN
      DISJ2_TAC THEN
      EXISTS_TAC `m : num` THEN
      ASM_REWRITE_TAC []]]]);;

export_thm mem_stake;;

let set_of_list_stake = prove
  (`!(s : A stream) n.
      set_of_list (stake s n) = { x | ?i. i < n /\ x = snth s i }`,
   REWRITE_TAC [EXTENSION; IN_ELIM; GSYM MEM_SET_OF_LIST; mem_stake]);;

export_thm set_of_list_stake;;

let nth_stake = prove
  (`!(s : A stream) n i. i < n ==> nth (stake s n) i = snth s i`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   SPEC_TAC (`s : A stream`, `s : A stream`) THEN
   SPEC_TAC (`i : num`, `i : num`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [LT_REFL];
     ALL_TAC] THEN
    STRIP_TAC THEN
    REWRITE_TAC [stake_suc; nth_zero; shd_def];
    ALL_TAC] THEN
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT_ZERO];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LT_SUC] THEN
   STRIP_TAC THEN
   REWRITE_TAC [stake_suc; snth_suc] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `nth (stake (stl s) n) i : A` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC nth_suc THEN
    ASM_REWRITE_TAC [length_stake];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm nth_stake;;

let ssplit_sinterleave = prove
  (`!s1 s2 : A stream. ssplit (sinterleave s1 s2) = (s1,s2)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [ssplit_def; sinterleave_def; PAIR_EQ] THEN
   SUBGOAL_THEN `~(2 = 0)` ASSUME_TAC THENL
   [NUM_REDUCE_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC snth_eq_imp THEN
    GEN_TAC THEN
    REWRITE_TAC [stream_snth; EVEN_DOUBLE] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC snth_eq_imp THEN
    GEN_TAC THEN
    REWRITE_TAC [stream_snth; GSYM NOT_ODD] THEN
    SUBGOAL_THEN `ODD (2 * n + 1)`
      (fun th ->
         (SUBST1_TAC o EQT_INTRO) th THEN
         (STRIP_ASSUME_TAC o REWRITE_RULE [ODD_MOD]) th) THENL
    [REWRITE_TAC [GSYM ADD1; ODD_DOUBLE];
     ALL_TAC] THEN
    REWRITE_TAC [] THEN
    AP_TERM_TAC THEN
    MP_TAC (SPECL [`2`; `(2 * n + 1) DIV 2`; `n : num`] EQ_MULT_LCANCEL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (SPECL [`2 * n + 1 : num`; `2`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm ssplit_sinterleave;;

let sunfold = prove
 (`!(f : B -> A # B) b.
     sunfold f b =
     let (a,b') = f b in
     scons a (sunfold f b')`,
  GEN_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [sunfold_def; scons_def; LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `(f : B -> A # B) b` THEN
  DISCH_THEN (X_CHOOSE_THEN `a : A` (X_CHOOSE_THEN `b' : B` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [stream_tybij] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  NUM_CASES_TAC `n : num` THENL
  [DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [funpow_zero; I_THM];
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   ASM_REWRITE_TAC [SUC_SUB1; NOT_SUC; funpow_suc_x'; o_THM]]);;

export_thm sunfold;;

let num_stream_exists = prove
  (`!(p : num -> bool).
      (!m. ?n. m <= n /\ p n) ==>
      ?s.
        (!i j. snth s i <= snth s j <=> i <= j) /\
        (!n. p n <=> ?i. snth s i = n)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MONO_SIMPLIFY] THEN
   EXISTS_TAC
     `sunfold (\b. let n = (minimal m. b <= m /\ p m) in (n, SUC n)) 0` THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [sunfold_def; stream_tybij; funpow_suc_x] THEN
    SPEC_TAC
      (`funpow
          (SND o (\b. let n = (minimal m. b <= m /\ p m) in (n, SUC n)))
          n 0`, `k : num`) THEN
    GEN_TAC THEN
    REWRITE_TAC [o_THM] THEN
    REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    SPEC_TAC (`minimal m. k <= m /\ p m`, `n : num`) THEN
    GEN_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `SUC n`) THEN
    REWRITE_TAC [MINIMAL] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [GSYM LE_SUC_LT];
    EQ_TAC THENL
    [STRIP_TAC THEN
     MP_TAC (SPEC `n : num` LE_0) THEN
     SPEC_TAC (`0`, `k : num`) THEN
     GEN_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV LE_EXISTS)) THEN
     REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
     STRIP_TAC THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     SPEC_TAC (`k : num`, `k : num`) THEN
     WF_INDUCT_TAC `d : num` THEN
     GEN_TAC THEN
     DISCH_THEN SUBST_VAR_TAC THEN
     ONCE_REWRITE_TAC [sunfold] THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     SUBGOAL_THEN
       `?m : num. k <= m /\ p m` (MP_TAC o REWRITE_RULE [MINIMAL]) THENL
     [EXISTS_TAC `k + d : num` THEN
      ASM_REWRITE_TAC [LE_ADD];
      ALL_TAC] THEN
     SPEC_TAC (`minimal m. k <= m /\ p m`, `j : num`) THEN
     GEN_TAC THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `k + d : num`) THEN
     POP_ASSUM (K ALL_TAC) THEN
     ASM_REWRITE_TAC [LE_ADD; NOT_LT] THEN
     POP_ASSUM MP_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV LE_EXISTS)) THEN
     DISCH_THEN (X_CHOOSE_THEN `x : num` SUBST_VAR_TAC) THEN
     REWRITE_TAC [LE_ADD_LCANCEL] THEN
     CONV_TAC (LAND_CONV (REWR_CONV LE_LT)) THEN
     STRIP_TAC THENL
     [POP_ASSUM (MP_TAC o REWRITE_RULE [LT_EXISTS]) THEN
      DISCH_THEN (X_CHOOSE_THEN `y : num` SUBST_VAR_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `y : num`) THEN
      ANTS_TAC THENL
      [REWRITE_TAC [ADD_CLAUSES; LT_SUC_LE; LE_ADDR];
       ALL_TAC] THEN
      DISCH_THEN (MP_TAC o SPEC `SUC (k + x)`) THEN
      ANTS_TAC THENL
      [REWRITE_TAC [ADD_CLAUSES; ADD_ASSOC];
       ALL_TAC] THEN
      STRIP_TAC THEN
      EXISTS_TAC `SUC i` THEN
      ASM_REWRITE_TAC [snth_scons_suc];
      FIRST_X_ASSUM SUBST_VAR_TAC THEN
      EXISTS_TAC `0` THEN
      REWRITE_TAC [snth_scons_zero]];
     REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
     GEN_TAC THEN
     SPEC_TAC (`0`, `k : num`) THEN
     SPEC_TAC (`i : num`, `i : num`) THEN
     INDUCT_TAC THENL
     [GEN_TAC THEN
      ONCE_REWRITE_TAC [sunfold] THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF; snth_scons_zero] THEN
      DISCH_THEN SUBST_VAR_TAC THEN
      FIRST_X_ASSUM (MP_TAC o REWRITE_RULE [MINIMAL] o SPEC `k : num`) THEN
      STRIP_TAC;
      GEN_TAC THEN
      ONCE_REWRITE_TAC [sunfold] THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF; snth_scons_suc] THEN
      FIRST_X_ASSUM
        (MATCH_ACCEPT_TAC o REWRITE_RULE [LET_DEF; LET_END_DEF])]]]);;

export_thm num_stream_exists;;

let siterate = prove
 (`!(f : A -> A) a. siterate f a = scons a (siterate f (f a))`,
  GEN_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [siterate_def] THEN
  CONV_TAC (LAND_CONV (REWR_CONV sunfold)) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF]);;

export_thm siterate;;

let sreplicate = prove
 (`!(a : A). sreplicate a = scons a (sreplicate a)`,
  GEN_TAC THEN
  REWRITE_TAC [sreplicate_def] THEN
  CONV_TAC (LAND_CONV (REWR_CONV siterate)) THEN
  REWRITE_TAC [I_THM]);;

export_thm sreplicate;;

let snth_sreplicate = prove
 (`!(a : A) n. snth (sreplicate a) n = a`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [ONCE_REWRITE_TAC [sreplicate] THEN
   REWRITE_TAC [GSYM shd_def; shd_scons];
   ONCE_REWRITE_TAC [sreplicate] THEN
   ASM_REWRITE_TAC [snth_suc; stl_scons]]);;

export_thm snth_sreplicate;;

let snth_src = prove
 (`!(s : A stream) n.
     snth s n = if n = 0 then shd s else snth (stl s) (n - 1)`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [shd_def];
   REWRITE_TAC [NOT_SUC; SUC_SUB1; snth_suc]]);;

export_thm snth_src;;

let stake_src = prove
 (`!(s : A stream) n.
     stake s n = if n = 0 then [] else CONS (shd s) (stake (stl s) (n - 1))`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [stake_zero];
   REWRITE_TAC [NOT_SUC; SUC_SUB1; stake_suc]]);;

export_thm stake_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for stream types.                                          *)
(* ------------------------------------------------------------------------- *)

logfile "stream-haskell-src";;

export_thm snth_src;;  (* Haskell *)
export_thm stake_src;;  (* Haskell *)
export_thm sunfold;;  (* Haskell *)

logfile_end ();;

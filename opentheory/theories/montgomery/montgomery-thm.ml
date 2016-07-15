(* ========================================================================= *)
(* PROPERTIES OF MONTGOMERY MULTIPLICATION                                   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "montgomery-thm";;

(* ------------------------------------------------------------------------- *)
(* Properties of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

let montgomery_reduce_lemma = prove
 (`!n r s k a. r * s = k * n + 1 ==> (a + (a * k) MOD r * n) MOD r = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
  [DISCH_THEN SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
   ALL_TAC] THEN
  MP_TAC (SPEC `r : num` MOD_MOD_REFL') THEN
  MP_TAC (SPEC `r : num` MOD_MULT_MOD2') THEN
  MP_TAC (SPEC `r : num` MOD_ADD_MOD') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
  POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
  SUBGOAL_THEN `a + (a * k) * n = a * (1 + k * n)` SUBST1_TAC THENL
  [REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1; MULT_ASSOC];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  REWRITE_TAC [GSYM MULT_ASSOC] THEN
  MATCH_MP_TAC MOD_MULT THEN
  FIRST_ASSUM ACCEPT_TAC);;

let montgomery_reduce_divides = prove
 (`!n r s k a.
     r * s = k * n + 1 ==>
     montgomery_reduce n r k a =
     a DIV r + (((a * k) MOD r) * n) DIV r +
     (if (a * k * n) MOD r = 0 then 0 else 1)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [montgomery_reduce_def] THEN
  SUBGOAL_THEN `~(r = 0)` (fun th -> ASSUME_TAC th THEN MP_TAC th) THENL
  [DISCH_THEN SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
   ALL_TAC] THEN
  MATCH_MP_TAC (TAUT `!x y. y \/ x ==> (~x ==> y)`) THEN
  REWRITE_TAC [GSYM EQ_MULT_RCANCEL; RIGHT_ADD_DISTRIB] THEN
  MP_TAC
    (SPECL
       [`n : num`; `r : num`; `s : num`; `k : num`; `a : num`]
       montgomery_reduce_lemma) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`a + (a * k) MOD r * n`; `r : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  ONCE_REWRITE_TAC
    [GSYM (SPEC `a MOD r + ((a * k) MOD r * n) MOD r` EQ_ADD_RCANCEL)] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((a DIV r * r + a MOD r) +
      (((a * k) MOD r * n) DIV r * r + ((a * k) MOD r * n) MOD r)) +
     (if (a * k * n) MOD r = 0 then 0 else 1) * r` THEN
  REVERSE_TAC CONJ_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
   ALL_TAC] THEN
  MP_TAC (SPECL [`a : num`; `r : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC (SPECL [`(a * k) MOD r * n`; `r : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  MP_TAC
    (SPECL
       [`r : num`;
        `a MOD r + ((a * k) MOD r * n) MOD r`]
       divides_mod) THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
    (SPECL
       [`a : num`;
        `(a * k) MOD r * n`;
        `r : num`]
       MOD_ADD_MOD) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  MP_TAC
    (SPECL
       [`r : num`;
        `(a * k) MOD r`;
        `n : num`]
       MOD_MULT_MOD2') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`a * k : num`;
        `r : num`]
       MOD_MOD_REFL) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`r : num`;
        `a * k : num`;
        `n : num`]
       MOD_MULT_MOD2') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [GSYM MULT_ASSOC] THEN
  REWRITE_TAC [divides_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `q : num` (ASSUME_TAC o SYM)) THEN
  ASM_REWRITE_TAC [EQ_MULT_RCANCEL] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC (SPEC `q : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `qs : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [ZERO_MULT; ADD_EQ_0] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [ZERO_MULT];
   ALL_TAC] THEN
  MP_TAC (SPEC `qs : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `qss : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [GSYM ONE; ONE_MULT] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [ONE; NOT_SUC; ADD_0] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`a : num`; `r : num`] DIVISION_DEF_MOD) THEN
    ASM_REWRITE_TAC [NOT_LT; LE_REFL];
    REWRITE_TAC []];
   ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `F` CONTR_TAC THEN
  MP_TAC (SPEC `SUC (SUC qss) * r` LT_REFL) THEN
  REWRITE_TAC [] THEN
  POP_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
  MATCH_MP_TAC LT_TRANS THEN
  EXISTS_TAC `r + (a * k * n) MOD r` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LT_ADD_RCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `r + r : num` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LT_ADD_LCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM MULT_2; LE_MULT_RCANCEL] THEN
  REWRITE_TAC [TWO; ONE; LE_SUC; LE_0]);;

export_thm montgomery_reduce_divides;;

let montgomery_reduce_bits = prove
 (`!n r s k a.
     2 EXP r * s = k * n + 1 ==>
     montgomery_reduce n (2 EXP r) k a =
     bit_shr a r +
     bit_shr (bit_bound (a * k) r * n) r +
     bit_to_num (~(bit_bound (a * k * n) r = 0))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bit_shr_def; bit_bound_def; bit_to_num_def; COND_SWAP] THEN
  MATCH_MP_TAC montgomery_reduce_divides THEN
  EXISTS_TAC `s : num` THEN
  ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_bits;;

let montgomery_reduce_correct = prove
 (`!n r s k a.
     ~(n = 0) /\
     r * s = k * n + 1 ==>
     montgomery_reduce n r k a MOD n = (a * s) MOD n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
  [DISCH_THEN SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(montgomery_reduce n r k a * (r * s)) MOD n` THEN
  CONJ_TAC THENL
  [SPEC_TAC (`montgomery_reduce n r k a`,`m : num`) THEN
   GEN_TAC THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   ASM_REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
   MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
   SUBGOAL_THEN `(m * k * n) MOD n = 0` SUBST1_TAC THENL
   [REWRITE_TAC [MULT_ASSOC] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    MATCH_MP_TAC MOD_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC MOD_MOD_REFL THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [MULT_ASSOC; montgomery_reduce_def] THEN
  MP_TAC (SPEC `n : num` MOD_MULT_MOD2') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC (SPECL [`a + (a * k) MOD r * n`; `r : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `(a + (a * k) MOD r * n) MOD r = 0` SUBST1_TAC THENL
  [MATCH_MP_TAC montgomery_reduce_lemma THEN
   EXISTS_TAC `s : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
  SUBGOAL_THEN `((a * k) MOD r * n) MOD n = 0` SUBST1_TAC THENL
  [ONCE_REWRITE_TAC [MULT_SYM] THEN
   MATCH_MP_TAC MOD_MULT THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [ADD_0] THEN
  MATCH_MP_TAC MOD_MOD_REFL THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_correct;;

let montgomery_reduce_bound = prove
 (`!n r k m a.
     ~(n = 0) /\
     ~(r = 0) /\
     a <= r * m ==>
     montgomery_reduce n r k a < m + n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [montgomery_reduce_def] THEN
  MATCH_MP_TAC LT_LDIV THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `a + r * n : num` THEN
  ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL; LT_MULT_RCANCEL] THEN
  MATCH_MP_TAC DIVISION_DEF_MOD THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_bound;;

let montgomery_reduce_normalized_bound = prove
 (`!n r k a.
     ~(n = 0) /\
     ~(r = 0) /\
     a <= r * n ==>
     montgomery_reduce n r k a < 2 * n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [MULT_2] THEN
  MATCH_MP_TAC montgomery_reduce_bound THEN
  ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_normalized_bound;;

let montgomery_reduce_unnormalized_bound = prove
 (`!n r k a.
     ~(n = 0) /\
     ~(r = 0) /\
     a <= r * r ==>
     montgomery_reduce n r k a < r + n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC montgomery_reduce_bound THEN
  ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_unnormalized_bound;;

let montgomery_reduce_small_bound = prove
 (`!n r k a.
     ~(n = 0) /\
     ~(r = 0) /\
     a <= r ==>
     montgomery_reduce n r k a <= n`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM LT_SUC_LE; ONCE_REWRITE_RULE [ADD_SYM] ADD1] THEN
  MATCH_MP_TAC montgomery_reduce_bound THEN
  ASM_REWRITE_TAC [MULT_1]);;

export_thm montgomery_reduce_small_bound;;

(* ========================================================================= *)
(* MONTGOMERY MULTIPLICATION                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Montgomery multiplication.                            *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/montgomery/montgomery.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Montgomery multiplication [1].                              *)
(*                                                                           *)
(* 1. http://en.wikipedia.org/wiki/Montgomery_reduction                      *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-def";;

let montgomery_reduce_def = new_definition
  `!n r k a.
     montgomery_reduce n r k a =
     (a + ((a * k) MOD r) * n) DIV r`;;

export_thm montgomery_reduce_def;;

let (montgomery_double_exp_zero,montgomery_double_exp_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!n r k a. montgomery_double_exp n r k a 0 = a) /\
     (!n r k a m.
        montgomery_double_exp n r k a (SUC m) =
        let b = montgomery_reduce n r k (a * a) in
        let c = if r <= b then b - n else b in
        montgomery_double_exp n r k c m)` in
  CONJ_PAIR def;;

export_thm montgomery_double_exp_zero;;
export_thm montgomery_double_exp_suc;;

let montgomery_double_exp_def =
    CONJ montgomery_double_exp_zero montgomery_double_exp_suc;;

(* ------------------------------------------------------------------------- *)
(* Properties of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-thm";;

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
   REWRITE_TAC [bit_shr_def; bit_bound_def; bit_to_num_def; COND_NOT] THEN
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

let montgomery_double_exp_correct = prove
  (`!n r s k a m.
      ~(n = 0) /\
      n <= r /\
      r * s = k * n + 1 ==>
      montgomery_double_exp n r k a m MOD n =
      ((a * s) EXP (2 EXP m) * r) MOD n`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [montgomery_double_exp_zero; EXP_0; EXP_1] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(s * r) MOD n = 1 MOD n` SUBST1_TAC THENL
    [MATCH_MP_TAC MOD_EQ THEN
     EXISTS_TAC `k : num` THEN
     ONCE_REWRITE_TAC [MULT_SYM; ADD_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC [MULT_1]];
    ALL_TAC] THEN
   GEN_TAC THEN
   ASM_REWRITE_TAC
     [montgomery_double_exp_suc; EXP_SUC; LET_DEF; LET_END_DEF; EXP_MULT;
      EXP_2] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((montgomery_reduce n r k (a * a) - n) + n) MOD n` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
     MP_TAC (SPEC `n : num` MOD_REFL) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [ADD_0] THEN
     MATCH_MP_TAC MOD_MOD_REFL THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `montgomery_reduce n r k (a * a) MOD n` THEN
     CONJ_TAC THENL
     [AP_THM_TAC THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC SUB_ADD THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `r : num` THEN
      ASM_REWRITE_TAC [];
      MATCH_MP_TAC montgomery_reduce_correct THEN
      ASM_REWRITE_TAC []]];
    MATCH_MP_TAC montgomery_reduce_correct THEN
    ASM_REWRITE_TAC []]);;

export_thm montgomery_double_exp_correct;;

let montgomery_double_exp_bound = prove
  (`!n r k a m.
      ~(n = 0) /\
      n <= r /\
      a < r ==>
      montgomery_double_exp n r k a m < r`,
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [montgomery_double_exp_zero];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_double_exp_suc; LET_DEF; LET_END_DEF] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [GSYM NOT_LT] THEN
   ASM_CASES_TAC `montgomery_reduce n r k (a * a) < r` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `n : num` LT_ADD_RCANCEL)] THEN
   SUBGOAL_THEN
     `montgomery_reduce n r k (a * a) - n + n =
      montgomery_reduce n r k (a * a)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUB_ADD THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [GSYM NOT_LT];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MATCH_MP_TAC montgomery_reduce_unnormalized_bound THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [NOT_LT; LE_0];
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LT_LE]) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `a * r : num` THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL; LE_MULT_RCANCEL]]);;

export_thm montgomery_double_exp_bound;;

(* ------------------------------------------------------------------------- *)
(* Definition of a Montgomery multiplication circuit.                        *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-montgomery-def";;

(* -------------------------------------------------------------- *)
(* Montgomery multiplication modulo 2^(r+2), where d = d1 + d2    *)
(* -------------------------------------------------------------- *)
(*        r+3 r+2 r+1  r  r-1 r-2 ... d+1  d  d-1 ...  2   1   0  *)
(* -------------------------------------------------------------- *)
(*  xs  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  xc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ys  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  yc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ks  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  kc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ns  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  nc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  pb  =  -   -   -   -   -   -  ...  -   -   X  ...  X   X   X  *)
(*  ps  =  -   -   X   X   X   X  ...  X   X   -  ...  -   -   -  *)
(*  pc  =  -   -   X   X   X   X  ...  X   -   -  ...  -   -   -  *)
(* -------------------------------------------------------------- *)
(*  vs  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  vc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  vt  =  -   -   -   -   -   -  ...  -   -   -  ...  -   -   X  *)
(* -------------------------------------------------------------- *)
(*  sa  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  sb  =  -   -   X   X   X   X  ...  X   -   -  ...  -   -   -  *)
(*  sc  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  sd  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(* -------------------------------------------------------------- *)
(*  ms  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  mc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  zs  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  zc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)

let montgomery_mult_def = new_definition
  `!ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc.
     montgomery_mult ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc <=>
     ?r pb ps pc pbp qb qs qc vb vs vc vt sa sb sc sd ms mc
      ld1 ld2 zs0 zs1 zs2 zc0 zc1 zc2 zc3 ps0 pc0 pb1 pbp0 pbp1 qb2
      sa0 sa1 sa2 sa3 sa4 sa5 sb0 sb1 sb2 sd0 sd1 sd2 sd3
      ms0 ms1 ms2 ms3 ms4 mc0 mc1 mc2 mc3 mc4 mw.
       width xs = d1 + d2 + r + 2 /\
       width xc = d1 + d2 + r + 2 /\
       width ys = d1 + d2 + r + 2 /\
       width yc = d1 + d2 + r + 2 /\
       width ks = d1 + d2 + r + 3 /\
       width kc = d1 + d2 + r + 3 /\
       width ns = d1 + d2 + r + 1 /\
       width nc = d1 + d2 + r + 1 /\
       width zs = d1 + d2 + r + 3 /\
       width zc = d1 + d2 + r + 3 /\
       width ps = d1 + d2 + r + 2 /\
       width pc = d1 + d2 + r + 2 /\
       width pbp = d1 + d2 + 1 /\
       width qs = d1 + d2 + r + 3 /\
       width qc = d1 + d2 + r + 3 /\
       width vs = d1 + d2 + r + 1 /\
       width vc = d1 + d2 + r + 1 /\
       width sa = d1 + d2 + r + 4 /\
       width sb = r + 3 /\
       width sc = d1 + d2 + r + 1 /\
       width sd = d1 + d2 + r + 2 /\
       width ms = d1 + d2 + r + 3 /\
       width mc = d1 + d2 + r + 3
       /\
       bsub zs 0 (d1 + d2 + 1) zs0 /\
       bsub zs (d1 + d2 + 1) (r + 1) zs1 /\
       wire zs (d1 + d2 + r + 2)  zs2 /\
       bsub zc 0 (d1 + d2) zc0 /\
       wire zc (d1 + d2) zc1 /\
       bsub zc (d1 + d2 + 1) (r + 1) zc2 /\
       wire zc (d1 + d2 + r + 2) zc3 /\
       bsub ps 0 (r + 4) ps0 /\
       bsub pc 0 (r + 3) pc0 /\
       wire pbp d1 pb1 /\
       bsub pbp 1 (d1 + d2) pbp0 /\
       brev pbp0 pbp1 /\
       bsub sa 0 (d1 + d2) sa0 /\
       bsub sa 0 (d1 + d2 + r + 1) sa1 /\
       bsub sa (d1 + d2) (r + 4) sa2 /\
       wire sa (d1 + d2 + r + 1) sa3 /\
       wire sa (d1 + d2 + r + 2) sa4 /\
       wire sa (d1 + d2 + r + 3) sa5 /\
       bsub sb 0 (r + 1) sb0 /\
       wire sb (r + 1) sb1 /\
       wire sb (r + 2) sb2 /\
       wire sd 0 sd0 /\
       bsub sd 0 (d1 + d2 + r + 1) sd1 /\
       bsub sd 1 (d1 + d2 + r + 1) sd2 /\
       wire sd (d1 + d2 + r + 1) sd3 /\
       bsub ms 0 (d1 + d2 + 1) ms0 /\
       bsub ms 0 (d1 + d2 + r + 1) ms1 /\
       bsub ms (d1 + d2 + 1) (r + 1) ms4 /\
       wire ms (d1 + d2 + r + 1) ms2 /\
       wire ms (d1 + d2 + r + 2) ms3 /\
       bsub mc 0 (d1 + d2) mc0 /\
       bsub mc 0 (d1 + d2 + r + 1) mc1 /\
       bsub mc (d1 + d2) (r + 1) mc2 /\
       wire mc (d1 + d2 + r + 1) mc3 /\
       wire mc (d1 + d2 + r + 2) mc4
       /\
       scmult ld xs xc d0 ys yc pb ps pc /\
       pipe ld (d0 + d1) ld1 /\
       bpipe pb pbp /\
       bmult ld1 pb1 ks kc qb qs qc /\
       pipe ld1 d2 ld2 /\
       pipe qb d2 qb2 /\
       bmult ld2 qb2 ns nc vb vs vc /\
       sticky ld2 vb vt /\
       bconnect pbp1 sa0 /\
       badder3 sa1 sc sd1 ms1 mc1 /\
       adder2 sa3 sd3 ms2 mc3 /\
       connect sa4 ms3 /\
       connect sa5 mc4 /\
       bconnect ms0 zs0 /\
       bconnect mc0 zc0 /\
       connect ground zc1 /\
       badder3 sb0 ms4 mc2 zs1 zc2 /\
       adder3 sb1 ms3 mc3 zs2 mw /\
       or3 sb2 mc4 mw zc3
       /\
       bdelay ps0 sa2 /\
       bdelay pc0 sb /\
       bdelay vs sc /\
       delay vt sd0 /\
       bdelay vc sd2`;;

export_thm montgomery_mult_def;;

(* --------------------------------------------- *)
(* Compress the Montgomery multiplication result *)
(* --------------------------------------------- *)
(*        r+2 r+1  r  ...  1   0                 *)
(* --------------------------------------------- *)
(*  xs  =  -   X   X  ...  X   X                 *)
(*  xc  =  X   X   X  ...  X   -                 *)
(*  rx  =  -   -   X  ...  X   X                 *)
(*  ry  =  -   -   X  ...  X   X                 *)
(*  rz  =  -   -   X  ...  X   X                 *)
(* --------------------------------------------- *)
(*  ns  =  -   X   -  ...  -   -                 *)
(*  nc  =  X   -   -  ...  -   -                 *)
(* --------------------------------------------- *)
(*  ys  =  -   -   X  ...  X   X                 *)
(*  yc  =  -   X   X  ...  X   -                 *)
(* --------------------------------------------- *)

(***
let montgomery_compress_def = new_definition
  `!xs xc d rx ry rz ys yc.
      montgomery_compress xs xc d rx ry rz ys yc <=>
      ?r nct ns nc nsd ncd rnl rnh rn
       xs0 xs1 xs2 xc0 xc1 xc2 ys0 ys1 yc0 yc1 rn0 rn1.
         width xs = r + 2 /\
         width xc = r + 2 /\
         width rx = r + 1 /\
         width ry = r + 1 /\
         width rz = r + 1 /\
         width ys = r + 1 /\
         width yc = r + 1 /\
         width rnl = r + 1 /\
         width rnh = r + 1 /\
         width rn = r + 1
         /\
         wire xs 0 xs0 /\
         bsub xs 1 r xs1 /\
         wire xs (r + 1) xs2 /\
         bsub xc 0 r xc0 /\
         wire xc r xc1 /\
         wire xc (r + 1) xc2 /\
         wire ys 0 ys0 /\
         bsub ys 1 r ys1 /\
         wire yc 0 yc0 /\
         bsub yc 1 r yc1 /\
         wire rn 0 rn0 /\
         bsub rn 1 r rn1
         /\
         adder2 xs2 xc1 ns nct /\
         or2 nct xc2 nc /\
         pipe ns d nsd /\
         pipe nc d ncd /\
         bcase1 nsd rx (bground (r + 1)) rnl /\
         bcase1 nsd rz ry rnh /\
         bcase1 ncd rnh rnl rn /\
         adder2 xs0 rn0 ys0 yc0 /\
         badder3 xs1 xc0 rn1 ys1 yc1`;;

export_thm montgomery_compress_def;;

let montgomery_circuit_def = new_definition
  `!ld nb kb rx ry rz xs xc ys yc
    zs' zc'.
      montgomery_circuit
        ld nb kb rx ry rz xs xc ys yc
        zs' zc' <=>
      ?r ps pc qs qc.
         width nb = r /\
         width kb = r /\
         width rx = r /\
         width ry = r /\
         width rz = r /\
         width xs = r /\
         width xc = r /\
         width ys = r /\
         width yc = r
         /\
         width zs' = r /\
         width zc' = r
         /\
         montgomery_loop nb kb xs xc ps pc /\
         bdelay ps qs /\
         bdelay pc qc /\
         montgomery_compress rx ry rz qs qc zs' zc'`;;

export_thm montgomery_circuit_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Correctness of a Montgomery multiplication circuit.                       *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-montgomery-thm";;

let montgomery_mult_bit_width = prove
 (`!n r k x y ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc t.
     width xs = r /\
     ~(n = 0) /\
     bit_width n <= r /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     montgomery_mult ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc ==>
     bit_width x <= r + 2 /\
     bit_width y <= r + 2 /\
     bit_width (x * y) <= (r + 2) + (r + 2) /\
     bit_width (montgomery_reduce n (2 EXP (r + 2)) k (x * y)) <= r + 2`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `r : num` THEN
  X_GEN_TAC `k : num` THEN
  X_GEN_TAC `x : num` THEN
  X_GEN_TAC `y : num` THEN
  X_GEN_TAC `ld : wire` THEN
  X_GEN_TAC `xs : bus` THEN
  X_GEN_TAC `xc : bus` THEN
  X_GEN_TAC `d0 : cycle` THEN
  X_GEN_TAC `ys : bus` THEN
  X_GEN_TAC `yc : bus` THEN
  X_GEN_TAC `d1 : cycle` THEN
  X_GEN_TAC `ks : bus` THEN
  X_GEN_TAC `kc : bus` THEN
  X_GEN_TAC `d2 : cycle` THEN
  X_GEN_TAC `ns : bus` THEN
  X_GEN_TAC `nc : bus` THEN
  X_GEN_TAC `zs : bus` THEN
  X_GEN_TAC `zc : bus` THEN
  X_GEN_TAC `t : cycle` THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [montgomery_mult_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `rs : num` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `width xs = r` MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `x < 2 EXP r + 2 EXP (r + 1)`
    ASSUME_TAC THENL
  [UNDISCH_THEN
     `bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x`
     (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC
     `2 EXP (LENGTH (bsignal xs t)) +
      2 * bits_to_num (bsignal xc t)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT_ADD_RCANCEL; bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [GSYM ADD1; EXP_SUC; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (LENGTH (bsignal xc t))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `y < 2 EXP r + 2 EXP (r + 1)`
    ASSUME_TAC THENL
  [UNDISCH_THEN
     `!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y`
     (MP_TAC o SPEC `d0 : cycle`) THEN
   ASM_REWRITE_TAC [LE_REFL; LE_ADD] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC
     `2 EXP (LENGTH (bsignal ys (t + d0))) +
      2 * bits_to_num (bsignal yc (t + d0))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT_ADD_RCANCEL; bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [GSYM ADD1; EXP_SUC; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (LENGTH (bsignal yc (t + d0)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL];
   ALL_TAC] THEN
  MATCH_MP_TAC (TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_width_upper_bound] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP r + 2 EXP (r + 1)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `2 * 2 EXP r + 2 EXP (r + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [MULT_2; GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD1; GSYM EXP_SUC; GSYM MULT_2; TWO; ADD_SUC; LE_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC (TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_width_upper_bound] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP r + 2 EXP (r + 1)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `2 * 2 EXP r + 2 EXP (r + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [MULT_2; GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD1; GSYM EXP_SUC; GSYM MULT_2; TWO; ADD_SUC; LE_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `bit_width x + bit_width y` THEN
   REWRITE_TAC [bit_width_mult] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `(r + 2) + bit_width y` THEN
   ASM_REWRITE_TAC [LE_ADD_LCANCEL; LE_ADD_RCANCEL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC (SPEC `r : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `qs : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [ADD_EQ_0; TWO; NOT_SUC];
   ALL_TAC] THEN
  MP_TAC (SPEC `qs : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `q : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [ADD_EQ_0; ADD_SUC; TWO; NOT_SUC; SUC_INJ; ONE];
   ALL_TAC] THEN
  DISCH_THEN (K ALL_TAC) THEN
  REWRITE_TAC [GSYM ADD1] THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC [TWO; GSYM ADD1; ADD_SUC] THEN
  REWRITE_TAC [GSYM TWO; bit_width_upper_bound] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `(2 EXP q + 2 EXP SUC (SUC (SUC q))) + n` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EXP_EQ_0; TWO; NOT_SUC];
    ALL_TAC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `(2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))) * y` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_MULT_RCANCEL] THEN
    DISJ1_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC
     `(2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))) *
      (2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC
     [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM EXP_ADD; ADD_SUC; SUC_ADD;
      GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC; LE_REFL];
   ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 EXP q + 2 EXP SUC (SUC (SUC q))) + 2 EXP SUC (SUC q)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LE_ADD_LCANCEL] THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM bit_width_upper_bound];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `2 EXP q + 2 EXP q + 2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))` THEN
  REWRITE_TAC [LE_ADDR] THEN
  REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `2 EXP SUC q +
     (2 EXP SUC q + 2 EXP SUC (SUC q)) + 2 EXP SUC (SUC (SUC q))` THEN
  REWRITE_TAC [LE_ADDR] THEN
  REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC; LE_REFL]);;

export_thm montgomery_mult_bit_width;;

let montgomery_mult_bits_to_num = prove
 (`!n r s k x y ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc t.
     width xs = r /\
     ~(n = 0) /\
     bit_width n <= r /\
     2 EXP (r + 2) * s = k * n + 1 /\
     (!i. i <= d1 + d2 + r + 1 ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     (!i.
        d0 + d1 <= i /\ i <= d0 + d1 + r + 1 ==>
        bits_to_num (bsignal ks (t + i)) +
        2 * bits_to_num (bsignal kc (t + i)) = k) /\
     (!i.
        d0 + d1 + d2 <= i /\ i <= d0 + d1 + d2 + r + 1 ==>
        bits_to_num (bsignal ns (t + i)) +
        2 * bits_to_num (bsignal nc (t + i)) = n) /\
     montgomery_mult ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc ==>
     bits_to_num (bsignal zs (t + d0 + d1 + d2 + r + 2)) +
     2 * bits_to_num (bsignal zc (t + d0 + d1 + d2 + r + 2)) =
     montgomery_reduce n (2 EXP (r + 2)) k (x * y)`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `r : num` THEN
  X_GEN_TAC `s : num` THEN
  X_GEN_TAC `k : num` THEN
  X_GEN_TAC `x : num` THEN
  X_GEN_TAC `y : num` THEN
  X_GEN_TAC `ld : wire` THEN
  X_GEN_TAC `xs : bus` THEN
  X_GEN_TAC `xc : bus` THEN
  X_GEN_TAC `d0 : cycle` THEN
  X_GEN_TAC `ys : bus` THEN
  X_GEN_TAC `yc : bus` THEN
  X_GEN_TAC `d1 : cycle` THEN
  X_GEN_TAC `ks : bus` THEN
  X_GEN_TAC `kc : bus` THEN
  X_GEN_TAC `d2 : cycle` THEN
  X_GEN_TAC `ns : bus` THEN
  X_GEN_TAC `nc : bus` THEN
  X_GEN_TAC `zs : bus` THEN
  X_GEN_TAC `zc : bus` THEN
  X_GEN_TAC `t : cycle` THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `r : num`;
        `k : num`;
        `x : num`;
        `y : num`;
        `ld : wire`;
        `xs : bus`;
        `xc : bus`;
        `d0 : cycle`;
        `ys : bus`;
        `yc : bus`;
        `d1 : cycle`;
        `ks : bus`;
        `kc : bus`;
        `d2 : cycle`;
        `ns : bus`;
        `nc : bus`;
        `zs : bus`;
        `zc : bus`;
        `t : cycle`]
       montgomery_mult_bit_width) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (fun th -> STRIP_TAC THEN MP_TAC th) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  REWRITE_TAC [montgomery_mult_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `rs : num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `!i.
       i <= d1 + d2 + r + 1 ==>
       bit_cons (signal pb (t + d0 + i))
         (bits_to_num (bsignal ps (t + d0 + i)) +
          2 * bits_to_num (bsignal pc (t + d0 + i))) =
       bit_shr (bit_bound x (i + 1) * y) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC scmult_bits_to_num THEN
   EXISTS_TAC `ld : wire` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `ys : bus` THEN
   EXISTS_TAC `yc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`j : cycle`;
          `i : cycle`;
          `d1 + d2 + r + 1 : cycle`]
         LE_TRANS) THEN
    ASM_REWRITE_TAC [];
    X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + d0 + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= d1 + d2 + r + 1 ==> signal pb (t + d0 + i) = bit_nth (x * y) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal pb (t + d0 + i))
           (bits_to_num (bsignal ps (t + d0 + i)) +
            2 * bits_to_num (bsignal pc (t + d0 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `bit_nth (bit_bound (bit_bound x (i + 1) * y) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= d1 + d2 + r + 1 ==>
       bits_to_num (bsignal ps (t + d0 + i)) +
       2 * bits_to_num (bsignal pc (t + d0 + i)) =
       bit_shr (bit_bound x (i + 1) * y) (i + 1)`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_tl
        (bit_cons (signal pb (t + d0 + i))
          (bits_to_num (bsignal ps (t + d0 + i)) +
           2 * bits_to_num (bsignal pc (t + d0 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_tl_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM ADD1; bit_shr_suc];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= d2 + r + 1 ==> (signal ld1 (t + d0 + d1 + i) <=> i = 0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + i : cycle) = (t + i) + (d0 + d1)`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `d0 + d1 : cycle`;
         `ld1 : wire`;
         `t + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `d2 + r + 1` THEN
   ASM_REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= d2 + r + 1 ==>
       signal pb1 (t + d0 + d1 + i) = bit_nth (x * y) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + i : cycle) = (t + d0 + i) + d1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`pb : wire`;
         `pbp : bus`;
         `d1 : cycle`;
         `pb1 : wire`;
         `t + d0 + i : cycle`]
      bpipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `d2 + r + 1` THEN
   ASM_REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bit_cons (signal qb (t + d0 + d1 + i))
         (bits_to_num (bsignal qs (t + d0 + d1 + i)) +
          2 * bits_to_num (bsignal qc (t + d0 + d1 + i))) =
       bit_shr (bit_bound (x * y) (i + 1) * k) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MATCH_MP_TAC bmult_bits_to_num THEN
   EXISTS_TAC `ld1 : wire` THEN
   EXISTS_TAC `pb1 : wire` THEN
   EXISTS_TAC `ks : bus` THEN
   EXISTS_TAC `kc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `j : cycle` THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`j : cycle`; `i : cycle`; `r + 1 : cycle`]
        LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD; LE_ADD_LCANCEL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= r + 1 ==> signal qb (t + d0 + d1 + i) = bit_nth (x * y * k) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal qb (t + d0 + d1 + i))
           (bits_to_num (bsignal qs (t + d0 + d1 + i)) +
            2 * bits_to_num (bsignal qc (t + d0 + d1 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_nth (bit_bound (bit_bound (x * y) (i + 1) * k) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; MULT_ASSOC; GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= r + 1 ==> (signal ld2 (t + d0 + d1 + d2 + i) <=> i = 0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + d2 + i : cycle) = (t + d0 + d1 + i) + d2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`ld1 : wire`;
         `d2 : cycle`;
         `ld2 : wire`;
         `t + d0 + d1 + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `r + 1` THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       signal qb2 (t + d0 + d1 + d2 + i) = bit_nth (x * y * k) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + d2 + i : cycle) = (t + d0 + d1 + i) + d2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`qb : wire`;
         `d2 : cycle`;
         `qb2 : wire`;
         `t + d0 + d1 + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bit_cons (signal vb (t + d0 + d1 + d2 + i))
         (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
          2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))) =
       bit_shr (bit_bound (x * y * k) (i + 1) * n) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MATCH_MP_TAC bmult_bits_to_num THEN
   EXISTS_TAC `ld2 : wire` THEN
   EXISTS_TAC `qb2 : wire` THEN
   EXISTS_TAC `ns : bus` THEN
   EXISTS_TAC `nc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `j : cycle` THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`j : cycle`; `i : cycle`; `r + 1 : cycle`] LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_THEN `j <= (i : cycle)` (K ALL_TAC) THEN
   UNDISCH_THEN `i <= (r + 1 : cycle)` (K ALL_TAC) THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD; LE_ADD_LCANCEL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
       2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i)) =
       bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1)`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_tl
        (bit_cons (signal vb (t + d0 + d1 + d2 + i))
          (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
           2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_tl_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM ADD1; bit_shr_suc];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       signal vb (t + d0 + d1 + d2 + i) =
       bit_nth (x * y * k * n) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal vb (t + d0 + d1 + d2 + i))
           (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
            2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_nth (bit_bound (bit_bound (x * y * k) (i + 1) * n) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT; MULT_ASSOC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       (signal vt (t + d0 + d1 + d2 + i) <=>
        ~(bit_bound (x * y * k * n) (i + 1) = 0))`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld2 : wire`;
         `vb : wire`;
         `vt : wire`;
         `t + d0 + d1 + d2 : cycle`;
         `i : cycle`]
        sticky_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   ANTS_TAC THENL
   [X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `i : cycle` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM zero_bit_nth_eq; bit_nth_bound; NOT_FORALL_THM] THEN
   REWRITE_TAC [GSYM ADD1; LT_SUC_LE] THEN
   SUBGOAL_THEN
     `(?j. j <= i /\ signal vb (t + d0 + d1 + d2 + j)) <=>
      (?j. j <= i /\ bit_nth (x * y * k * n) j)`
     ACCEPT_TAC THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   REVERSE_TAC (ASM_CASES_TAC `j <= (i : cycle)`) THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `i : cycle` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + i + 1)) +
       bit_shl
         (bits_to_num (bsignal ps (t + d0 + d1 + d2 + i)) +
          2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + i)))
         (d1 + d2) +
       (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
        2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))) +
       bit_to_num (signal vt (t + d0 + d1 + d2 + i)) =
       bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (i + 1) +
       bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1) +
       bit_to_num (~(bit_bound (x * y * k * n) (i + 1) = 0))`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_bound (bit_shr (x * y) (i + 1)) (d1 + d2) +
      bit_shl
        (bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (d1 + d2 + i + 1))
        (d1 + d2) +
      bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1) +
      bit_to_num (~(bit_bound (x * y * k * n) (i + 1) = 0))` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    MP_TAC
      (SPECL
         [`bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (i + 1)`;
          `d1 + d2 : num`]
         bit_bound) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [GSYM bit_shr_add; GSYM bit_shr_bound_add] THEN
    SUBGOAL_THEN
      `(i + 1) + (d1 + d2) = d1 + d2 + i + 1`
      SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL; GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
    REWRITE_TAC [bit_bound_bound];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN
     `!i.
        i <= d1 + d2 + r + 1 ==>
        bits_to_num (bsignal ps (t + d0 + i)) +
        2 * bits_to_num (bsignal pc (t + d0 + i)) =
        bit_shr (bit_bound x (i + 1) * y) (i + 1)`
     (MP_TAC o SPEC `d1 + d2 + i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width pbp0 = d1 + d2` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `pbp : bus` THEN
    EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width pbp1 = d1 + d2` ASSUME_TAC THENL
   [MATCH_MP_TAC brev_width_out THEN
    EXISTS_TAC `pbp0 : bus` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
       [`bit_shr (x * y) (i + 1)`;
        `pbp1 : bus`;
        `t + d0 + d1 + d2 + i + 1 : cycle`]
       bit_nth_wire_bits_to_num) THEN
   ANTS_TAC THENL
   [X_GEN_TAC `j : num` THEN
    X_GEN_TAC `pbj : wire` THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`pbp0 : bus`;
          `pbp1 : bus`;
          `j : num`;
          `pbj : wire`]
         brev_wire_out) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `jr : num` STRIP_ASSUME_TAC) THEN
    MP_TAC
      (SPECL
        [`pbp : bus`;
         `1`;
         `d1 + d2 : num`;
         `pbp0 : bus`;
         `jr : num`;
         `pbj : wire`]
        bsub_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
        [`pb : wire`;
         `pbp : bus`;
         `1 + jr : num`;
         `pbj : wire`;
         `t + d0 + j + i + 1 : cycle`]
        bpipe_signal) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `(t + d0 + j + i + 1) + 1 + jr = t + d0 + d1 + d2 + i + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     REWRITE_TAC [ADD_ASSOC] THEN
     UNDISCH_THEN `jr + j + 1 = d1 + d2` (SUBST1_TAC o SYM) THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [GSYM bit_nth_add] THEN
    SUBGOAL_THEN
      `(i + 1) + j = j + i + 1`
      SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [];
     ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `d1 + d2 + i : num` THEN
    ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    UNDISCH_THEN `jr + j + 1 = d1 + d2` (SUBST1_TAC o SYM) THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN
     `!i.
        i <= r + 1 ==>
        (signal vt (t + d0 + d1 + d2 + i) <=>
         ~(bit_bound (x * y * k * n) (i + 1) = 0))`
     (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN (MP_TAC o SPEC `r + 1`) THEN
  ASM_REWRITE_TAC [LE_REFL; GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  SUBGOAL_THEN
    `bit_bound x (d1 + d2 + r + 2) = x`
    SUBST1_TAC THENL
  [REWRITE_TAC [bit_bound_id] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `r + 2` THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `r + 2 : num`;
        `s : num`;
        `k : num`;
        `x * y : num`]
       montgomery_reduce_bits) THEN
  ASM_REWRITE_TAC [GSYM MULT_ASSOC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `!a b.
       bit_shl a (d1 + d2 + rs + 4) + b =
       montgomery_reduce n (2 EXP (r + 2)) k (x * y) <=>
       a = 0 /\ b = montgomery_reduce n (2 EXP (r + 2)) k (x * y)`
    MP_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `d1 + d2 + rs + 4 = (d1 + d2 + rs + 2) + 2` SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 2`];
    ALL_TAC] THEN
   UNDISCH_TAC `width xs = r` THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REVERSE_TAC EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [zero_bit_shl; ZERO_ADD];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC (TAUT `!x y. (x ==> y) /\ x ==> x /\ y`) THEN
   CONJ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [zero_bit_shl; ZERO_ADD];
    ALL_TAC] THEN
   UNDISCH_THEN
     `bit_width (montgomery_reduce n (2 EXP (r + 2)) k (x * y)) <= r + 2`
     (MP_TAC o SYM o REWRITE_RULE [GSYM bit_bound_id]) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`bit_shl a (r + 2) + b`; `r + 2`] bit_bound) THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC
     [EQ_ADD_LCANCEL_0; add_bit_shl; ADD_EQ_0; bit_shl_eq_zero;
      ONCE_REWRITE_RULE [ADD_SYM] add_bit_shr] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  SPEC_TAC (`montgomery_reduce n (2 EXP (r + 2)) k (x * y)`, `m : num`) THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `width ps0 = rs + 4` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ps : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC] THEN
  MP_TAC
    (SPECL
       [`ps : bus`;
        `0`;
        `rs + 4`;
        `ps0 : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [bsub_zero; ZERO_ADD; LE_0] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d : num`
       (X_CHOOSE_THEN `ps2 : bus`
          (X_CHOOSE_THEN `ps1 : bus`
             STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [bnil_bappend] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; GSYM bit_shl_add; add_bit_shl; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 4 + d1 + d2 = d1 + d2 + rs + 4` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1))) (d1 + d2) +
     bit_shl (bits_to_num (bsignal ps1 (t + d0 + d1 + d2 + r + 1)))
      (d1 + d2 + rs + 4) +
     bit_shl (2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1)) +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     bit_shl (bits_to_num (bsignal ps1 (t + d0 + d1 + d2 + r + 1)))
      (d1 + d2 + rs + 4) +
     bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1))) (d1 + d2) +
     bit_shl (2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1)) +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC
    [GSYM bit_shl_one; ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `width pc0 = rs + 3` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `pc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`pc : bus`;
        `0`;
        `rs + 3`;
        `pc0 : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [bsub_zero; ZERO_ADD; LE_0] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d : num`
       (X_CHOOSE_THEN `pc2 : bus`
          (X_CHOOSE_THEN `pc1 : bus`
             STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [bnil_bappend] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; GSYM bit_shl_add; add_bit_shl; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 3 + d1 + d2 + 1 = d1 + d2 + rs + 4` SUBST1_TAC THENL
  [REWRITE_TAC [GSYM (NUM_REDUCE_CONV `3 + 1`); ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bit_shl (bits_to_num (bsignal pc1 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + rs + 4) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     bit_shl (bits_to_num (bsignal pc1 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + rs + 4) +
     bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC
    [GSYM bit_shl_one; ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     (bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
      bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
        (d1 + d2)) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     (bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) +
      bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1)`
    SUBST1_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) =
     bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `bappend sa0 sa2 = sa` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `d1 + d2 + rs + 4 = (d1 + d2) + (rs + 4)` SUBST1_TAC THENL
    [REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bits_to_num] THEN
   MP_TAC
     (SPECL
        [`pbp1 : bus`;
         `sa0 : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bconnect_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`ps0 : bus`;
         `sa2 : bus`;
         `t + d0 + d1 + d2 + r + 1`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `sa : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`pc0 : bus`;
        `sb : bus`;
        `t + d0 + d1 + d2 + r + 1`]
       bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`vs : bus`;
        `sc : bus`;
        `t + d0 + d1 + d2 + r + 1`]
       bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 =
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `bappend (bwire sd0) sd2 = sd` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `d1 + d2 + rs + 2 = 1 + (d1 + d2 + rs + 1)` SUBST1_TAC THENL
    [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
   MP_TAC
     (SPECL
        [`vt : wire`;
         `sd0 : wire`;
         `t + d0 + d1 + d2 + r + 1`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`vc : bus`;
         `sd2 : bus`;
         `t + d0 + d1 + d2 + r + 1`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [bit_shl_one];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal sb (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2)) =
     bit_shl (bits_to_num (bsignal sb (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2)) =
     bits_to_num (bsignal ms (t + d0 + d1 + d2 + r + 2)) +
     2 * bits_to_num (bsignal mc (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `bappend sa1
        (bappend (bwire sa3) (bappend (bwire sa4) (bwire sa5))) = sa`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 4 = (d1 + d2 + rs + 1) + 1 + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 3`;
        NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def;
       NUM_REDUCE_CONV `1 + 1`; NUM_REDUCE_CONV `1 + 2`];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend sd1 (bwire sd3) = sd`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 2 = (d1 + d2 + rs + 1) + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend ms1 (bappend (bwire ms2) (bwire ms3)) = ms`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 3 = (d1 + d2 + rs + 1) + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend mc1 (bappend (bwire mc3) (bwire mc4)) = mc`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 3 = (d1 + d2 + rs + 1) + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   REWRITE_TAC
     [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
      bwire_bits_to_num; GSYM bit_shl_one] THEN
   SUBGOAL_THEN `width sa1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sa : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width sd1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sd : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width ms1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `ms : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width mc1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `mc : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   SUBGOAL_THEN `1 + d1 + d2 + rs + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
   [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   SUBGOAL_THEN `1 + d1 + d2 + rs + 2 = d1 + d2 + rs + 3` SUBST1_TAC THENL
   [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `(bits_to_num (bsignal sa1 (t + d0 + d1 + d2 + r + 2)) +
       bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
       bits_to_num (bsignal sd1 (t + d0 + d1 + d2 + r + 2))) +
      bit_shl (bit_to_num (signal sa3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal sa4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal sa5 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3) +
      bit_shl (bit_to_num (signal sd3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC)) THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sa1 : bus`;
         `sc : bus`;
         `sd1 : bus`;
         `ms1 : bus`;
         `mc1 : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_shl_one; GSYM ADD_ASSOC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bits_to_num (bsignal ms1 (t + d0 + d1 + d2 + r + 2)) +
      bit_shl (bits_to_num (bsignal mc1 (t + d0 + d1 + d2 + r + 2))) 1 +
      bit_shl (bit_to_num (signal ms2 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_shl
        (bit_to_num (signal sa3 (t + d0 + d1 + d2 + r + 2)) +
         bit_to_num (signal sd3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal sa4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal sa5 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sa3 : wire`;
         `sd3 : wire`;
         `ms2 : wire`;
         `mc3 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        adder2_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_shl
        (bit_to_num (signal ms2 (t + d0 + d1 + d2 + r + 2)) +
         2 * bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [add_bit_shl; GSYM bit_shl_one; GSYM bit_shl_add] THEN
    SUBGOAL_THEN `1 + d1 + d2 + rs + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MP_TAC
     (SPECL
        [`sa4 : wire`;
         `ms3 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        connect_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`sa5 : wire`;
         `mc4 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        connect_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend sb0 (bappend (bwire sb1) (bwire sb2)) = sb`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `rs + 3 = (rs + 1) + 1 + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC
      [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC
     [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `width sb0 = rs + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `sb : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bappend ms0 (bappend ms4 (bwire ms3)) = ms`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2 + 1) + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `width ms0 = d1 + d2 + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ms : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width ms4 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ms : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bappend mc0 (bappend mc2 (bappend (bwire mc3) (bwire mc4))) = mc`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2) + (rs + 1) + 1 + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC
      [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`;
       NUM_REDUCE_CONV `1 + 2`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  SUBGOAL_THEN `width mc0 = d1 + d2` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `mc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width mc2 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `mc : bus` THEN
   EXISTS_TAC `d1 + d2 : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `rs + 1 + d1 + d2 + 1 = d1 + d2 + rs + 2`
    SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `1 + d1 + d2 + rs + 2 = d1 + d2 + rs + 3`
    SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_shl (bits_to_num (bsignal sb0 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal sb1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bits_to_num (bsignal ms0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ms4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bits_to_num (bsignal mc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal mc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) =
     bits_to_num (bsignal ms0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal mc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl
       (bits_to_num (bsignal sb0 (t + d0 + d1 + d2 + r + 2)) +
        bits_to_num (bsignal ms4 (t + d0 + d1 + d2 + r + 2)) +
        bits_to_num (bsignal mc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl
       (bit_to_num (signal sb1 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl
       (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3)`
    SUBST1_TAC THENL
  [REWRITE_TAC [add_bit_shl; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ms0 : bus`;
        `zs0 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`mc0 : bus`;
        `zc0 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`sb0 : bus`;
        `ms4 : bus`;
        `mc2 : bus`;
        `zs1 : bus`;
        `zc2 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       badder3_bits_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`sb1 : wire`;
        `ms3 : wire`;
        `mc3 : wire`;
        `zs2 : wire`;
        `mw : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       adder3_bit_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC
    [add_bit_shl; GSYM bit_shl_one; GSYM ADD_ASSOC;
     ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     NUM_REDUCE_CONV `1 + 1`; NUM_REDUCE_CONV `2 + 1`] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal zs0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal zc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal zs1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bits_to_num (bsignal zc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 2) +
     bit_shl (bit_to_num (signal zs2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bit_shl (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) =
     bits_to_num (bsignal zs0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal zs1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal zs2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bits_to_num (bsignal zc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal zc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 2) +
     bit_shl
       (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3)`
    SUBST1_TAC THENL
  [REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
     bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)) +
     bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)) =
     bit_cons
       ((signal sb2 (t + d0 + d1 + d2 + r + 2) <=>
         signal mc4 (t + d0 + d1 + d2 + r + 2)) <=>
        signal mw (t + d0 + d1 + d2 + r + 2))
       (bit_to_num
          ((signal sb2 (t + d0 + d1 + d2 + r + 2) /\
            signal mc4 (t + d0 + d1 + d2 + r + 2)) \/
           (signal sb2 (t + d0 + d1 + d2 + r + 2) /\
            signal mw (t + d0 + d1 + d2 + r + 2)) \/
           (signal mc4 (t + d0 + d1 + d2 + r + 2) /\
            signal mw (t + d0 + d1 + d2 + r + 2))))`
    SUBST1_TAC THENL
  [BOOL_CASES_TAC `signal sb2 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mc4 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mw (t + d0 + d1 + d2 + r + 2)` THEN
   REWRITE_TAC [bit_to_num_def; bit_cons_def] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC
    [bit_cons_def; GSYM bit_shl_one; add_bit_shl;
     ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC; NUM_REDUCE_CONV `3 + 1`] THEN
  REWRITE_TAC [ADD_ASSOC] THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; bit_to_num_zero; NOT_OR_THM] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN
    `((signal sb2 (t + d0 + d1 + d2 + r + 2) <=>
       signal mc4 (t + d0 + d1 + d2 + r + 2)) <=>
      signal mw (t + d0 + d1 + d2 + r + 2)) <=>
     (signal sb2 (t + d0 + d1 + d2 + r + 2) \/
      signal mc4 (t + d0 + d1 + d2 + r + 2) \/
      signal mw (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   BOOL_CASES_TAC `signal sb2 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mc4 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mw (t + d0 + d1 + d2 + r + 2)` THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  MP_TAC
    (SPECL
       [`sb2 : wire`;
        `mc4 : wire`;
        `mw : wire`;
        `zc3 : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       or3_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `bappend zs0 (bappend zs1 (bwire zs2)) = zs`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2 + 1) + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend zc0 (bappend (bwire zc1) (bappend zc2 (bwire zc3))) = zc`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2) + 1 + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM wire_def] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `width zs0 = d1 + d2 + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zs : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zs1 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zs : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zc0 = d1 + d2` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zc2 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zc : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 1 + d1 + d2 + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN `1 + d1 + d2 + 1 = d1 + d2 + 2` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN `rs + 1 + d1 + d2 + 2 = d1 + d2 + rs + 3` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 2`];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ground`;
        `zc1 : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC
    [EQ_ADD_LCANCEL; ground_signal; bit_to_num_false; zero_bit_shl;
     ZERO_ADD]);;

export_thm montgomery_mult_bits_to_num;;

(***
let montgomery_compress_bits_to_num = prove
 (`!n r x xs xc d rx ry rz ys yc t.
     width rx = r /\
     ~(n = 0) /\
     bit_width x <= r + 1 /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     bsignal xs (t + d) = bsignal xs t /\
     bsignal xc (t + d) = bsignal xc t /\
     bits_to_num (bsignal rx (t + d)) = (2 EXP r) MOD n /\
     bits_to_num (bsignal ry (t + d)) = (2 * (2 EXP r)) MOD n /\
     bits_to_num (bsignal rz (t + d)) = (3 * (2 EXP r)) MOD n /\
     montgomery_compress xs xc d rx ry rz ys yc ==>
     (bits_to_num (bsignal ys (t + d)) +
      2 * bits_to_num (bsignal yc (t + d))) MOD n = x MOD n`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `r : num` THEN
  X_GEN_TAC `s : num` THEN
  X_GEN_TAC `k : num` THEN
  X_GEN_TAC `x : num` THEN

let montgomery_circuit = prove
 (`!n r s k x y ld nb kb rx ry rz xs xc ys yc zs' zc' t.
      ~(n = 0) /\
      (2 EXP (r + 2)) * s = k * n + 1 /\
      width nb = r /\
      (!i. i < r ==> (signal ld (t + i) <=> i = 0)) /\
      (!i.
         0 < i /\ i < r ==>
         bits_to_num (bsignal nb (t + i)) = n) /\
      (!i.
         0 < i /\ i < r ==>
         bits_to_num (bsignal kb (t + i)) = k MOD (2 EXP r)) /\
      bits_to_num (bsignal rx (t + (r + 8))) = (2 EXP r) MOD n /\
      bits_to_num (bsignal ry (t + (r + 8))) = (2 * (2 EXP r)) MOD n /\
      bits_to_num (bsignal rz (t + (r + 8))) = (3 * (2 EXP r)) MOD n /\
      (!i.
        i < r ==>
        bits_to_num (bsignal xs' (t + i)) +
        2 * bits_to_num (bsignal xc' (t + i)) = x) /\
      bits_to_num (bsignal ys' t) +
      2 * bits_to_num (bsignal yc' t) = y /\
      montgomery_circuit
        ld nb kb rx ry rz xs xc ys yc
        zs' zc' ==>
      (bits_to_num (bsignal zs' (t + (r + 8))) +
       2 * bits_to_num (bsignal zc' (t + (r + 8)))) MOD n =
      ((x * y) * s) MOD n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_circuit_def] THEN
  STRIP_TAC THEN
***)

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing hardware.                                      *)
(* ------------------------------------------------------------------------- *)

let montgomery_mult_syn_gen n =
    setify
      ((n,montgomery_mult_def) ::
       scmult_syn @
       pipe_syn @
       bpipe_syn @
       bmult_syn @
       sticky_syn @
       badder3_syn @
       adder2_syn @
       adder3_syn @
       or3_syn);;

let montgomery_mult_syn = montgomery_mult_syn_gen "montgomery";;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing verified Montgomery multiplication circuits.   *)
(* ------------------------------------------------------------------------- *)

let mk_montgomery_mult n =
    let undisch_bind th =
        let (tm,_) = dest_imp (concl th) in
        (tm, UNDISCH th) in
    let nn = mk_numeral n in
    let r_th = bit_width_conv (mk_comb (`bit_width`,nn)) in
    let rn = rand (concl r_th) in
    let r = dest_numeral rn in
    let r1 = add_num r num_1 in
    let (d0,d1,d2) =
        let d = add_num (quo_num (bit_width_num r) num_2) num_1 in
        let dn = mk_numeral d in
        (dn,dn,dn) in
    let ld = mk_var ("ld",wire_ty) in
    let xs = variable_bus "xs" r in
    let xc = variable_bus "xc" r in
    let ys = variable_bus "ys" r in
    let yc = variable_bus "yc" r in
    let zs = variable_bus "zs" r1 in
    let zc = variable_bus "zc" r1 in
    let egcd_th =
        let rtm =
            let tm0 = mk_comb (`(+) : num -> num -> num`, rn) in
            mk_comb (`(EXP) 2`, mk_comb (tm0, `2`)) in
        let rth = NUM_REDUCE_CONV rtm in
        let eth = prove_egcd (rhs (concl rth)) nn in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let sn = rand (lhs (concl egcd_th)) in
    let kn = lhand (lhand (rhs (concl egcd_th))) in
    let (ns,nc) =
        let r1 = sub_num r num_1 in
        let n1 = num_to_bits_bound r1 n in
        let n2 = div_num (sub_num n (bits_to_num n1)) num_2 in
        (bits_to_bus n1, bits_to_bus (num_to_bits_bound r1 n2)) in
    let k = dest_numeral kn in
    let (ks,kc) =
        let k1 = num_to_bits_bound r1 k in
        let k2 = div_num (sub_num k (bits_to_num k1)) num_2 in
        (bits_to_bus k1, bits_to_bus (num_to_bits_bound r1 k2)) in
    let fv_x = `x : num` in
    let fv_y = `y : num` in
    let fv_t = `t : cycle` in
    let th0 =
        SPECL
          [nn; rn; sn; kn; fv_x; fv_y; ld; xs; xc; d0; ys; yc; d1;
           ks; kc; d2; ns; nc; zs; zc; fv_t]
          montgomery_mult_bits_to_num in
    let th1 =
        let conv =
            REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th0 in
    let th2 =
        let conv =
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th1 in
    let th3 =
        let conv =
            LAND_CONV (REWR_CONV r_th) THENC
            REWR_CONV (EQT_INTRO (SPEC_ALL LE_REFL)) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th2 in
    let th4 =
        let conv =
            REWR_CONV (EQT_INTRO egcd_th) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th3 in
    let (ld_cond,th5) =
        let conv =
            RAND_CONV (ABS_CONV (LAND_CONV (RAND_CONV NUM_REDUCE_CONV))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th4) in
    let (x_cond,th6) =
        let conv = ALL_CONV in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th5) in
    let (y_cond,th7) =
        let conv =
            RAND_CONV
              (ABS_CONV (LAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th6) in
    let th8 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th7 in
    let th9 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th8 in
    let (ckt,th10) = undisch_bind th9 in
    let th11 =
        let conv =
            LAND_CONV
              (LAND_CONV
                 (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))) THENC
               RAND_CONV
                 (RAND_CONV
                    (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))))) THENC
            RAND_CONV
              (RATOR_CONV
                 (RATOR_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))) in
        CONV_RULE conv th10 in
    let th =
        (GEN fv_x o GEN fv_y o GEN fv_t o
         REWRITE_RULE [IMP_IMP; GSYM CONJ_ASSOC] o
         DISCH ld_cond o DISCH x_cond o DISCH y_cond) th11 in
    let syn = montgomery_mult_syn_gen "" in
    let primary = frees (concl th) in
    instantiate_hardware syn primary th;;

(*** Testing
let montgomery91_thm = mk_montgomery_mult (dest_numeral `91`);;
let primary = `clk : wire` :: frees (concl montgomery91_thm);;
output_string stdout (hardware_to_verilog "montgomery91" primary montgomery91_thm);;
hardware_to_verilog_file "montgomery91" primary montgomery91_thm;;
***)

(* ------------------------------------------------------------------------- *)
(* LCS35 Time Capsule Crypto-Puzzle [1].                                     *)
(*                                                                           *)
(* 1. http://people.csail.mit.edu/rivest/lcs35-puzzle-description.txt        *)
(* ------------------------------------------------------------------------- *)

(***
let time_capsule_n_def = new_definition
  `time_capsule_n =
   6314466083072888893799357126131292332363298818330841375588990772701957128924885547308446055753206513618346628848948088663500368480396588171361987660521897267810162280557475393838308261759713218926668611776954526391570120690939973680089721274464666423319187806830552067951253070082020241246233982410737753705127344494169501180975241890667963858754856319805507273709904397119733614666701543905360152543373982524579313575317653646331989064651402133985265800341991903982192844710212464887459388853582070318084289023209710907032396934919962778995323320184064522476463966355937367009369212758092086293198727008292431243681`;;

export_thm time_capsule_n_def;;

let time_capsule_t_def = new_definition
  `time_capsule_t = 79685186856218`;;

export_thm time_capsule_t_def;;

let time_capsule_z_def = new_definition
  `time_capsule_z =
   4273385266812394147070994861525419078076239304748427595531276995752128020213613672254516516003537339494956807602382848752586901990223796385882918398855224985458519974818490745795238804226283637519132355620865854807750610249277739682050363696697850022630763190035330004501577720670871722527280166278354004638073890333421755189887803390706693131249675969620871735333181071167574435841870740398493890811235683625826527602500294010908702312885095784549814408886297505226010693375643169403606313753753943664426620220505295457067077583219793772829893613745614142047193712972117251792879310395477535810302267611143659071382`;;

export_thm time_capsule_z_def;;
***)

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Natural number divisibility.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-def";;

let divides_def = new_definition
  `!(a:num) b. divides a b <=> ?c. c * a = b`;;

export_thm divides_def;;

logfile "natural-divides-thm";;

let symmetry_reduction = prove
  (`!p : num -> num -> bool.
      (!m n. p m n ==> p n m) /\
      (!m n. m <= n ==> p m n) ==>
      (!m n. p m n)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`m : num`; `n : num`] LE_CASES) THEN
   STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_THEN `!m n : num. p m n ==> p n m` MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let divides_le = prove
  (`!a b. ~(b = 0) /\ divides a b ==> a <= b`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV (GSYM ONE_MULT))) THEN
   ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
   DISJ1_TAC THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [ONE; LE_SUC_LT; LT_NZ]);;

export_thm divides_le;;

let divides_zero = prove
  (`!a. divides a 0`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [MULT]);;

export_thm divides_zero;;

let divides_one = prove
  (`!a. divides a 1 <=> a = 1`,
   REWRITE_TAC [divides_def; MULT_EQ_1; UNWIND_THM2]);;

export_thm divides_one;;

let zero_divides = prove
  (`!a. divides 0 a <=> a = 0`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def; MULT_0] THEN
   MATCH_ACCEPT_TAC EQ_SYM_EQ);;

export_thm zero_divides;;

let one_divides = prove
  (`!a. divides 1 a`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def; MULT_CLAUSES] THEN
   EXISTS_TAC `a : num` THEN
   REFL_TAC);;

export_thm one_divides;;

let divides_refl = prove
  (`!a. divides a a`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [MULT_CLAUSES]);;

export_thm divides_refl;;

let divides_refl_imp = prove
  (`!a b. a = b ==> divides a b`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [divides_refl]);;

export_thm divides_refl_imp;;

let divides_antisym = prove
  (`!a b. divides a b /\ divides b a ==> a = b`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `b = 0` THENL
   [ASM_REWRITE_TAC [zero_divides; divides_zero];
    REWRITE_TAC [divides_def] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [MULTR_EQ; MULT_ASSOC; MULT_EQ_1] THEN
    STRIP_TAC]);;

export_thm divides_antisym;;

let divides_trans = prove
  (`!a b c. divides a b /\ divides b c ==> divides a c`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   EXISTS_TAC `c'' * (c' : num)` THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_ACCEPT_TAC MULT_ASSOC);;

export_thm divides_trans;;

let divides_below_imp = prove
  (`!a b. (!c. divides c a ==> divides c b) ==> divides a b`,
   REPEAT GEN_TAC THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MATCH_ACCEPT_TAC divides_refl);;

export_thm divides_below_imp;;

let divides_below = prove
  (`!a b. (!c. divides c a ==> divides c b) <=> divides a b`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC divides_below_imp;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `a : num` THEN
    ASM_REWRITE_TAC []]);;

export_thm divides_below;;

let divides_above_imp = prove
  (`!a b. (!c. divides b c ==> divides a c) ==> divides a b`,
   REPEAT GEN_TAC THEN
   DISCH_THEN MATCH_MP_TAC THEN
   MATCH_ACCEPT_TAC divides_refl);;

export_thm divides_above_imp;;

let divides_above = prove
  (`!a b. (!c. divides b c ==> divides a c) <=> divides a b`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC divides_above_imp;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `b : num` THEN
    ASM_REWRITE_TAC []]);;

export_thm divides_above;;

let mult2_divides = prove
  (`!a b c. divides (a * b) c ==> divides b c`,
   REWRITE_TAC [divides_def] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `(c':num) * a` THEN
   ASM_REWRITE_TAC [GSYM MULT_ASSOC]);;

export_thm mult2_divides;;

let mult1_divides = prove
  (`!a b c. divides (a * b) c ==> divides a c`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   MATCH_ACCEPT_TAC mult2_divides);;

export_thm mult1_divides;;

let divides_mult2 = prove
  (`!a b c. divides a c ==> divides a (b * c)`,
   REWRITE_TAC [divides_def] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `(b:num) * c'` THEN
   ASM_REWRITE_TAC [GSYM MULT_ASSOC]);;

export_thm divides_mult2;;

let divides_mult1 = prove
  (`!a b c. divides a b ==> divides a (b * c)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   MATCH_ACCEPT_TAC divides_mult2);;

export_thm divides_mult1;;

let mult_divides_mult = prove
  (`!a b c d. divides a c /\ divides b d ==> divides (a * b) (c * d)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `c' * c'' : num` THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [GSYM MULT_ASSOC] THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC MULT_SYM);;

export_thm mult_divides_mult;;

let divides_mult_cancel = prove
  (`!a b c. divides (b * a) (c * a) <=> a = 0 \/ divides b c`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [MULT_0; divides_refl];
    ASM_REWRITE_TAC [divides_def; MULT_ASSOC; EQ_MULT_RCANCEL]]);;

export_thm divides_mult_cancel;;

let mult_divides_cancel = prove
  (`!a b c. divides (a * b) (a * c) <=> a = 0 \/ divides b c`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC divides_mult_cancel);;

export_thm mult_divides_cancel;;

let divides_add = prove
  (`!a b c. divides a b /\ divides a c ==> divides a (b + c)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   EXISTS_TAC `(c' : num) + c''` THEN
   MATCH_ACCEPT_TAC RIGHT_ADD_DISTRIB);;

export_thm divides_add;;

let divides_sub = prove
  (`!a b c. c <= b /\ divides a b /\ divides a c ==> divides a (b - c)`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_divides] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [SUB_REFL];
    REWRITE_TAC [divides_def] THEN
    STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
    STRIP_TAC THEN
    EXISTS_TAC `(c' : num) - c''` THEN
    MATCH_MP_TAC RIGHT_SUB_DISTRIB THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm divides_sub;;

let divides_div = prove
  (`!a b. ~(a = 0) ==> (divides a b <=> (b DIV a) * a = b)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [divides_def] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPECL [`a : num`; `c : num`] DIV_MULT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o ONCE_REWRITE_RULE [MULT_SYM]) THEN
    REFL_TAC;
    STRIP_TAC THEN
    EXISTS_TAC `b DIV a` THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm divides_div;;

let divides_mod = prove
  (`!a b. ~(a = 0) ==> (divides a b <=> b MOD a = 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`a : num`; `b : num`] divides_div) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`b : num`; `a : num`] DIVISION_DEF_DIV) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    UNDISCH_TAC `b DIV a * a + b MOD a = b` THEN
    ASM_REWRITE_TAC [EQ_ADD_LCANCEL_0];
    STRIP_TAC THEN
    UNDISCH_TAC `b DIV a * a + b MOD a = b` THEN
    ASM_REWRITE_TAC [ADD_0]]);;

export_thm divides_mod;;

let divides_mod_cond = prove
  (`!a b. divides a b <=> if a = 0 then b = 0 else b MOD a = 0`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_divides];
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC divides_mod THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm divides_mod_cond;;

let divides_two = prove
  (`!a. divides a 2 <=> a = 1 \/ a = 2`,
   GEN_TAC THEN
   ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC [one_divides];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `a = 2` THENL
   [ASM_REWRITE_TAC [divides_refl];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_divides; TWO; NOT_SUC];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`a : num`; `2`] divides_le) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [TWO; ONE; LE; NOT_SUC] THEN
   REPEAT (DISCH_THEN (SUBST1_TAC o EQF_INTRO)) THEN
   REWRITE_TAC []);;

export_thm divides_two;;

let two_divides = prove
  (`!a. divides 2 a <=> EVEN a`,
   GEN_TAC THEN
   REWRITE_TAC [EVEN_MOD] THEN
   MATCH_MP_TAC divides_mod THEN
   NUM_REDUCE_TAC);;

export_thm two_divides;;

let divides_three = prove
  (`!a. divides a 3 <=> a = 1 \/ a = 3`,
   GEN_TAC THEN
   ASM_CASES_TAC `a = 1` THENL
   [ASM_REWRITE_TAC [one_divides];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `a = 3` THENL
   [ASM_REWRITE_TAC [divides_refl];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `a = 2` THENL
   [ASM_REWRITE_TAC [two_divides] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_divides; THREE; NOT_SUC];
    ALL_TAC] THEN
   MP_TAC (SPECL [`a : num`; `3`] divides_le) THEN
   BOOL_CASES_TAC `divides a 3` THENL
   [ALL_TAC;
    REWRITE_TAC []] THEN
   REWRITE_TAC [NOT_IMP] THEN
   NUM_REDUCE_TAC THEN
   REWRITE_TAC [THREE; TWO; ONE; LE] THEN
   ASM_REWRITE_TAC [GSYM THREE; GSYM TWO; GSYM ONE]);;

export_thm divides_three;;

let gcd_induction = prove
  (`!p : num -> num -> bool.
      (!n. p 0 n) /\
      (!m n. n < m /\ p n m ==> p m n) /\
      (!m n. p m n ==> p m (n + m)) ==>
      (!m n. p m n)`,
   REPEAT STRIP_TAC THEN
   WF_INDUCT_TAC `(m : num) + m + n` THEN
   ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `(m : num) <= n` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    UNDISCH_THEN `!(m : num) n. p m n ==> p m (n + m)` MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LT_ADD_LCANCEL] THEN
    ASM_REWRITE_TAC [LT_ADDR; LT_NZ];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [NOT_LE] THEN
    STRIP_TAC THEN
    UNDISCH_THEN `!(m : num) n. n < m /\ p n m ==> p m n` MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    ASM_REWRITE_TAC [ADD_ASSOC; LT_ADD_RCANCEL]]);;

export_thm gcd_induction;;

let gcd_exists = prove
  (`!a b. ?g.
      divides g a /\ divides g b /\
      !c. divides c a /\ divides c b ==> divides c g`,
   MATCH_MP_TAC gcd_induction THEN
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `b : num` THEN
    REWRITE_TAC [divides_zero; divides_refl];
    EXISTS_TAC `g:num` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `g : num` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC divides_add THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `divides c ((b + a) - a)`
       (fun th -> MP_TAC th THEN REWRITE_TAC [ADD_SUB]) THEN
     MATCH_MP_TAC divides_sub THEN
     ASM_REWRITE_TAC [LE_ADDR]]]);;

export_thm gcd_exists;;

let divides_factorial = prove
  (`!a b. ~(b = 0) /\ b <= a ==> divides b (FACT a)`,
   INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [LE_ZERO] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   GEN_TAC THEN
   REWRITE_TAC [LE; FACT_SUC] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC divides_mult1 THEN
    ASM_REWRITE_TAC [divides_refl];
    MATCH_MP_TAC divides_mult2 THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm divides_factorial;;

logfile_end ();;

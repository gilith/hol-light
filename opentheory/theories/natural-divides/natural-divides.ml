(* ========================================================================= *)
(* THE DIVIDES RELATION ON NATURAL NUMBERS                                   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for the divides relation on natural numbers.              *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/natural-divides/natural-divides.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of the divides relation on natural numbers.                    *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-def";;

let divides_def = new_definition
  `!(a:num) b. divides a b <=> ?c. c * a = b`;;

export_thm divides_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the divides relation on natural numbers.                    *)
(* ------------------------------------------------------------------------- *)

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

let divides_dist = prove
 (`!a b c. divides c a /\ divides c b ==> divides c (dist a b)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [dist] THEN
  COND_CASES_TAC THENL
  [MATCH_MP_TAC divides_sub THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC divides_sub THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM NOT_LE]]);;

export_thm divides_dist;;

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

(* ------------------------------------------------------------------------- *)
(* Definition of natural number greatest common divisor.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-gcd-def";;

let (gcd_divides1,gcd_divides2,gcd_greatest_imp) =
  let def = new_specification ["gcd"]
              (REWRITE_RULE [SKOLEM_THM] gcd_exists) in
  let def = REWRITE_RULE [FORALL_AND_THM] def in
  let div1 = CONJUNCT1 def in
  let def = CONJUNCT2 def in
  let div2 = CONJUNCT1 def in
  let def = CONJUNCT2 def in
  (div1,div2,def);;

export_thm gcd_divides1;;
export_thm gcd_divides2;;
export_thm gcd_greatest_imp;;

let egcd_def =
  let exists_lemma = prove
    (`?f. !a b.
        f a b =
        if b = 0 then (a,1,0) else
        let c = a MOD b in
        if c = 0 then (b, 1, a DIV b - 1) else
        let (g,s,t) = f c (b MOD c) in
        let u = s + (b DIV c) * t in
        (g, u, t + (a DIV b) * u)`,
     MP_TAC
       ((INST_TYPE [(`:num # num # num`,`:B`)] o
         ISPEC `MEASURE (SND : num # num -> num)`) WF_REC) THEN
     ASM_REWRITE_TAC [WF_MEASURE] THEN
     DISCH_THEN
       (MP_TAC o
        SPEC `\f (a,b).
                if b = 0 then (a,1,0) else
                let c = a MOD b in
                if c = 0 then (b, 1, a DIV b - 1) else
                let (g,s,t) = f (c, b MOD c) in
                let u = s + (b DIV c) * t in
                (g, u, t + (a DIV b) * u)`) THEN
     REVERSE_TAC ANTS_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `\a b. (f : num # num -> num # num # num) (a,b)` THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC [] THEN
      POP_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV) THEN
      REWRITE_TAC [];
      ALL_TAC] THEN
     X_GEN_TAC `f : num # num -> num # num # num` THEN
     X_GEN_TAC `h : num # num -> num # num # num` THEN
     REWRITE_TAC [FORALL_PAIR_THM] THEN
     X_GEN_TAC `a : num` THEN
     X_GEN_TAC `b : num` THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC [];
      ALL_TAC] THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN (MP_TAC o SPECL [`a MOD b`; `b MOD (a MOD b)`]) THEN
     REVERSE_TAC ANTS_TAC THENL
     [DISCH_THEN (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [];
      ALL_TAC] THEN
     REWRITE_TAC [MEASURE] THEN
     MATCH_MP_TAC LT_TRANS THEN
     EXISTS_TAC `a MOD b` THEN
     CONJ_TAC THEN
     MATCH_MP_TAC DIVISION_DEF_MOD THEN
     ASM_REWRITE_TAC []) in
  new_specification ["egcd"] exists_lemma;;

export_thm egcd_def;;

let chinese_def = new_definition
  `!a b x y.
     chinese a b x y =
     let (g,s,t) = egcd a b in
     (x * (a - t) * b + y * s * a) MOD (a * b)`;;

export_thm chinese_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of natural number greatest common divisor.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-gcd-thm";;

let gcd_greatest = prove
 (`!a b c. divides c (gcd a b) <=> divides c a /\ divides c b`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `gcd a b` THEN
   ASM_REWRITE_TAC [gcd_divides1; gcd_divides2];
   MATCH_ACCEPT_TAC gcd_greatest_imp]);;

export_thm gcd_greatest;;

let gcd_divides1_imp = prove
 (`!a b c. divides b a ==> divides (gcd b c) a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_trans THEN
  EXISTS_TAC `b : num` THEN
  ASM_REWRITE_TAC [gcd_divides1]);;

export_thm gcd_divides1_imp;;

let gcd_divides2_imp = prove
 (`!a b c. divides b a ==> divides (gcd c b) a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_trans THEN
  EXISTS_TAC `b : num` THEN
  ASM_REWRITE_TAC [gcd_divides2]);;

export_thm gcd_divides2_imp;;

let gcd_unique = prove
 (`!a b g.
     divides g a /\ divides g b /\
     (!c. divides c a /\ divides c b ==> divides c g) ==>
     gcd a b = g`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_antisym THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [gcd_divides1; gcd_divides2];
   MATCH_MP_TAC gcd_greatest_imp THEN
   ASM_REWRITE_TAC []]);;

export_thm gcd_unique;;

let gcd_refl = prove
 (`!a. gcd a a = a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [divides_refl]);;

export_thm gcd_refl;;

let gcd_comm = prove
 (`!a b. gcd a b = gcd b a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [gcd_divides1; gcd_divides2] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_greatest_imp THEN
  ASM_REWRITE_TAC []);;

export_thm gcd_comm;;

let gcd_assoc = prove
 (`!a b c. gcd (gcd a b) c = gcd a (gcd b c)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_antisym THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC gcd_greatest_imp THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `gcd a b` THEN
    REWRITE_TAC [gcd_divides1];
    MATCH_MP_TAC gcd_greatest_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd a b` THEN
     REWRITE_TAC [gcd_divides1; gcd_divides2];
     REWRITE_TAC [gcd_divides2]]];
   MATCH_MP_TAC gcd_greatest_imp THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC gcd_greatest_imp THEN
    STRIP_TAC THENL
    [REWRITE_TAC [gcd_divides1];
     MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd b c` THEN
     REWRITE_TAC [gcd_divides1; gcd_divides2]];
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `gcd b c` THEN
    REWRITE_TAC [gcd_divides2]]]);;

export_thm gcd_assoc;;

let divides_gcd = prove
 (`!a b. gcd a b = a <=> divides a b`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_ACCEPT_TAC gcd_divides2;
   STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   ASM_REWRITE_TAC [divides_refl] THEN
   REPEAT STRIP_TAC]);;

export_thm divides_gcd;;

let gcd_divides = prove
 (`!a b. gcd b a = a <=> divides a b`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC divides_gcd);;

export_thm gcd_divides;;

let zero_gcd = prove
 (`!a. gcd 0 a = a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [zero_divides; divides_zero; divides_refl]);;

export_thm zero_gcd;;

let gcd_zero = prove
 (`!a. gcd a 0 = a`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [zero_divides; divides_zero; divides_refl]);;

export_thm gcd_zero;;

let gcd_is_zero = prove
 (`!a b. gcd a b = 0 <=> a = 0 /\ b = 0`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [zero_gcd];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [CONTRAPOS_THM] THEN
  STRIP_TAC THEN
  REWRITE_TAC [GSYM zero_divides] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  MATCH_ACCEPT_TAC gcd_divides1);;

export_thm gcd_is_zero;;

let one_gcd = prove
 (`!a. gcd 1 a = 1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [one_divides; divides_one; divides_refl] THEN
  REPEAT STRIP_TAC);;

export_thm one_gcd;;

let gcd_one = prove
 (`!a. gcd a 1 = 1`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC one_gcd);;

export_thm gcd_one;;

let gcd_is_one = prove
 (`!a b. (!c. divides c a /\ divides c b ==> c = 1) ==> gcd a b = 1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  ASM_REWRITE_TAC [divides_one; one_divides]);;

export_thm gcd_is_one;;

let gcd_addl = prove
 (`!a b. gcd a (a + b) = gcd a b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [gcd_divides1] THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC divides_add THEN
   REWRITE_TAC [gcd_divides1; gcd_divides2];
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_greatest_imp THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `divides c ((a + b) - a)`
     (fun th -> MP_TAC th THEN REWRITE_TAC [ADD_SUB2]) THEN
   MATCH_MP_TAC divides_sub THEN
   ASM_REWRITE_TAC [LE_ADD]]);;

export_thm gcd_addl;;

let gcd_addr = prove
 (`!a b. gcd a (b + a) = gcd a b`,
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ACCEPT_TAC gcd_addl);;

export_thm gcd_addr;;

let addl_gcd = prove
 (`!a b. gcd (b + a) b = gcd a b`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  MATCH_ACCEPT_TAC gcd_addl);;

export_thm addl_gcd;;

let addr_gcd = prove
 (`!a b. gcd (a + b) b = gcd a b`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  MATCH_ACCEPT_TAC gcd_addr);;

export_thm addr_gcd;;

let gcd_sub = prove
 (`!a b. a <= b ==> gcd a (b - a) = gcd a b`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  REWRITE_TAC [gcd_divides1] THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC divides_sub THEN
   ASM_REWRITE_TAC [gcd_divides1; gcd_divides2];
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_greatest_imp THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `divides c ((b - a) + a)` MP_TAC THENL
   [MATCH_MP_TAC divides_add THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC SUB_ADD THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm gcd_sub;;

let sub_gcd = prove
 (`!a b. b <= a ==> gcd (a - b) b = gcd a b`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  MATCH_ACCEPT_TAC gcd_sub);;

export_thm sub_gcd;;

let gcd_recursion = prove
 (`!a b.
     gcd a b =
       if a = 0 then b
       else if a <= b then gcd a (b - a)
       else gcd b a`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [zero_gcd];
   COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC gcd_sub THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_ACCEPT_TAC gcd_comm]]);;

export_thm gcd_recursion;;

let egcd_exists = prove
 (`!a b. ?s t. dist (s * a) (t * b) = gcd a b`,
  MATCH_MP_TAC gcd_induction THEN
  REPEAT STRIP_TAC THENL
  [EXISTS_TAC `0` THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [zero_gcd; ONE_MULT; ZERO_MULT; DIST_LZERO];
   EXISTS_TAC `t : num` THEN
   EXISTS_TAC `s : num` THEN
   ONCE_REWRITE_TAC [gcd_comm; DIST_SYM] THEN
   FIRST_ASSUM ACCEPT_TAC;
   EXISTS_TAC `(s : num) + t` THEN
   EXISTS_TAC `t : num` THEN
   ASM_REWRITE_TAC
     [gcd_addr; RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; DIST_RADD]]);;

export_thm egcd_exists;;

let egcd_exists_nonzero1 = prove
 (`!a b. ~(a = 0) ==> ?s t. t * b + gcd a b = s * a`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`a : num`; `b : num`] egcd_exists) THEN
  REWRITE_TAC [DIST_CASES] THEN
  STRIP_TAC THENL
  [ALL_TAC;
   EXISTS_TAC `s : num` THEN
   EXISTS_TAC `t : num` THEN
   FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] gcd_divides1) THEN
  REWRITE_TAC [divides_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `k : num` MP_TAC) THEN
  MP_TAC (SPEC `k : num` num_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [ZERO_MULT];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  EXISTS_TAC `SUC (s * (n : num))` THEN
  EXISTS_TAC `n * (t : num)` THEN
  REWRITE_TAC [SUC_MULT] THEN
  POP_ASSUM (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
  REWRITE_TAC [SUC_MULT] THEN
  REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC [GSYM MULT_ASSOC] THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC [MULT_ASSOC] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

export_thm egcd_exists_nonzero1;;

let egcd_exists_nonzero2 = prove
 (`!a b. ~(a = 0) ==> ?s t. t * b + gcd b a = s * a`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC egcd_exists_nonzero1);;

export_thm egcd_exists_nonzero2;;

let mult_gcd_cancel = prove
 (`!a b c. gcd (a * b) (a * c) = a * gcd b c`,
  GEN_TAC THEN
  MATCH_MP_TAC gcd_induction THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC [zero_gcd; MULT_0];
   ONCE_REWRITE_TAC [gcd_comm] THEN
   FIRST_ASSUM ACCEPT_TAC;
   REWRITE_TAC [gcd_addr; LEFT_ADD_DISTRIB] THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm mult_gcd_cancel;;

let gcd_mult_cancel = prove
 (`!a b c. gcd (b * a) (c * a) = gcd b c * a`,
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  ACCEPT_TAC mult_gcd_cancel);;

export_thm gcd_mult_cancel;;

let mult1_coprime = prove
 (`!a b c. gcd (a * b) c = 1 ==> gcd b c = 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM divides_one] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC gcd_greatest_imp THEN
  REWRITE_TAC [gcd_divides2] THEN
  MATCH_MP_TAC divides_mult2 THEN
  MATCH_ACCEPT_TAC gcd_divides1);;

export_thm mult1_coprime;;

let mult2_coprime = prove
 (`!a b c. gcd (b * a) c = 1 ==> gcd b c = 1`,
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  ACCEPT_TAC mult1_coprime);;

export_thm mult2_coprime;;

let coprime_mult1 = prove
 (`!a b c. gcd b (a * c) = 1 ==> gcd b c = 1`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  MATCH_ACCEPT_TAC mult1_coprime);;

export_thm coprime_mult1;;

let coprime_mult2 = prove
 (`!a b c. gcd b (c * a) = 1 ==> gcd b c = 1`,
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  ACCEPT_TAC coprime_mult1);;

export_thm coprime_mult2;;

let coprime_induction = prove
 (`!p.
     p 0 0 /\
     (!a b. gcd a b = 1 ==> p a b) /\
     (!c a b. ~(c = 0) /\ p a b ==> p (c * a) (c * b)) ==>
     !a b. p a b`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `gcd a b = 0` THENL
  [POP_ASSUM MP_TAC THEN
   REWRITE_TAC [gcd_is_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`a:num`; `b:num`] gcd_divides1) THEN
  REWRITE_TAC [divides_def] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s:num`
       (fun th -> SUBST1_TAC (SYM th) THEN ASSUME_TAC th)) THEN
  MP_TAC (SPECL [`a:num`; `b:num`] gcd_divides2) THEN
  REWRITE_TAC [divides_def] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `t:num`
       (fun th ->
          CONV_TAC (RAND_CONV (REWR_CONV (SYM th))) THEN ASSUME_TAC th)) THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  MATCH_MP_TAC gcd_is_one THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM divides_one] THEN
  MP_TAC (SPECL [`gcd a b`; `c : num`; `1`] divides_mult_cancel) THEN
  ASM_REWRITE_TAC [ONE_MULT] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC gcd_greatest_imp THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   ASM_REWRITE_TAC [divides_mult_cancel];
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   ASM_REWRITE_TAC [divides_mult_cancel]]);;

export_thm coprime_induction;;

let egcd_divides = prove
 (`!a b s t. divides (gcd a b) (dist (s * a) (t * b))`,
  MATCH_MP_TAC coprime_induction THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC [MULT_0; DIST_REFL; divides_zero];
   ASM_REWRITE_TAC [one_divides];
   REWRITE_TAC [mult_gcd_cancel; MULT_ASSOC] THEN
   CONV_TAC (RAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
   CONV_TAC (RAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
   REWRITE_TAC [GSYM MULT_ASSOC; GSYM DIST_LMUL; mult_divides_cancel] THEN
   ASM_REWRITE_TAC []]);;

export_thm egcd_divides;;

let egcd_imp_gcd = prove
 (`!a b s t g.
     dist (s * a) (t * b) = g /\ divides g a /\ divides g b ==>
     gcd a b = g`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC gcd_unique THEN
  ASM_REWRITE_TAC [] THEN
  X_GEN_TAC `c : num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC divides_trans THEN
  EXISTS_TAC `gcd a b` THEN
  ASM_REWRITE_TAC [gcd_greatest] THEN
  UNDISCH_THEN `dist (s * a) (t * b) = g` (SUBST1_TAC o SYM) THEN
  MATCH_ACCEPT_TAC egcd_divides);;

export_thm egcd_imp_gcd;;

let egcd1_imp_gcd = prove
 (`!a b s t g.
     t * b + g = s * a /\ divides g a /\ divides g b ==>
     gcd a b = g`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC egcd_imp_gcd THEN
  EXISTS_TAC `s : num` THEN
  EXISTS_TAC `t : num` THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [DIST_LADD_0]);;

export_thm egcd1_imp_gcd;;

let egcd2_imp_gcd = prove
 (`!a b s t g.
     s * a + g = t * b /\ divides g a /\ divides g b ==>
     gcd a b = g`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  MATCH_MP_TAC egcd1_imp_gcd THEN
  EXISTS_TAC `t : num` THEN
  EXISTS_TAC `s : num` THEN
  ASM_REWRITE_TAC []);;

export_thm egcd2_imp_gcd;;

let coprime_egcd = prove
 (`!a b s t. dist (s * a) (t * b) = 1 ==> gcd a b = 1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM divides_one] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  MATCH_ACCEPT_TAC egcd_divides);;

export_thm coprime_egcd;;

let square_coprime_imp = prove
 (`!a b. gcd a b = 1 ==> gcd (a * a) b = 1`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [MULT_0];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`a : num`; `b : num`] egcd_exists_nonzero1) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC coprime_egcd THEN
  EXISTS_TAC `s * s : num` THEN
  EXISTS_TAC `(t * b) * t + t + t : num` THEN
  REWRITE_TAC [DIST_CASES] THEN
  DISJ2_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(s * a) * (s * a) : num` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [GSYM MULT_ASSOC] THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC MULT_SYM;
   ALL_TAC] THEN
  FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ONE_MULT; MULT_1] THEN
  REWRITE_TAC [MULT_ASSOC; ADD_ASSOC]);;

export_thm square_coprime_imp;;

let coprime_square_imp = prove
 (`!a b. gcd b a = 1 ==> gcd b (a * a) = 1`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC square_coprime_imp);;

export_thm coprime_square_imp;;

let coprime_mult_imp = prove
 (`!a b c. gcd a b = 1 /\ gcd a c = 1 ==> gcd a (b * c) = 1`,
  GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [zero_gcd] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [MULT_1];
   ALL_TAC] THEN
  MATCH_MP_TAC coprime_induction THEN
  REPEAT STRIP_TAC THENL
  [ASM_REWRITE_TAC [MULT_0];
   REPEAT (POP_ASSUM MP_TAC) THEN
   ASM_CASES_TAC `b' = 0` THENL
   [ASM_REWRITE_TAC [MULT_0] THEN
    REPEAT STRIP_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `b = 0` THENL
   [ASM_REWRITE_TAC [ZERO_MULT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`b' : num`; `a : num`] egcd_exists_nonzero2) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPECL [`b : num`; `a : num`] egcd_exists_nonzero2) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPECL [`b : num`; `b' : num`] egcd_exists) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `x : num` (X_CHOOSE_THEN `y : num` ASSUME_TAC)) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `s : num` (X_CHOOSE_THEN `t : num` ASSUME_TAC)) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num` (X_CHOOSE_THEN `q : num` ASSUME_TAC)) THEN
   MATCH_MP_TAC coprime_egcd THEN
   EXISTS_TAC `dist (x * b * q) (y * b' * t)` THEN
   EXISTS_TAC `dist (x * p) (y * s)` THEN
   REWRITE_TAC [DIST_RMUL] THEN
   SUBGOAL_THEN
     `(x * p) * (b * b') = (x * b * q) * a + x * b : num` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(x * b) * (p * b') : num` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [MULT_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [GSYM MULT_ASSOC] THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC MULT_SYM;
     ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_1; ONE_MULT] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL; GSYM MULT_ASSOC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   SUBGOAL_THEN
     `(y * s) * (b * b') = (y * b' * t) * a + y * b' : num` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `y * (s * b) * b' : num` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [MULT_ASSOC];
     ALL_TAC] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_1; ONE_MULT] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL; GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
    REWRITE_TAC [MULT_ASSOC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM
     (STRIP_ASSUME_TAC o
      ONCE_REWRITE_RULE [ADD_SYM] o
      REWRITE_RULE [DIST_CASES]) THENL
   [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_ASSOC; DIST_RADD; DIST_DIST_SUC];
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_ASSOC; DIST_RADD] THEN
    CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV DIST_SYM))) THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV DIST_SYM))) THEN
    MATCH_ACCEPT_TAC DIST_DIST_SUC];
   UNDISCH_TAC `gcd a b = 1 /\ gcd a b' = 1 ==> gcd a (b * b') = 1` THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC coprime_mult1 THEN
     EXISTS_TAC `c : num` THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC coprime_mult1 THEN
     EXISTS_TAC `c : num` THEN
     FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   SUBGOAL_THEN `gcd (c * c) a = 1` MP_TAC THENL
   [MATCH_MP_TAC square_coprime_imp THEN
    ONCE_REWRITE_TAC [gcd_comm] THEN
    MATCH_MP_TAC coprime_mult2 THEN
    EXISTS_TAC `b : num` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`a : num`; `b * b' : num`] egcd_exists_nonzero1) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPECL [`c * c : num`; `a : num`] egcd_exists_nonzero1) THEN
   ASM_REWRITE_TAC [MULT_EQ_0] THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num` (X_CHOOSE_THEN `q : num` ASSUME_TAC)) THEN
   STRIP_TAC THEN
   MATCH_MP_TAC coprime_egcd THEN
   EXISTS_TAC `q * t * b * b' + s : num` THEN
   EXISTS_TAC `p * t : num` THEN
   REWRITE_TAC [DIST_CASES] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(q * a + 1) * (t * b * b') : num` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [RIGHT_ADD_DISTRIB; EQ_ADD_RCANCEL; ONE_MULT] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
    REWRITE_TAC [MULT_ASSOC];
    FIRST_X_ASSUM SUBST1_TAC THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC MULT_SYM]]);;

export_thm coprime_mult_imp;;

let mult_coprime_imp = prove
 (`!a b c. gcd b a = 1 /\ gcd c a = 1 ==> gcd (b * c) a = 1`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC coprime_mult_imp);;

export_thm mult_coprime_imp;;

let coprime_mult = prove
 (`!a b c. gcd a (b * c) = 1 <=> gcd a b = 1 /\ gcd a c = 1`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC coprime_mult2 THEN
    EXISTS_TAC `c : num` THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC coprime_mult1 THEN
    EXISTS_TAC `b : num` THEN
    FIRST_ASSUM ACCEPT_TAC];
   MATCH_ACCEPT_TAC coprime_mult_imp]);;

export_thm coprime_mult;;

let mult_coprime = prove
 (`!a b c. gcd (b * c) a = 1 <=> gcd b a = 1 /\ gcd c a = 1`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC coprime_mult);;

export_thm mult_coprime;;

let square_coprime = prove
 (`!a b. gcd (a * a) b = 1 <=> gcd a b = 1`,
  REWRITE_TAC [mult_coprime]);;

export_thm square_coprime;;

let coprime_square = prove
 (`!a b. gcd b (a * a) = 1 <=> gcd b a = 1`,
  REWRITE_TAC [coprime_mult]);;

export_thm coprime_square;;

let coprime_gcd_mult2 = prove
 (`!a b c. gcd a b = 1 ==> gcd a (b * c) = gcd a c`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  GEN_TAC THEN
  MATCH_MP_TAC coprime_induction THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC [MULT_0];
   ASM_REWRITE_TAC [coprime_mult];
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV MULT_ASSOC))) THEN
   CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
   REWRITE_TAC [GSYM MULT_ASSOC; mult_gcd_cancel] THEN
   AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC mult1_coprime THEN
   EXISTS_TAC `c : num` THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm coprime_gcd_mult2;;

let coprime_gcd_mult1 = prove
 (`!a b c. gcd a b = 1 ==> gcd a (c * b) = gcd a c`,
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  ACCEPT_TAC coprime_gcd_mult2);;

export_thm coprime_gcd_mult1;;

let coprime_mult1_gcd = prove
 (`!a b c. gcd b a = 1 ==> gcd (c * b) a = gcd c a`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC coprime_gcd_mult1);;

export_thm coprime_mult1_gcd;;

let coprime_mult2_gcd = prove
 (`!a b c. gcd b a = 1 ==> gcd (b * c) a = gcd c a`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC coprime_gcd_mult2);;

export_thm coprime_mult2_gcd;;

let coprime_mult_divides = prove
 (`!a b c. gcd b c = 1 /\ divides b a /\ divides c a ==> divides (b * c) a`,
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `divides b a`
    (X_CHOOSE_THEN `k:num` SUBST_VAR_TAC o
     ONCE_REWRITE_RULE [MULT_SYM] o
     REWRITE_RULE [divides_def]) THEN
  REWRITE_TAC [mult_divides_cancel] THEN
  ASM_CASES_TAC `b = 0` THEN
  ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `divides c (b * k)` THEN
  REWRITE_TAC [GSYM divides_gcd] THEN
  DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC coprime_gcd_mult2 THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm coprime_mult_divides;;

let divides_gcd_mult = prove
 (`!a b c. divides (gcd a (b * c)) (gcd a b * gcd a c)`,
  MATCH_MP_TAC coprime_induction THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [zero_gcd; ZERO_MULT; divides_refl];
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [ONE_MULT] THEN
   MATCH_MP_TAC divides_refl_imp THEN
   MATCH_MP_TAC coprime_gcd_mult2 THEN
   FIRST_ASSUM ACCEPT_TAC;
   X_GEN_TAC `k : num` THEN
   X_GEN_TAC `a : num` THEN
   X_GEN_TAC `b : num` THEN
   STRIP_TAC THEN
   X_GEN_TAC `c : num` THEN
   ASM_REWRITE_TAC [mult_gcd_cancel; GSYM MULT_ASSOC; mult_divides_cancel] THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `gcd a b * gcd a c` THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [mult_divides_cancel] THEN
   DISJ2_TAC THEN
   REWRITE_TAC [gcd_greatest; gcd_divides2] THEN
   MATCH_MP_TAC divides_mult2 THEN
   MATCH_ACCEPT_TAC gcd_divides1]);;

export_thm divides_gcd_mult;;

let gcd_mod = prove
 (`!a b. ~(a = 0) ==> gcd a (b MOD a) = gcd a b`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`b : num`; `a : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
  SPEC_TAC (`b MOD a`, `c : num`) THEN
  GEN_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  SPEC_TAC (`b DIV a`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ZERO_MULT; ZERO_ADD];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [ONCE_REWRITE_RULE [ADD_SYM] SUC_MULT; GSYM ADD_ASSOC; gcd_addl]);;

export_thm gcd_mod;;

let egcd_induction = prove
 (`!p.
     (!a. p a 0) /\
     (!a b. ~(b = 0) /\ divides b a ==> p a b) /\
     (!a b c.
        ~(b = 0) /\ c = a MOD b /\ ~(c = 0) /\ p c (b MOD c) ==> p a b) ==>
     !a b. p a b`,
  GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC (ISPEC `MEASURE (SND : num # num -> num)` WF_IND) THEN
  REWRITE_TAC [WF_MEASURE] THEN
  DISCH_THEN (MP_TAC o SPEC `\(a,b). (p : num -> num -> bool) a b`) THEN
  REWRITE_TAC [FORALL_PAIR_THM] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `a : num` THEN
  X_GEN_TAC `b : num` THEN
  ASM_CASES_TAC `b = 0` THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_CASES_TAC `a MOD b = 0` THENL
  [DISCH_THEN (K ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPECL [`b : num`; `a : num`] divides_mod) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [IMP_IMP];
   ALL_TAC] THEN
  DISCH_THEN (MP_TAC o SPECL [`a MOD b`; `b MOD (a MOD b)`]) THEN
  ANTS_TAC THENL
  [REWRITE_TAC [MEASURE] THEN
   MATCH_MP_TAC LT_TRANS THEN
   EXISTS_TAC `a MOD b` THEN
   CONJ_TAC THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `a MOD b` THEN
  ASM_REWRITE_TAC []);;

export_thm egcd_induction;;

let egcd_zero = prove
 (`!a. egcd a 0 = (a,1,0)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  REWRITE_TAC []);;

export_thm egcd_zero;;

let zero_egcd = prove
 (`!b. FST (egcd 0 b) = b`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  ASM_CASES_TAC `b = 0` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPEC `b : num` MOD_0) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [egcd_zero; LET_DEF; LET_END_DEF]);;

export_thm zero_egcd;;

let egcd_one = prove
 (`!a. ~(a = 0) ==> egcd a 1 = (1, 1, a - 1)`,
  GEN_TAC THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  REWRITE_TAC [NUM_REDUCE_CONV `1 = 0`; MOD_1; DIV_1; LET_DEF; LET_END_DEF]);;

export_thm egcd_one;;

let one_egcd = prove
 (`!b. egcd 1 b = (1,1,0)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 1` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [MOD_1; LET_DEF; LET_END_DEF; DIV_1; SUB_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `1 < b` ASSUME_TAC THENL
  [POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `b : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `n : num` SUBST1_TAC) THEN
   REWRITE_TAC [ONE; SUC_INJ; LT_SUC; LT_NZ];
   ALL_TAC] THEN
  SUBGOAL_THEN `1 MOD b = 1` SUBST1_TAC THENL
  [MATCH_MP_TAC MOD_LT THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC
     [LET_DEF; LET_END_DEF; NUM_REDUCE_CONV `1 = 0`; MOD_1; egcd_zero;
      MULT_0; ADD_0; ZERO_ADD; MULT_1; PAIR_EQ] THEN
  MATCH_MP_TAC DIV_LT THEN
  ASM_REWRITE_TAC []);;

export_thm one_egcd;;

let egcd_gcd = prove
 (`!a b. FST (egcd a b) = gcd a b`,
  MATCH_MP_TAC egcd_induction THEN
  CONJ_TAC THENL
  [REWRITE_TAC [egcd_zero; gcd_zero];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [egcd_def] THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   REVERSE_TAC COND_CASES_TAC THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    MP_TAC (SPECL [`b : num`; `a : num`] divides_mod) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_SYM THEN
   ASM_REWRITE_TAC [gcd_divides];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_THEN `c = a MOD b` (STRIP_ASSUME_TAC o SYM) THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  UNDISCH_TAC `FST (egcd c (b MOD c)) = gcd c (b MOD c)` THEN
  MP_TAC (ISPEC `egcd c (b MOD c)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [EXISTS_PAIR_THM] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `g : num`
      (X_CHOOSE_THEN `s : num`
        (X_CHOOSE_THEN `t : num` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `gcd c b` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC gcd_mod THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [gcd_comm] THEN
  POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
  MATCH_MP_TAC gcd_mod THEN
  ASM_REWRITE_TAC []);;

export_thm egcd_gcd;;

let egcd_nonzero = prove
 (`!a b g s t. ~(a = 0) /\ egcd a b = (g,s,t) ==> t * b + g = s * a`,
  MATCH_MP_TAC egcd_induction THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [egcd_zero; MULT_0; ZERO_ADD; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [ONE_MULT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [egcd_def] THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [divides_mod_cond] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [ONE_MULT] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(a DIV b) * b` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC [GSYM SUC_MULT; EQ_MULT_RCANCEL; ADD1] THEN
    MATCH_MP_TAC SUB_ADD THEN
    REWRITE_TAC [ONE; LE_SUC_LT; LT_NZ] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`a : num`; `b : num`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [ZERO_MULT; ADD_0];
    ALL_TAC] THEN
   MP_TAC (SPECL [`a : num`; `b : num`] DIVISION_DEF_DIV) THEN
   ASM_REWRITE_TAC [ADD_0];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  UNDISCH_THEN `c = a MOD b` (STRIP_ASSUME_TAC o SYM) THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `egcd c (b MOD c)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [EXISTS_PAIR_THM] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `g' : num`
      (X_CHOOSE_THEN `s' : num`
        (X_CHOOSE_THEN `t' : num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`g' : num`; `s' : num`; `t' : num`]) THEN
  ASM_REWRITE_TAC [PAIR_EQ] THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM)))) THEN
  REWRITE_TAC [RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  MP_TAC (SPECL [`b : num`; `c : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (CONV_TAC o LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV o
     REWR_CONV o SYM) THEN
  ASM_REWRITE_TAC [LEFT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_ASSOC] THEN
  CONV_TAC (RAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
  ASM_REWRITE_TAC [EQ_ADD_LCANCEL; RIGHT_ADD_DISTRIB; EQ_MULT_RCANCEL] THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

export_thm egcd_nonzero;;

let egcd_bound = prove
 (`!a b g s t. ~(a = 0) /\ egcd a b = (g,s,t) ==> s < MAX b 2 /\ t < a`,
  MATCH_MP_TAC egcd_induction THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [egcd_zero; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   NUM_REDUCE_TAC THEN
   ASM_REWRITE_TAC [LT_NZ];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [egcd_def] THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [divides_mod_cond] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT_MAX] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   CONV_TAC (REWR_CONV (GSYM (SPEC `1` LT_ADD_RCANCEL))) THEN
   MP_TAC (SPECL [`a DIV b`; `1`] SUB_ADD) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [ONE; LE_SUC_LT; LT_NZ] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`a : num`; `b : num`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [ZERO_MULT; ADD_0];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `a : num` THEN
   REWRITE_TAC [GSYM ADD1; SUC_LT] THEN
   MATCH_MP_TAC DIV_LE THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  UNDISCH_THEN `c = a MOD b` (STRIP_ASSUME_TAC o SYM) THEN
  ONCE_REWRITE_TAC [egcd_def] THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `egcd c (b MOD c)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [EXISTS_PAIR_THM] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `g' : num`
      (X_CHOOSE_THEN `s' : num`
        (X_CHOOSE_THEN `t' : num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`g' : num`; `s' : num`; `t' : num`]) THEN
  ASM_REWRITE_TAC [PAIR_EQ] THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ASM_CASES_TAC `b = 1` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `a MOD b = c` THEN
   ASM_REWRITE_TAC [MOD_1];
   ALL_TAC] THEN
  SUBGOAL_THEN `1 < b` ASSUME_TAC THENL
  [POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `b : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `n : num` SUBST1_TAC) THEN
   REWRITE_TAC [ONE; SUC_INJ; LT_SUC; LT_NZ];
   ALL_TAC] THEN
  SUBGOAL_THEN `MAX b 2 = b` SUBST1_TAC THENL
  [ONCE_REWRITE_TAC [MAX_COMM] THEN
   ASM_REWRITE_TAC [MAX; LE_SUC_LT; TWO];
   ALL_TAC] THEN
  SUBGOAL_THEN `s < (b : num)` ASSUME_TAC THENL
  [MP_TAC (SPECL [`b : num`; `c : num`] DIVISION_DEF_DIV) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   UNDISCH_TAC `s' < MAX (b MOD c) 2` THEN
   ONCE_REWRITE_TAC [MAX_COMM] THEN
   REWRITE_TAC [MAX] THEN
   COND_CASES_TAC THENL
   [STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `b MOD c + b DIV c * t'` THEN
    ASM_REWRITE_TAC [LT_ADD_RCANCEL; LE_ADD_LCANCEL; LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LE; TWO; LT_SUC_LE]) THEN
   ASM_CASES_TAC `b DIV c = 0` THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `1 < b` THEN
    REWRITE_TAC [NOT_LT] THEN
    MP_TAC (SPECL [`b : num`; `c : num`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
    ASM_REWRITE_TAC [ZERO_MULT; ZERO_ADD];
    ALL_TAC] THEN
   UNDISCH_TAC `egcd c (b MOD c) = g,s',t'` THEN
   UNDISCH_THEN `b MOD c <= 1`
     (STRIP_ASSUME_TAC o REWRITE_RULE [GSYM ONE] o REWRITE_RULE [ONE; LE]) THENL
   [MP_TAC (SPEC `c : num` egcd_one) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (K ALL_TAC)
         (CONJUNCTS_THEN (SUBST1_TAC o SYM))) THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL; LT_MULT_LCANCEL] THEN
    MP_TAC (SPEC `c : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [SUC_SUB1; SUC_LT];
    MP_TAC (SPEC `c : num` egcd_zero) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [PAIR_EQ] THEN
    DISCH_THEN
      (CONJUNCTS_THEN2 (K ALL_TAC)
         (CONJUNCTS_THEN (SUBST1_TAC o SYM))) THEN
    REWRITE_TAC [MULT_0; ADD_0; ZERO_ADD] THEN
    MP_TAC (SPECL [`b : num`; `c : num`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [ADD_0] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `c + a DIV b * s` THEN
  ASM_REWRITE_TAC [LT_ADD_RCANCEL] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `c + a DIV b * b` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LE_ADD_LCANCEL; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] DIVISION_DEF_DIV) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [LE_REFL]);;

export_thm egcd_bound;;

let egcd_cases = prove
 (`!a b.
     ~(a = 0) ==>
     ?s t. egcd a b = (gcd a b, s, t) /\ t * b + gcd a b = s * a`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPEC `egcd a b` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [EXISTS_PAIR_THM] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `g : num`
      (X_CHOOSE_THEN `s : num`
        (X_CHOOSE_THEN `t : num` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `s : num` THEN
  EXISTS_TAC `t : num` THEN
  ASM_REWRITE_TAC [PAIR_EQ] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] egcd_gcd) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [] THEN
  MATCH_MP_TAC egcd_nonzero THEN
  ASM_REWRITE_TAC []);;

export_thm egcd_cases;;

let chinese_remainder = prove
 (`!a b x y n.
     gcd a b = 1 /\ x < a /\ y < b /\ chinese a b x y = n ==>
     n MOD a = x /\ n MOD b = y`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC [chinese_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] egcd_cases) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num`
       (X_CHOOSE_THEN `t : num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  CONJ_TAC THENL
  [MP_TAC
     (SPECL [`x * (a - t) * b + y * s * a : num`; `a : num`; `b : num`]
        MOD_MOD) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [MULT_EQ_0];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPEC `a : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) THEN
   MP_TAC (SPEC `a : num` (ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [MULT_ASSOC; th]) THEN
   REWRITE_TAC [GSYM MULT_ASSOC; ADD_0] THEN
   SUBGOAL_THEN `(a - t) * b = 1 + a * (b - s)` SUBST1_TAC THENL
   [SUBGOAL_THEN `t < (a : num)` ASSUME_TAC THENL
    [MP_TAC
       (SPECL [`a : num`; `b : num`; `1`; `s : num`; `t : num`]
          egcd_bound) THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC;
     ALL_TAC] THEN
    MP_TAC (SPECL [`a : num`; `t : num`; `b : num`] RIGHT_SUB_DISTRIB) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC LT_IMP_LE THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(t : num) * b < a * b` ASSUME_TAC THENL
    [ASM_REWRITE_TAC [LT_MULT_RCANCEL];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(a * b + 1) - (t * b + 1)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC SUB_ADD_RCANCEL THEN
     MATCH_MP_TAC LT_IMP_LE THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `t * b + 1 < b * a + 1` MP_TAC THENL
    [CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
     ASM_REWRITE_TAC [LT_ADD_RCANCEL];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC_LE; LE_MULT_RCANCEL] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `d : num` SUBST1_TAC o
       REWRITE_RULE [LE_EXISTS]) THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV MULT_SYM))) THEN
    REWRITE_TAC [ADD1; LEFT_ADD_DISTRIB; GSYM ADD_ASSOC; ADD_SUB2] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
   MP_TAC (SPEC `a : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV o GSYM) THEN
   SUBGOAL_THEN `(x * a * (b - s)) MOD a = 0` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MATCH_MP_TAC MOD_MULT THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPEC `a : num` MOD_MOD_REFL') THEN
   ASM_REWRITE_TAC [ADD_0] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MATCH_MP_TAC MOD_LT THEN
   ASM_REWRITE_TAC [];
   MP_TAC
     (SPECL [`x * (a - t) * b + y * s * a : num`; `b : num`; `a : num`]
        (ONCE_REWRITE_RULE [MULT_SYM] MOD_MOD)) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [MULT_EQ_0];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPEC `b : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) THEN
   MP_TAC (SPEC `b : num` (ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [MULT_ASSOC; th]) THEN
   REWRITE_TAC [GSYM MULT_ASSOC; ZERO_ADD] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
   MP_TAC (SPEC `b : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV o GSYM) THEN
   MP_TAC (SPEC `b : num` (ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [MULT_ASSOC; th]) THEN
   MP_TAC (SPEC `b : num` MOD_MOD_REFL') THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MATCH_MP_TAC MOD_LT THEN
   ASM_REWRITE_TAC []]);;

export_thm chinese_remainder;;

let chinese_bound = prove
 (`!a b x y. x < a /\ y < b ==> chinese a b x y < a * b`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [chinese_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (SPECL [`a : num`; `b : num`] egcd_cases) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num`
       (X_CHOOSE_THEN `t : num` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC DIVISION_DEF_MOD THEN
  ASM_REWRITE_TAC [MULT_EQ_0]);;

export_thm chinese_bound;;

let chinese_src = prove
 (`!a b.
     chinese a b =
     let (g,s,t) = egcd a b in
     let ab = a * b in
     let sa = s * a in
     let tb = (a - t) * b in
     \x y. (x * tb + y * sa) MOD ab`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `x : num` THEN
  X_GEN_TAC `y : num` THEN
  REWRITE_TAC [chinese_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `egcd a b` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [EXISTS_PAIR_THM] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm chinese_src;;

let egcd_divides1_test = prove
 (`!a b. divides (FST (egcd a b)) a`,
  REWRITE_TAC [egcd_gcd; gcd_divides1]);;

export_thm egcd_divides1_test;;

let egcd_divides2_test = prove
 (`!a b. divides (FST (egcd a b)) b`,
  REWRITE_TAC [egcd_gcd; gcd_divides2]);;

export_thm egcd_divides2_test;;

let egcd_nonzero_test = prove
 (`!ap b. let a = ap + 1 in let (g,s,t) = egcd a b in t * b + g = s * a`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`ap + 1`; `b : num`] egcd_cases) THEN
  REWRITE_TAC [GSYM ADD1; NOT_SUC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF]);;

export_thm egcd_nonzero_test;;

let egcd_bound1_test = prove
 (`!ap b. let a = ap + 1 in let (g,s,t) = egcd a b in s < MAX b 2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`ap + 1`; `b : num`] egcd_cases) THEN
  REWRITE_TAC [GSYM ADD1; NOT_SUC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MP_TAC
    (SPECL [`SUC ap`; `b : num`; `gcd (SUC ap) b`; `s : num`; `t : num`]
       egcd_bound) THEN
  ASM_REWRITE_TAC [NOT_SUC] THEN
  STRIP_TAC);;

export_thm egcd_bound1_test;;

let egcd_bound2_test = prove
 (`!ap b. let a = ap + 1 in let (g,s,t) = egcd a b in t < a`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`ap + 1`; `b : num`] egcd_cases) THEN
  REWRITE_TAC [GSYM ADD1; NOT_SUC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MP_TAC
    (SPECL [`SUC ap`; `b : num`; `gcd (SUC ap) b`; `s : num`; `t : num`]
       egcd_bound) THEN
  ASM_REWRITE_TAC [NOT_SUC] THEN
  STRIP_TAC);;

export_thm egcd_bound2_test;;

let chinese_remainder1_test = prove
 (`!ap bp xp yp.
     let aq = ap + 1 in
     let bq = bp + 1 in
     let g = FST (egcd aq bq) in
     let a = aq DIV g in
     let b = bq DIV g in
     let x = xp MOD a in
     let y = yp MOD b in
     chinese a b x y MOD a = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [egcd_gcd] THEN
  REPEAT LET_TAC THEN
  MP_TAC
    (SPECL [`a : num`; `b : num`; `x : num`; `y : num`; `chinese a b x y`]
       chinese_remainder) THEN
  REVERSE_TAC ANTS_TAC THENL
  [STRIP_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [] THEN
  ASM_CASES_TAC `g = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `gcd aq bq = g` THEN
   ASM_REWRITE_TAC [gcd_is_zero] THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MP_TAC (SPECL [`gcd a b`; `1`; `g : num`] EQ_MULT_RCANCEL) THEN
   ASM_REWRITE_TAC [ONE_MULT] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM gcd_mult_cancel] THEN
   MP_TAC (SPECL [`g : num`; `aq : num`] divides_div) THEN
   MP_TAC (SPECL [`g : num`; `bq : num`] divides_div) THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   ASM_REWRITE_TAC [gcd_divides1; gcd_divides2] THEN
   DISCH_THEN SUBST1_TAC THEN
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `a = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `aq DIV g = a` THEN
   MP_TAC (SPECL [`aq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides1];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `bq DIV g = b` THEN
   MP_TAC (SPECL [`bq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides2];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [UNDISCH_THEN `xp MOD a = x` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   UNDISCH_THEN `yp MOD b = y` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC []]);;

export_thm chinese_remainder1_test;;

let chinese_remainder2_test = prove
 (`!ap bp xp yp.
     let aq = ap + 1 in
     let bq = bp + 1 in
     let g = FST (egcd aq bq) in
     let a = aq DIV g in
     let b = bq DIV g in
     let x = xp MOD a in
     let y = yp MOD b in
     chinese a b x y MOD b = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [egcd_gcd] THEN
  REPEAT LET_TAC THEN
  MP_TAC
    (SPECL [`a : num`; `b : num`; `x : num`; `y : num`; `chinese a b x y`]
       chinese_remainder) THEN
  REVERSE_TAC ANTS_TAC THENL
  [STRIP_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [] THEN
  ASM_CASES_TAC `g = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `gcd aq bq = g` THEN
   ASM_REWRITE_TAC [gcd_is_zero] THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MP_TAC (SPECL [`gcd a b`; `1`; `g : num`] EQ_MULT_RCANCEL) THEN
   ASM_REWRITE_TAC [ONE_MULT] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM gcd_mult_cancel] THEN
   MP_TAC (SPECL [`g : num`; `aq : num`] divides_div) THEN
   MP_TAC (SPECL [`g : num`; `bq : num`] divides_div) THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   ASM_REWRITE_TAC [gcd_divides1; gcd_divides2] THEN
   DISCH_THEN SUBST1_TAC THEN
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `a = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `aq DIV g = a` THEN
   MP_TAC (SPECL [`aq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides1];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `bq DIV g = b` THEN
   MP_TAC (SPECL [`bq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides2];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [UNDISCH_THEN `xp MOD a = x` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   UNDISCH_THEN `yp MOD b = y` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC []]);;

export_thm chinese_remainder2_test;;

let chinese_bound_test = prove
 (`!ap bp xp yp.
     let aq = ap + 1 in
     let bq = bp + 1 in
     let g = FST (egcd aq bq) in
     let a = aq DIV g in
     let b = bq DIV g in
     let x = xp MOD a in
     let y = yp MOD b in
     chinese a b x y < a * b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [egcd_gcd] THEN
  REPEAT LET_TAC THEN
  MP_TAC
    (SPECL [`a : num`; `b : num`; `x : num`; `y : num`] chinese_bound) THEN
  REVERSE_TAC ANTS_TAC THENL
  [STRIP_TAC;
   ALL_TAC] THEN
  ASM_CASES_TAC `g = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `gcd aq bq = g` THEN
   ASM_REWRITE_TAC [gcd_is_zero] THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`];
   ALL_TAC] THEN
  ASM_CASES_TAC `a = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `aq DIV g = a` THEN
   MP_TAC (SPECL [`aq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides1];
   ALL_TAC] THEN
  ASM_CASES_TAC `b = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `bq DIV g = b` THEN
   MP_TAC (SPECL [`bq : num`; `g : num`] DIV_EQ_0) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC divides_le THEN
   REWRITE_TAC [ADD_EQ_0; NUM_REDUCE_CONV `1 = 0`; gcd_divides2];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [UNDISCH_THEN `xp MOD a = x` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC [];
   UNDISCH_THEN `yp MOD b = y` (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   ASM_REWRITE_TAC []]);;

export_thm chinese_bound_test;;

(* ------------------------------------------------------------------------- *)
(* Definition of natural number least common multiple.                       *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-lcm-def";;

let (zero_lcm,lcm_gcd) =
  let def = new_definition
    `!a b. lcm a b = if a = 0 then 0 else (a * b) DIV (gcd a b)` in
  let zero = prove
    (`!a. lcm 0 a = 0`,
     REWRITE_TAC [def])
  and mult = prove
    (`!a b. lcm a b * gcd a b = a * b`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC [def] THEN
     ASM_CASES_TAC `a = 0` THENL
     [ASM_REWRITE_TAC [ZERO_MULT];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `~(gcd a b = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC [gcd_is_zero];
      ALL_TAC] THEN
     MP_TAC (SPECL [`gcd a b`; `a * (b:num)`] divides_div) THEN
     ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC divides_mult1 THEN
     MATCH_ACCEPT_TAC gcd_divides1) in
  (zero,mult);;

export_thm zero_lcm;;
export_thm lcm_gcd;;

(* ------------------------------------------------------------------------- *)
(* Properties of natural number least common multiple.                       *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-lcm-thm";;

let lcm_comm = prove
 (`!a b. lcm a b = lcm b a`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `gcd a b = 0` THENL
  [POP_ASSUM MP_TAC THEN
   REWRITE_TAC [gcd_is_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [zero_lcm];
   MP_TAC (SPECL [`lcm a b`; `lcm b a`; `gcd a b`] EQ_MULT_RCANCEL) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV gcd_comm))) THEN
   REWRITE_TAC [lcm_gcd] THEN
   MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm lcm_comm;;

let lcm_zero = prove
 (`!a. lcm a 0 = 0`,
  ONCE_REWRITE_TAC [lcm_comm] THEN
  ACCEPT_TAC zero_lcm);;

export_thm lcm_zero;;

let divides_lcm1 = prove
 (`!a b. divides a (lcm a b)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a = 0` THENL
  [ASM_REWRITE_TAC [divides_zero; zero_lcm];
   ALL_TAC] THEN
  SUBGOAL_THEN `~(gcd a b = 0)` ASSUME_TAC THENL
  [ASM_REWRITE_TAC [gcd_is_zero];
   ALL_TAC] THEN
  MP_TAC (SPECL [`gcd a b`; `a : num`; `lcm a b`] divides_mult_cancel) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [lcm_gcd] THEN
  MATCH_MP_TAC mult_divides_mult THEN
  REWRITE_TAC [gcd_divides2; divides_refl]);;

export_thm divides_lcm1;;

let divides_lcm2 = prove
 (`!a b. divides b (lcm a b)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [lcm_comm] THEN
  MATCH_ACCEPT_TAC divides_lcm1);;

export_thm divides_lcm2;;

let divides_lcm1_imp = prove
 (`!a b c. divides a b ==> divides a (lcm b c)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_trans THEN
  EXISTS_TAC `b : num` THEN
  ASM_REWRITE_TAC [divides_lcm1]);;

export_thm divides_lcm1_imp;;

let divides_lcm2_imp = prove
 (`!a b c. divides a b ==> divides a (lcm c b)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_trans THEN
  EXISTS_TAC `b : num` THEN
  ASM_REWRITE_TAC [divides_lcm2]);;

export_thm divides_lcm2_imp;;

let mult_lcm_cancel = prove
 (`!a b c. lcm (a * b) (a * c) = a * lcm b c`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `a * gcd b c = 0` THENL
  [POP_ASSUM MP_TAC THEN
   REWRITE_TAC [MULT_EQ_0; gcd_is_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [ZERO_MULT; lcm_zero; MULT_0];
   MP_TAC (SPECL [`lcm (a * b) (a * c)`; `a * lcm b c`; `a * gcd b c`]
                 EQ_MULT_RCANCEL) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM mult_gcd_cancel)))) THEN
   REWRITE_TAC [lcm_gcd] THEN
   REWRITE_TAC [GSYM MULT_ASSOC] THEN
   AP_TERM_TAC THEN
   CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV MULT_SYM))) THEN
   REWRITE_TAC [MULT_ASSOC; lcm_gcd] THEN
   REWRITE_TAC [GSYM MULT_ASSOC] THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm mult_lcm_cancel;;

let lcm_mult_cancel = prove
 (`!a b c. lcm (b * a) (c * a) = lcm b c * a`,
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  ACCEPT_TAC mult_lcm_cancel);;

export_thm lcm_mult_cancel;;

let lcm_least_imp = prove
 (`!a b c. divides a c /\ divides b c ==> divides (lcm a b) c`,
  MATCH_MP_TAC coprime_induction THEN
  REPEAT STRIP_TAC THENL
  [ASM_REWRITE_TAC [lcm_zero];
   MP_TAC (SPECL [`gcd a b`; `lcm a b`; `c : num`] divides_mult_cancel) THEN
   REWRITE_TAC [lcm_gcd] THEN
   ASM_REWRITE_TAC [MULT_1] THEN
   NUM_REDUCE_TAC THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC coprime_mult_divides THEN
   ASM_REWRITE_TAC [];
   SUBGOAL_THEN `divides c c'` MP_TAC THENL
   [MATCH_MP_TAC mult1_divides THEN
    EXISTS_TAC `a : num` THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `k:num` SUBST_VAR_TAC o
      REWRITE_RULE [MULT_SYM] o
      REWRITE_RULE [divides_def]) THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [mult_divides_cancel; mult_lcm_cancel; IMP_IMP]]);;

export_thm lcm_least_imp;;

let lcm_least = prove
 (`!a b c. divides (lcm a b) c <=> divides a c /\ divides b c`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `lcm a b` THEN
   ASM_REWRITE_TAC [divides_lcm1; divides_lcm2];
   MATCH_ACCEPT_TAC lcm_least_imp]);;

export_thm lcm_least;;

let lcm_unique = prove
 (`!a b l.
     divides a l /\ divides b l /\
     (!c. divides a c /\ divides b c ==> divides l c) ==>
     lcm a b = l`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_antisym THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC lcm_least_imp THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [divides_lcm1; divides_lcm2]]);;

export_thm lcm_unique;;

let one_lcm = prove
 (`!a. lcm 1 a = a`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC lcm_unique THEN
  REWRITE_TAC [one_divides; divides_refl]);;

export_thm one_lcm;;

let lcm_one = prove
 (`!a. lcm a 1 = a`,
  ONCE_REWRITE_TAC [lcm_comm] THEN
  ACCEPT_TAC one_lcm);;

export_thm lcm_one;;

let lcm_is_one = prove
 (`!a b. lcm a b = 1 <=> a = 1 /\ b = 1`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REWRITE_TAC [GSYM divides_one] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `lcm a b` THEN
   ASM_REWRITE_TAC [divides_lcm1; divides_lcm2];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [lcm_one]]);;

export_thm lcm_is_one;;

let lcm_is_zero = prove
 (`!a b. lcm a b = 0 <=> a = 0 \/ b = 0`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   REWRITE_TAC [GSYM MULT_EQ_0] THEN
   ONCE_REWRITE_TAC [GSYM lcm_gcd] THEN
   ASM_REWRITE_TAC [ZERO_MULT];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [zero_lcm; lcm_zero]]);;

export_thm lcm_is_zero;;

let lcm_refl = prove
 (`!a. lcm a a = a`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC lcm_unique THEN
  REWRITE_TAC [divides_refl]);;

export_thm lcm_refl;;

let lcm_assoc = prove
 (`!a b c. lcm (lcm a b) c = lcm a (lcm b c)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC divides_antisym THEN
  STRIP_TAC THENL
  [MATCH_MP_TAC lcm_least_imp THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC lcm_least_imp THEN
    STRIP_TAC THENL
    [MATCH_ACCEPT_TAC divides_lcm1;
     MATCH_MP_TAC divides_lcm2_imp THEN
     MATCH_ACCEPT_TAC divides_lcm1];
    MATCH_MP_TAC divides_lcm2_imp THEN
    MATCH_ACCEPT_TAC divides_lcm2];
   MATCH_MP_TAC lcm_least_imp THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_lcm1_imp THEN
    MATCH_ACCEPT_TAC divides_lcm1;
    MATCH_MP_TAC lcm_least_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_lcm1_imp THEN
     MATCH_ACCEPT_TAC divides_lcm2;
     MATCH_ACCEPT_TAC divides_lcm2]]]);;

export_thm lcm_assoc;;

let divides_lcm = prove
 (`!a b. lcm a b = a <=> divides b a`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_ACCEPT_TAC divides_lcm2;
   STRIP_TAC THEN
   MATCH_MP_TAC lcm_unique THEN
   ASM_REWRITE_TAC [divides_refl] THEN
   REPEAT STRIP_TAC]);;

export_thm divides_lcm;;

let lcm_divides = prove
 (`!a b. lcm b a = a <=> divides b a`,
  ONCE_REWRITE_TAC [lcm_comm] THEN
  ACCEPT_TAC divides_lcm);;

export_thm lcm_divides;;

let lcm_left_distrib = prove
 (`!a b c. gcd a (lcm b c) = lcm (gcd a b) (gcd a c)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC divides_antisym THEN
  STRIP_TAC THENL
  [ALL_TAC;
   REWRITE_TAC [lcm_least; gcd_greatest; gcd_divides1; gcd_divides2] THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `b : num` THEN
    REWRITE_TAC [gcd_divides2; divides_lcm1];
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `c : num` THEN
    REWRITE_TAC [gcd_divides2; divides_lcm2]]] THEN
  SUBGOAL_THEN `?ac. gcd a c = ac` (CHOOSE_THEN MP_TAC) THENL
  [EXISTS_TAC `gcd a c` THEN
   REFL_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `?ab. gcd a b = ab` (CHOOSE_THEN MP_TAC) THENL
  [EXISTS_TAC `gcd a b` THEN
   REFL_TAC;
   ALL_TAC] THEN
  SPEC_TAC (`c : num`, `c : num`) THEN
  SPEC_TAC (`b : num`, `b : num`) THEN
  SPEC_TAC (`a : num`, `a : num`) THEN
  SPEC_TAC (`ac : num`, `ac : num`) THEN
  SPEC_TAC (`ab : num`, `ab : num`) THEN
  MATCH_MP_TAC coprime_induction THEN
  REPEAT CONJ_TAC THENL
  [REWRITE_TAC [gcd_is_zero] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [gcd_zero; lcm_zero; divides_refl];
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`ab : num`; `ac : num`] lcm_gcd) THEN
   ASM_REWRITE_TAC [MULT_1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `gcd a (b * c)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [gcd_greatest; gcd_divides1] THEN
    MATCH_MP_TAC gcd_divides2_imp THEN
    ONCE_REWRITE_TAC [GSYM lcm_gcd] THEN
    MATCH_MP_TAC divides_mult1 THEN
    MATCH_ACCEPT_TAC divides_refl;
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
    MATCH_ACCEPT_TAC divides_gcd_mult];
   X_GEN_TAC `k : num` THEN
   X_GEN_TAC `ab : num` THEN
   X_GEN_TAC `ac : num` THEN
   STRIP_TAC THEN
   X_GEN_TAC `a : num` THEN
   X_GEN_TAC `b : num` THEN
   X_GEN_TAC `c : num` THEN
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `divides k (gcd a b) /\ divides k (gcd a c)` MP_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC divides_mult1 THEN
    MATCH_ACCEPT_TAC divides_refl;
    ALL_TAC] THEN
   REWRITE_TAC [gcd_greatest] THEN
   CONV_TAC (LAND_CONV (REWRITE_CONV [divides_def])) THEN
   CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
   REWRITE_TAC [IMP_CONJ] THEN
   DISCH_THEN (K ALL_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `b' : num` SUBST_VAR_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `c' : num` SUBST_VAR_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `a' : num` SUBST_VAR_TAC) THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC
     [mult_gcd_cancel; mult_lcm_cancel; EQ_MULT_LCANCEL;
      mult_divides_cancel]]);;

export_thm lcm_left_distrib;;

let lcm_right_distrib = prove
 (`!a b c. gcd (lcm b c) a = lcm (gcd b a) (gcd c a)`,
  ONCE_REWRITE_TAC [gcd_comm] THEN
  ACCEPT_TAC lcm_left_distrib);;

export_thm lcm_right_distrib;;

let gcd_left_distrib = prove
 (`!a b c. lcm a (gcd b c) = gcd (lcm a b) (lcm a c)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [lcm_left_distrib] THEN
  REWRITE_TAC [lcm_right_distrib; gcd_refl; GSYM lcm_assoc] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC
    [lcm_assoc; divides_lcm; lcm_least; gcd_divides1; gcd_divides2]);;

export_thm gcd_left_distrib;;

let gcd_right_distrib = prove
 (`!a b c. lcm (gcd b c) a = gcd (lcm b a) (lcm c a)`,
  ONCE_REWRITE_TAC [lcm_comm] THEN
  ACCEPT_TAC gcd_left_distrib);;

export_thm gcd_right_distrib;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for the divides relation on natural numbers.               *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-haskell-src";;

export_thm divides_mod_cond;;  (* Haskell *)
export_thm egcd_def;;  (* Haskell *)
export_thm chinese_src;;  (* Haskell *)

(* ------------------------------------------------------------------------- *)
(* Haskell tests for the divides relation on natural numbers.                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-haskell-test";;

export_thm divides_refl;;  (* Haskell *)
export_thm divides_zero;;  (* Haskell *)
export_thm one_divides;;  (* Haskell *)
export_thm two_divides;;  (* Haskell *)
export_thm egcd_divides1_test;;  (* Haskell *)
export_thm egcd_divides2_test;;  (* Haskell *)
export_thm egcd_nonzero_test;;  (* Haskell *)
export_thm egcd_bound1_test;;  (* Haskell *)
export_thm egcd_bound2_test;;  (* Haskell *)
export_thm chinese_remainder1_test;;  (* Haskell *)
export_thm chinese_remainder2_test;;  (* Haskell *)
export_thm chinese_bound_test;;  (* Haskell *)

(* ------------------------------------------------------------------------- *)
(* Divides functions operating on ML numerals.                               *)
(* ------------------------------------------------------------------------- *)

(* Given a and b such that ~(a = 0), returns (s,t,g) satisfying *)
(* s * a = t * b + g /\ g = gcd a b *)
let egcd_num =
    let rec egcd a b =
        if eq_num b num_0 then (num_1,num_0,a)
        else if le_num a b then
          let q = quo_num b a in
          let b = sub_num b (mult_num q a) in
          let (s,t,g) = egcd a b in
          (add_num s (mult_num q t), t, g)
        else
          let q = quo_num a b in
          let a = sub_num a (mult_num q b) in
          if eq_num a num_0 then (num_1, sub_num q num_1, b) else
          let (s,t,g) = egcd a b in
          (s, add_num (mult_num q s) t, g) in
    egcd;;

(* ------------------------------------------------------------------------- *)
(* A simple proof tool to calculate the gcd of two numerals.                 *)
(* ------------------------------------------------------------------------- *)

let prove_egcd a b =
    let (s,t,g) = egcd_num (dest_numeral a) (dest_numeral b) in
    let mk_mult = mk_binop `( * ) : num -> num -> num` in
    let mk_add = mk_binop `( + ) : num -> num -> num` in
    let tm =
        mk_eq (mk_mult (mk_numeral s) a,
               mk_add (mk_mult (mk_numeral t) b) (mk_numeral g)) in
    EQT_ELIM (NUM_REDUCE_CONV tm);;

logfile_end ();;

(* ========================================================================= *)
(* Basic theory of divisibility, gcd, coprimality and primality (over N).    *)
(* ========================================================================= *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* HOL88 compatibility (since all this is a port of old HOL88 stuff).        *)
(* ------------------------------------------------------------------------- *)

let MULT_MONO_EQ = prove
 (`!m i n. ((SUC n) * m = (SUC n) * i) <=> (m = i)`,
  REWRITE_TAC[EQ_MULT_LCANCEL; NOT_SUC]);;

let LESS_ADD_1 = prove
 (`!m n. n < m ==> (?p. m = n + (p + 1))`,
  REWRITE_TAC[LT_EXISTS; ADD1; ADD_ASSOC]);;

let LESS_ADD_SUC = ARITH_RULE `!m n. m < (m + (SUC n))`;;

let LESS_0_CASES = ARITH_RULE `!m. (0 = m) \/ 0 < m`;;

let LESS_MONO_ADD = ARITH_RULE `!m n p. m < n ==> (m + p) < (n + p)`;;

let LESS_EQ_0 = prove
 (`!n. n <= 0 <=> (n = 0)`,
  REWRITE_TAC[LE]);;

let LESS_LESS_CASES = ARITH_RULE `!m n. (m = n) \/ m < n \/ n < m`;;

let LESS_ADD_NONZERO = ARITH_RULE `!m n. ~(n = 0) ==> m < (m + n)`;;

let NOT_EXP_0 = prove
 (`!m n. ~((SUC n) EXP m = 0)`,
  REWRITE_TAC[EXP_EQ_0; NOT_SUC]);;

let LESS_THM = ARITH_RULE `!m n. m < (SUC n) <=> (m = n) \/ m < n`;;

let NOT_LESS_0 = ARITH_RULE `!n. ~(n < 0)`;;

let ZERO_LESS_EXP = prove
 (`!m n. 0 < ((SUC n) EXP m)`,
  REWRITE_TAC[LT_NZ; NOT_EXP_0]);;

(* ------------------------------------------------------------------------- *)
(* General arithmetic lemmas.                                                *)
(* ------------------------------------------------------------------------- *)

let MULT_FIX = prove(
  `!x y. (x * y = x) <=> (x = 0) \/ (y = 1)`,
  REPEAT GEN_TAC THEN
  STRUCT_CASES_TAC(SPEC `x:num` num_CASES) THEN
  REWRITE_TAC[MULT_CLAUSES; NOT_SUC] THEN
  REWRITE_TAC[GSYM(el 4 (CONJUNCTS (SPEC_ALL MULT_CLAUSES)))] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [GSYM(el 3 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  MATCH_ACCEPT_TAC MULT_MONO_EQ);;

let LESS_EQ_MULT = prove(
  `!m n p q. m <= n /\ p <= q ==> (m * p) <= (n * q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB;
    GSYM ADD_ASSOC; LE_ADD]);;

let LESS_MULT = prove(
  `!m n p q. m < n /\ p < q ==> (m * p) < (n * q)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN
   ((CHOOSE_THEN SUBST_ALL_TAC) o MATCH_MP LESS_ADD_1)) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[GSYM ADD1; MULT_CLAUSES; ADD_CLAUSES; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[GSYM (el 3 (CONJUNCTS ADD_CLAUSES))] THEN
  MATCH_ACCEPT_TAC LESS_ADD_SUC);;

let MULT_LCANCEL = prove(
  `!a b c. ~(a = 0) /\ (a * b = a * c) ==> (b = c)`,
  REPEAT GEN_TAC THEN STRUCT_CASES_TAC(SPEC `a:num` num_CASES) THEN
  REWRITE_TAC[NOT_SUC; MULT_MONO_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Properties of the exponential function.                                   *)
(* ------------------------------------------------------------------------- *)

let EXP_0 = prove
 (`!n. 0 EXP (SUC n) = 0`,
  REWRITE_TAC[EXP; MULT_CLAUSES]);;

let EXP_MONO_LT_SUC = prove
 (`!n x y. (x EXP (SUC n)) < (y EXP (SUC n)) <=> (x < y)`,
  REWRITE_TAC[EXP_MONO_LT; NOT_SUC]);;

let EXP_MONO_LE_SUC = prove
 (`!x y n. (x EXP (SUC n)) <= (y EXP (SUC n)) <=> x <= y`,
  REWRITE_TAC[EXP_MONO_LE; NOT_SUC]);;

let EXP_MONO_EQ_SUC = prove
 (`!x y n. (x EXP (SUC n) = y EXP (SUC n)) <=> (x = y)`,
  REWRITE_TAC[EXP_MONO_EQ; NOT_SUC]);;

let EXP_EXP = prove
 (`!x m n. (x EXP m) EXP n = x EXP (m * n)`,
  REWRITE_TAC[EXP_MULT]);;

(* ------------------------------------------------------------------------- *)
(* More ad-hoc arithmetic lemmas unlikely to be useful elsewhere.            *)
(* ------------------------------------------------------------------------- *)

let DIFF_LEMMA = prove(
  `!a b. a < b ==> (a = 0) \/ (a + (b - a)) < (a + b)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPEC `a:num` LESS_0_CASES) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC o MATCH_MP LESS_ADD_1) THEN
  DISJ2_TAC THEN REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM (CONJUNCT1 ADD_CLAUSES)] THEN
  REWRITE_TAC[ADD_ASSOC] THEN
  REPEAT(MATCH_MP_TAC LESS_MONO_ADD) THEN POP_ASSUM ACCEPT_TAC);;

let NOT_EVEN_EQ_ODD = prove(
  `!m n. ~(2 * m = SUC(2 * n))`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
  REWRITE_TAC[EVEN; EVEN_MULT; ARITH]);;

let CANCEL_TIMES2 = prove(
  `!x y. (2 * x = 2 * y) <=> (x = y)`,
  REWRITE_TAC[num_CONV `2`; MULT_MONO_EQ]);;

let EVEN_SQUARE = prove(
  `!n. EVEN(n) ==> ?x. n EXP 2 = 4 * x`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  EXISTS_TAC `m * m` THEN REWRITE_TAC[EXP_2] THEN
  REWRITE_TAC[SYM(REWRITE_CONV[ARITH] `2 * 2`)] THEN
  REWRITE_TAC[MULT_AC]);;

let ODD_SQUARE = prove(
  `!n. ODD(n) ==> ?x. n EXP 2 = (4 * x) + 1`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST1_TAC) THEN
  ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES; ADD_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD1; SUC_INJ] THEN
  EXISTS_TAC `(m * m) + m` THEN
  REWRITE_TAC(map num_CONV [`4`; `3`; `2`; `1`]) THEN
  REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[ADD_AC]);;

let DIFF_SQUARE = prove(
  `!x y. (x EXP 2) - (y EXP 2) = (x + y) * (x - y)`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(SPECL [`x:num`; `y:num`] LE_CASES) THENL
   [SUBGOAL_THEN `(x * x) <= (y * y)` MP_TAC THENL
     [MATCH_MP_TAC LESS_EQ_MULT THEN ASM_REWRITE_TAC[];
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM SUB_EQ_0] THEN
      REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[EXP_2; MULT_CLAUSES]];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    REWRITE_TAC[EXP_2; LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
    REWRITE_TAC[GSYM ADD_ASSOC; ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC LAND_CONV [ADD_SYM] THEN
    AP_TERM_TAC THEN MATCH_ACCEPT_TAC MULT_SYM]);;

let ADD_IMP_SUB = prove(
  `!x y z. (x + y = z) ==> (x = z - y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[ADD_SUB]);;

let ADD_SUM_DIFF = prove(
  `!v w. v <= w ==> ((w + v) - (w - v) = 2 * v) /\
                    ((w + v) + (w - v) = 2 * w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CHOOSE_THEN SUBST1_TAC) THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB] THEN
  REWRITE_TAC[MULT_2; GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] ADD_SUB; GSYM ADD_ASSOC]);;

let EXP_4 = prove(
  `!n. n EXP 4 = (n EXP 2) EXP 2`,
  GEN_TAC THEN REWRITE_TAC[EXP_EXP] THEN
  REWRITE_TAC[ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Elementary theory of divisibility                                         *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_0 = prove
 (`!x. x divides 0`,
  NUMBER_TAC);;

let DIVIDES_ZERO = prove
 (`!x. 0 divides x <=> (x = 0)`,
  NUMBER_TAC);;

let DIVIDES_1 = prove
 (`!x. 1 divides x`,
  NUMBER_TAC);;

let DIVIDES_ONE = prove(
  `!x. (x divides 1) <=> (x = 1)`,
  GEN_TAC THEN REWRITE_TAC[divides] THEN
  CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  REWRITE_TAC[MULT_EQ_1] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `1` THEN REFL_TAC);;

let DIVIDES_REFL = prove
 (`!x. x divides x`,
  NUMBER_TAC);;

let DIVIDES_TRANS = prove
 (`!a b c. a divides b /\ b divides c ==> a divides c`,
  NUMBER_TAC);;

let DIVIDES_ANTISYM = prove
 (`!x y. x divides y /\ y divides x <=> (x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[divides] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CHOOSE_THEN SUBST1_TAC)) THEN
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN
    CONV_TAC(LAND_CONV SYM_CONV) THEN
    REWRITE_TAC[GSYM MULT_ASSOC; MULT_FIX; MULT_EQ_1] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[DIVIDES_REFL]]);;

let DIVIDES_ADD = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a + b)`,
  NUMBER_TAC);;

let DIVIDES_SUB = prove
 (`!d a b. d divides a /\ d divides b ==> d divides (a - b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
  REWRITE_TAC[GSYM LEFT_SUB_DISTRIB] THEN
  W(EXISTS_TAC o rand o lhs o snd o dest_exists o snd) THEN
  REFL_TAC);;

let DIVIDES_LMUL = prove
 (`!d a x. d divides a ==> d divides (x * a)`,
  NUMBER_TAC);;

let DIVIDES_RMUL = prove
 (`!d a x. d divides a ==> d divides (a * x)`,
  NUMBER_TAC);;

let DIVIDES_ADD_REVR = prove
 (`!d a b. d divides a /\ d divides (a + b) ==> d divides b`,
  NUMBER_TAC);;

let DIVIDES_ADD_REVL = prove
 (`!d a b. d divides b /\ d divides (a + b) ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_DIV = prove
 (`!n x. 0 < n /\ (x MOD n = 0) ==> n divides x`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:num` o MATCH_MP DIVISION o
           MATCH_MP (ARITH_RULE `0 < n ==> ~(n = 0)`)) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[divides] THEN EXISTS_TAC `x DIV n` THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN FIRST_ASSUM MATCH_ACCEPT_TAC);;

let DIVIDES_MUL_L = prove
 (`!a b c. a divides b ==> (c * a) divides (c * b)`,
  NUMBER_TAC);;

let DIVIDES_MUL_R = prove
 (`!a b c. a divides b ==> (a * c) divides (b * c)`,
  NUMBER_TAC);;

let DIVIDES_LMUL2 = prove
 (`!d a x. (x * d) divides a ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_RMUL2 = prove
 (`!d a x. (d * x) divides a ==> d divides a`,
  NUMBER_TAC);;

let DIVIDES_CMUL2 = prove
 (`!a b c. (c * a) divides (c * b) /\ ~(c = 0) ==> a divides b`,
  NUMBER_TAC);;

let DIVIDES_LMUL2_EQ = prove
 (`!a b c. ~(c = 0) ==> ((c * a) divides (c * b) <=> a divides b)`,
  NUMBER_TAC);;

let DIVIDES_RMUL2_EQ = prove
 (`!a b c. ~(c = 0) ==> ((a * c) divides (b * c) <=> a divides b)`,
  NUMBER_TAC);;

let DIVIDES_CASES = prove
 (`!m n. n divides m ==> m = 0 \/ m = n \/ 2 * n <= m`,
  SIMP_TAC[ARITH_RULE `m = n \/ 2 * n <= m <=> m = n * 1 \/ n * 2 <= m`] THEN
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[MULT_EQ_0; EQ_MULT_LCANCEL; LE_MULT_LCANCEL] THEN ARITH_TAC);;

let DIVIDES_LE_STRONG = prove
 (`!m n. m divides n ==> 1 <= m /\ m <= n \/ n = 0`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO; ARITH] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  POP_ASSUM MP_TAC THEN ARITH_TAC);;

let DIVIDES_DIV_NOT = prove(
  `!n x q r. (x = (q * n) + r) /\ 0 < r /\ r < n ==> ~(n divides x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPEC `n:num` DIVIDES_REFL) THEN
  DISCH_THEN(MP_TAC o SPEC `q:num` o MATCH_MP DIVIDES_LMUL) THEN
  PURE_REWRITE_TAC[TAUT `a ==> ~b <=> a /\ b ==> F`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_ADD_REVR) THEN
  DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[DE_MORGAN_THM; NOT_LE; GSYM LESS_EQ_0]);;

let DIVIDES_MUL2 = prove
 (`!a b c d. a divides b /\ c divides d ==> (a * c) divides (b * d)`,
  NUMBER_TAC);;

let DIVIDES_EXP = prove(
  `!x y n. x divides y ==> (x EXP n) divides (y EXP n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
  EXISTS_TAC `d EXP n` THEN MATCH_ACCEPT_TAC MULT_EXP);;

let DIVIDES_EXP2 = prove(
  `!n x y. ~(n = 0) /\ (x EXP n) divides y ==> x divides y`,
  INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EXP] THEN NUMBER_TAC);;

let DIVIDES_EXP_LE = prove
 (`!p m n. 2 <= p ==> ((p EXP m) divides (p EXP n) <=> m <= n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[LE_EXP; EXP_EQ_0] THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
    SIMP_TAC[LE_EXISTS; LEFT_IMP_EXISTS_THM; EXP_ADD] THEN NUMBER_TAC]);;

let DIVIDES_TRIVIAL_UPPERBOUND = prove
 (`!p n. ~(n = 0) /\ 2 <= p ==> ~((p EXP n) divides n)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP n` THEN REWRITE_TAC[LT_POW2_REFL] THEN
  UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP_MONO_LE_SUC]);;

let FACTORIZATION_INDEX = prove
 (`!n p. ~(n = 0) /\ 2 <= p
         ==> ?k. (p EXP k) divides n /\
                 !l. k < l ==> ~((p EXP l) divides n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NOT_LE; CONTRAPOS_THM] THEN
  REWRITE_TAC[GSYM num_MAX] THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[EXP; DIVIDES_1];
    EXISTS_TAC `n:num` THEN
    GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `2 EXP l` THEN
    SIMP_TAC[LT_POW2_REFL; LT_IMP_LE] THEN
    SPEC_TAC(`l:num`,`l:num`) THEN INDUCT_TAC THEN
    ASM_REWRITE_TAC[ARITH; CONJUNCT1 EXP; EXP_MONO_LE_SUC]]);;

let DIVIDES_FACT = prove
 (`!n p. 1 <= p /\ p <= n ==> p divides (FACT n)`,
  INDUCT_TAC THEN REWRITE_TAC[FACT; LE] THENL
   [ARITH_TAC; ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL; DIVIDES_REFL]]);;

let DIVIDES_2 = prove(
  `!n. 2 divides n <=> EVEN(n)`,
  REWRITE_TAC[divides; EVEN_EXISTS]);;

let DIVIDES_REXP_SUC = prove
 (`!x y n. x divides y ==> x divides (y EXP (SUC n))`,
  REWRITE_TAC[EXP; DIVIDES_RMUL]);;

let DIVIDES_REXP = prove
 (`!x y n. x divides y /\ ~(n = 0) ==> x divides (y EXP n)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[DIVIDES_REXP_SUC]);;

let DIVIDES_MOD = prove
 (`!m n. ~(m = 0) ==> (m divides n <=> (n MOD m = 0))`,
  REWRITE_TAC[divides] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[MOD_MULT]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  ASM_REWRITE_TAC[ADD_CLAUSES] THEN MESON_TAC[MULT_AC]);;

let DIVIDES_DIV_MULT = prove
 (`!m n. m divides n <=> ((n DIV m) * m = n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC[DIVIDES_ZERO; MULT_CLAUSES; EQ_SYM_EQ]; ALL_TAC] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[DIVIDES_LMUL; DIVIDES_REFL]] THEN
  DISCH_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `n DIV m * m + n MOD m` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[DIVIDES_MOD; ADD_CLAUSES];
    ASM_MESON_TAC[DIVISION]]);;

let FINITE_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d:num | d <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[DIVIDES_LE]);;

let FINITE_SPECIAL_DIVISORS = prove
 (`!n. ~(n = 0) ==> FINITE {d | P d /\ d divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{d | d divides n}` THEN ASM_SIMP_TAC[FINITE_DIVISORS] THEN
  SET_TAC[]);;

let DIVIDES_DIVIDES_DIV = prove
 (`!n d. 1 <= n /\ d divides n
         ==> (e divides (n DIV d) <=> (d * e) divides n)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [DIVIDES_DIV_MULT] THEN
  ABBREV_TAC `q = n DIV d` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `d = 0` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; LE_1];
    ASM_MESON_TAC[DIVIDES_LMUL2_EQ; MULT_SYM]]);;

let DIVISORS_EQ = prove
 (`!m n. m = n <=> !d. d divides m <=> d divides n`,
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let MULTIPLES_EQ = prove
 (`!m n. m = n <=> !d. m divides d <=> n divides d`,
  REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let DIVIDES_NSUM = prove
 (`!n f s. FINITE s /\ (!i. i IN s ==> n divides (f i))
           ==> n divides nsum s f`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  ASM_SIMP_TAC[DIVIDES_0; NSUM_CLAUSES; FORALL_IN_INSERT; DIVIDES_ADD]);;

(* ------------------------------------------------------------------------- *)
(* The Bezout theorem is a bit ugly for N; it'd be easier for Z              *)
(* ------------------------------------------------------------------------- *)

let IND_EUCLID = prove(
  `!P. (!a b. P a b <=> P b a) /\
       (!a. P a 0) /\
       (!a b. P a b ==> P a (a + b)) ==>
         !a b. P a b`,
  REPEAT STRIP_TAC THEN
  W(fun (asl,w) -> SUBGOAL_THEN `!n a b. (a + b = n) ==> P a b`
                   MATCH_MP_TAC) THENL
   [ALL_TAC; EXISTS_TAC `a + b` THEN REFL_TAC] THEN
  MATCH_MP_TAC num_WF THEN
  REPEAT STRIP_TAC THEN REPEAT_TCL DISJ_CASES_THEN MP_TAC
   (SPECL [`a:num`; `b:num`] LESS_LESS_CASES) THENL
   [DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM ADD_0] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM(MATCH_MP SUB_ADD
   (MATCH_MP LT_IMP_LE th))) THEN
    DISJ_CASES_THEN MP_TAC (MATCH_MP DIFF_LEMMA th)) THENL
   [DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM (CONV_TAC o REWR_CONV) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[ASSUME `a + b = n`] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `a + b - a < n` THEN
    DISCH_THEN(ANTE_RES_THEN MATCH_MP_TAC);
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] (ASSUME `a + b = n`)] THEN
    DISCH_TAC THEN ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_ASSUM (CONV_TAC o REWR_CONV) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `b + a - b < n` THEN
    DISCH_THEN(ANTE_RES_THEN MATCH_MP_TAC)] THEN
  REWRITE_TAC[]);;

let BEZOUT_LEMMA = prove(
  `!a b. (?d x y. (d divides a /\ d divides b) /\
                  ((a * x = (b * y) + d) \/
                   (b * x = (a * y) + d)))
     ==> (?d x y. (d divides a /\ d divides (a + b)) /\
                  ((a * x = ((a + b) * y) + d) \/
                   ((a + b) * x = (a * y) + d)))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `d:num` THENL
   [MAP_EVERY EXISTS_TAC [`x + y`; `y:num`];
    MAP_EVERY EXISTS_TAC [`x:num`; `x + y`]] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL [MATCH_MP_TAC DIVIDES_ADD; ALL_TAC]) THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[ADD_ASSOC] THEN DISJ1_TAC THEN
  REWRITE_TAC[ADD_AC]);;

let BEZOUT_ADD = prove(
  `!a b. ?d x y. (d divides a /\ d divides b) /\
                 ((a * x = (b * y) + d) \/
                  (b * x = (a * y) + d))`,
  W(fun (asl,w) -> MP_TAC(SPEC (list_mk_abs([`a:num`; `b:num`],
                                            snd(strip_forall w)))
    IND_EUCLID)) THEN BETA_TAC THEN DISCH_THEN MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT
     (AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
    GEN_TAC THEN BETA_TAC) THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [DISJ_SYM] THEN
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [CONJ_SYM] THEN REFL_TAC;
    GEN_TAC THEN MAP_EVERY EXISTS_TAC [`a:num`; `1`; `0`] THEN
    REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVIDES_0; DIVIDES_REFL];
    MATCH_ACCEPT_TAC BEZOUT_LEMMA]);;

let BEZOUT = prove(
  `!a b. ?d x y. (d divides a /\ d divides b) /\
                 (((a * x) - (b * y) = d) \/
                  ((b * x) - (a * y) = d))`,
  REPEAT GEN_TAC THEN REPEAT_TCL STRIP_THM_THEN ASSUME_TAC
   (SPECL [`a:num`; `b:num`] BEZOUT_ADD) THEN
  REPEAT(W(EXISTS_TAC o fst o dest_exists o snd)) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[ADD_SUB]);;

(* ------------------------------------------------------------------------- *)
(* We can get a stronger version with a nonzeroness assumption.              *)
(* ------------------------------------------------------------------------- *)

let BEZOUT_ADD_STRONG = prove
 (`!a b. ~(a = 0)
         ==> ?d x y. d divides a /\ d divides b /\ (a * x = b * y + d)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`] BEZOUT_ADD) THEN
  REWRITE_TAC[TAUT `a /\ (b \/ c) <=> a /\ b \/ a /\ c`] THEN
  REWRITE_TAC[EXISTS_OR_THM; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `(b ==> a) ==> a \/ b ==> a`) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `x:num`
    (X_CHOOSE_THEN `y:num` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_CASES_TAC `b = 0` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; ADD_EQ_0; MULT_EQ_0; ADD_CLAUSES] THEN
    STRIP_TAC THEN UNDISCH_TAC `d divides a` THEN
    ASM_REWRITE_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
  MP_TAC(SPECL [`d:num`; `b:num`] DIVIDES_LE) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[LE_LT] THEN STRIP_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN EXISTS_TAC `b:num` THEN EXISTS_TAC `b:num` THEN
    EXISTS_TAC `a - 1` THEN
    UNDISCH_TAC `d divides a` THEN ASM_SIMP_TAC[DIVIDES_REFL] THEN
    REWRITE_TAC[ARITH_RULE `b * x + b = (x + 1) * b`] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(a = 0) ==> ((a - 1) + 1 = a)`]] THEN
  ASM_CASES_TAC `x = 0` THENL
   [ASM_SIMP_TAC[MULT_CLAUSES; ADD_EQ_0; MULT_EQ_0] THEN STRIP_TAC THEN
    UNDISCH_TAC `d divides a` THEN ASM_REWRITE_TAC[DIVIDES_ZERO]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `( * ) (b - 1)`) THEN
  DISCH_THEN(MP_TAC o AP_TERM `(+) (d:num)`) THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV o RAND_CONV)
   [LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[ARITH_RULE `d + bay + b1 * d = (1 + b1) * d + bay`] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(b = 0) ==> (1 + (b - 1) = b)`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
   `(a + b = c + d) ==> a <= d ==> (b = (d - a) + c:num)`)) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[AC MULT_AC `(b - 1) * b * x = b * (b - 1) * x`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `d = d * 1`] THEN
    MATCH_MP_TAC LE_MULT2 THEN
    MAP_EVERY UNDISCH_TAC [`d < b:num`; `~(x = 0)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MAP_EVERY EXISTS_TAC [`d:num`; `y * (b - 1)`; `(b - 1) * x - d`] THEN
    MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o LAND_CONV) [LEFT_SUB_DISTRIB] THEN
  REWRITE_TAC[MULT_AC]);;

(* ------------------------------------------------------------------------- *)
(* Greatest common divisor.                                                  *)
(* ------------------------------------------------------------------------- *)

let GCD = prove
 (`!a b. (gcd(a,b) divides a /\ gcd(a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides gcd(a,b))`,
  NUMBER_TAC);;

let DIVIDES_GCD = prove
 (`!a b d. d divides gcd(a,b) <=> d divides a /\ d divides b`,
  NUMBER_TAC);;

let GCD_UNIQUE = prove(
  `!d a b. (d divides a /\ d divides b) /\
           (!e. e divides a /\ e divides b ==> e divides d) <=>
           (d = gcd(a,b))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[GCD] THEN
  ONCE_REWRITE_TAC[GSYM DIVIDES_ANTISYM] THEN
  ASM_REWRITE_TAC[DIVIDES_GCD] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[GCD]);;

let GCD_EQ = prove
 (`(!d. d divides x /\ d divides y <=> d divides u /\ d divides v)
   ==> gcd(x,y) = gcd(u,v)`,
  REWRITE_TAC[DIVIDES_GCD; GSYM DIVIDES_ANTISYM] THEN MESON_TAC[GCD]);;

let GCD_SYM = prove
 (`!a b. gcd(a,b) = gcd(b,a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM GCD_UNIQUE] THEN NUMBER_TAC);;

let GCD_ASSOC = prove(
  `!a b c. gcd(a,gcd(b,c)) = gcd(gcd(a,b),c)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_GCD; CONJ_ASSOC; GCD] THEN
  CONJ_TAC THEN MATCH_MP_TAC DIVIDES_TRANS THEN
  EXISTS_TAC `gcd(b,c)` THEN ASM_REWRITE_TAC[GCD]);;

let BEZOUT_GCD = prove(
  `!a b. ?x y. ((a * x) - (b * y) = gcd(a,b)) \/
               ((b * x) - (a * y) = gcd(a,b))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`a:num`; `b:num`] BEZOUT) THEN
  DISCH_THEN(EVERY_TCL (map X_CHOOSE_THEN [`d:num`; `x:num`; `y:num`])
    (CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `d divides gcd(a,b)` MP_TAC THENL
   [MATCH_MP_TAC(last(CONJUNCTS(SPEC_ALL GCD))) THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    MAP_EVERY EXISTS_TAC [`x * k`; `y * k`] THEN
    ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; MULT_ASSOC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);;

let BEZOUT_GCD_STRONG = prove
 (`!a b. ~(a = 0) ==> ?x y. a * x = b * y + gcd(a,b)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:num` o MATCH_MP BEZOUT_ADD_STRONG) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`d:num`; `x:num`; `y:num`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d divides gcd(a,b)` MP_TAC THENL
   [ASM_MESON_TAC[GCD]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
  MAP_EVERY EXISTS_TAC [`x * k`; `y * k`] THEN
  ASM_REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB; MULT_ASSOC]);;

let GCD_LMUL = prove(
  `!a b c. gcd(c * a, c * b) = c * gcd(a,b)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REPEAT CONJ_TAC THEN TRY(MATCH_MP_TAC DIVIDES_MUL_L) THEN
  REWRITE_TAC[GCD] THEN REPEAT STRIP_TAC THEN
  REPEAT_TCL STRIP_THM_THEN (SUBST1_TAC o SYM)
   (SPECL [`a:num`; `b:num`] BEZOUT_GCD) THEN
  REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_ASSOC] THEN
  MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN ASM_REWRITE_TAC[]);;

let GCD_RMUL = prove(
  `!a b c. gcd(a * c, b * c) = c * gcd(a,b)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [MULT_SYM] THEN
  MATCH_ACCEPT_TAC GCD_LMUL);;

let GCD_BEZOUT = prove(
  `!a b d. (?x y. ((a * x) - (b * y) = d) \/ ((b * x) - (a * y) = d)) <=>
           gcd(a,b) divides d`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN POP_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[GCD];
    DISCH_THEN(X_CHOOSE_THEN `k:num` SUBST1_TAC o REWRITE_RULE[divides]) THEN
    STRIP_ASSUME_TAC(SPECL [`a:num`; `b:num`] BEZOUT_GCD) THEN
    MAP_EVERY EXISTS_TAC [`x * k`; `y * k`] THEN
    ASM_REWRITE_TAC[GSYM RIGHT_SUB_DISTRIB; MULT_ASSOC] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN REWRITE_TAC[]]);;

let GCD_BEZOUT_SUM = prove(
  `!a b d x y. ((a * x) + (b * y) = d) ==> gcd(a,b) divides d`,
  REPEAT GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC DIVIDES_ADD THEN CONJ_TAC THEN
  MATCH_MP_TAC DIVIDES_RMUL THEN REWRITE_TAC[GCD]);;

let GCD_0 = prove
  (`(!a. gcd(0,a) = a) /\ (!a. gcd(a,0) = a)`,
  MESON_TAC[GCD_UNIQUE; DIVIDES_0; DIVIDES_REFL]);;

let GCD_ZERO = prove(
  `!a b. (gcd(a,b) = 0) <=> (a = 0) /\ (b = 0)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[GCD_0] THEN
  MP_TAC(SPECL [`a:num`; `b:num`] GCD) THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let GCD_REFL = prove(
  `!a. gcd(a,a) = a`,
  GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  REWRITE_TAC[DIVIDES_REFL]);;

let GCD_1 = prove
  (`(!a. gcd(1,a) = 1) /\ (!a. gcd(a,1) = 1)`,
  MESON_TAC[GCD_UNIQUE; DIVIDES_1]);;

let GCD_MULTIPLE = prove(
  `!a b. gcd(b,a * b) = b`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
   [GSYM(el 2 (CONJUNCTS(SPEC_ALL MULT_CLAUSES)))] THEN
  REWRITE_TAC[GCD_RMUL; GCD_1] THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let GCD_ADD = prove
 (`(!a b. gcd(a + b,b) = gcd(a,b)) /\
   (!a b. gcd(b + a,b) = gcd(a,b)) /\
   (!a b. gcd(a,a + b) = gcd(a,b)) /\
   (!a b. gcd(a,b + a) = gcd(a,b))`,
  REWRITE_TAC[GSYM GCD_UNIQUE] THEN NUMBER_TAC);;

let GCD_SUB = prove
 (`(!a b. b <= a ==> gcd(a - b,b) = gcd(a,b)) /\
   (!a b. a <= b ==> gcd(a,b - a) = gcd(a,b))`,
  MESON_TAC[SUB_ADD; GCD_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Coprimality                                                               *)
(* ------------------------------------------------------------------------- *)

let coprime = prove
 (`coprime(a,b) <=> !d. d divides a /\ d divides b ==> (d = 1)`,
  EQ_TAC THENL
   [REWRITE_TAC[GSYM DIVIDES_ONE];
    DISCH_THEN(MP_TAC o SPEC `gcd(a,b)`) THEN REWRITE_TAC[GCD]] THEN
  NUMBER_TAC);;

let COPRIME = prove(
  `!a b. coprime(a,b) <=> !d. d divides a /\ d divides b <=> (d = 1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THEN ASM_REWRITE_TAC[DIVIDES_1] THENL
   [FIRST_ASSUM MATCH_MP_TAC;
    FIRST_ASSUM(CONV_TAC o REWR_CONV o GSYM) THEN CONJ_TAC] THEN
  ASM_REWRITE_TAC[]);;

let COPRIME_GCD = prove
 (`!a b. coprime(a,b) <=> (gcd(a,b) = 1)`,
  REWRITE_TAC[GSYM DIVIDES_ONE] THEN NUMBER_TAC);;

let COPRIME_SYM = prove
 (`!a b. coprime(a,b) <=> coprime(b,a)`,
  NUMBER_TAC);;

let COPRIME_BEZOUT = prove(
  `!a b. coprime(a,b) <=> ?x y. ((a * x) - (b * y) = 1) \/
                                ((b * x) - (a * y) = 1)`,
  REWRITE_TAC[GCD_BEZOUT; DIVIDES_ONE; COPRIME_GCD]);;

let COPRIME_DIVPROD = prove
 (`!d a b. d divides (a * b) /\ coprime(d,a) ==> d divides b`,
  NUMBER_TAC);;

let COPRIME_1 = prove
 (`!a. coprime(a,1)`,
  NUMBER_TAC);;

let GCD_COPRIME = prove
 (`!a b a' b'. ~(gcd(a,b) = 0) /\ a = a' * gcd(a,b) /\ b = b' * gcd(a,b)
               ==> coprime(a',b')`,
  NUMBER_TAC);;

let GCD_COPRIME_EXISTS = prove(
  `!a b. ~(gcd(a,b) = 0) ==>
        ?a' b'. (a = a' * gcd(a,b)) /\
                (b = b' * gcd(a,b)) /\
                coprime(a',b')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN MP_TAC(SPECL [`a:num`; `b:num`] GCD) THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[divides] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a':num` o GSYM)
   (X_CHOOSE_TAC `b':num` o GSYM)) THEN
  MAP_EVERY EXISTS_TAC [`a':num`; `b':num`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC GCD_COPRIME THEN
  MAP_EVERY EXISTS_TAC [`a:num`; `b:num`] THEN
  ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[]);;

let COPRIME_0 = prove
 (`(!d. coprime(d,0) <=> d = 1) /\
   (!d. coprime(0,d) <=> d = 1)`,
  REWRITE_TAC[GSYM DIVIDES_ONE] THEN NUMBER_TAC);;

let COPRIME_MUL = prove
 (`!d a b. coprime(d,a) /\ coprime(d,b) ==> coprime(d,a * b)`,
  NUMBER_TAC);;

let COPRIME_LMUL2 = prove
 (`!d a b. coprime(d,a * b) ==> coprime(d,b)`,
  NUMBER_TAC);;

let COPRIME_RMUL2 = prove
 (`!d a b.  coprime(d,a * b) ==> coprime(d,a)`,
  NUMBER_TAC);;

let COPRIME_LMUL = prove
 (`!d a b. coprime(a * b,d) <=> coprime(a,d) /\ coprime(b,d)`,
  NUMBER_TAC);;

let COPRIME_RMUL = prove
 (`!d a b. coprime(d,a * b) <=> coprime(d,a) /\ coprime(d,b)`,
  NUMBER_TAC);;

let COPRIME_EXP = prove
 (`!n a d. coprime(d,a) ==> coprime(d,a EXP n)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; COPRIME_1] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_MUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let COPRIME_EXP_IMP = prove
 (`!n a b. coprime(a,b) ==> coprime(a EXP n,b EXP n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC COPRIME_EXP THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  MATCH_MP_TAC COPRIME_EXP THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN ASM_REWRITE_TAC[]);;

let COPRIME_REXP = prove
 (`!m n k. coprime(m,n EXP k) <=> coprime(m,n) \/ k = 0`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[CONJUNCT1 EXP; COPRIME_1] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[COPRIME_EXP; NOT_SUC] THEN
  REWRITE_TAC[EXP] THEN CONV_TAC NUMBER_RULE);;

let COPRIME_LEXP = prove
 (`!m n k. coprime(m EXP k,n) <=> coprime(m,n) \/ k = 0`,
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN REWRITE_TAC[COPRIME_REXP]);;

let COPRIME_EXP2 = prove
 (`!m n k. coprime(m EXP k,n EXP k) <=> coprime(m,n) \/ k = 0`,
  REWRITE_TAC[COPRIME_REXP; COPRIME_LEXP; DISJ_ACI]);;

let COPRIME_EXP2_SUC = prove
 (`!n a b. coprime(a EXP (SUC n),b EXP (SUC n)) <=> coprime(a,b)`,
  REWRITE_TAC[COPRIME_EXP2; NOT_SUC]);;

let COPRIME_REFL = prove
 (`!n. coprime(n,n) <=> (n = 1)`,
  REWRITE_TAC[COPRIME_GCD; GCD_REFL]);;

let COPRIME_PLUS1 = prove
 (`!n. coprime(n + 1,n)`,
  NUMBER_TAC);;

let COPRIME_MINUS1 = prove
 (`!n. ~(n = 0) ==> coprime(n - 1,n)`,
  REPEAT STRIP_TAC THEN SIMP_TAC[coprime] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_SUB) THEN
  ASM_SIMP_TAC[ARITH_RULE `~(n = 0) ==> n - (n - 1) = 1`; DIVIDES_ONE]);;

let BEZOUT_GCD_POW = prove(
  `!n a b. ?x y. (((a EXP n) * x) - ((b EXP n) * y) = gcd(a,b) EXP n) \/
                 (((b EXP n) * x) - ((a EXP n) * y) = gcd(a,b) EXP n)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `gcd(a,b) = 0` THENL
   [STRUCT_CASES_TAC(SPEC `n:num` num_CASES) THEN
    ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THENL
     [MAP_EVERY EXISTS_TAC [`1`; `0`] THEN REWRITE_TAC[SUB_0];
      REPEAT(EXISTS_TAC `0`) THEN REWRITE_TAC[MULT_CLAUSES; SUB_0]];
    MP_TAC(SPECL [`a:num`; `b:num`] GCD) THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN MP_TAC) THEN REWRITE_TAC[divides] THEN
    DISCH_THEN(X_CHOOSE_THEN `b':num` ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num` ASSUME_TAC) THEN
    MP_TAC(SPECL [`a:num`; `b:num`; `a':num`; `b':num`] GCD_COPRIME) THEN
    RULE_ASSUM_TAC GSYM THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP COPRIME_EXP_IMP) THEN
    REWRITE_TAC[COPRIME_BEZOUT] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num` (X_CHOOSE_THEN `y:num` MP_TAC)) THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THEN
    DISCH_THEN (MP_TAC o AP_TERM `(*) (gcd(a,b) EXP n)`) THEN
    REWRITE_TAC[MULT_CLAUSES; LEFT_SUB_DISTRIB] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MAP_EVERY EXISTS_TAC [`x:num`; `y:num`] THEN
    REWRITE_TAC[MULT_ASSOC; GSYM MULT_EXP] THEN
    RULE_ASSUM_TAC(ONCE_REWRITE_RULE[MULT_SYM]) THEN
    ASM_REWRITE_TAC[]]);;

let GCD_EXP = prove(
  `!n a b. gcd(a EXP n,b EXP n) = gcd(a,b) EXP n`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC DIVIDES_EXP THEN REWRITE_TAC[GCD];
    MATCH_MP_TAC DIVIDES_EXP THEN REWRITE_TAC[GCD];
    X_GEN_TAC `d:num` THEN STRIP_TAC THEN
    MP_TAC(SPECL [`n:num`; `a:num`; `b:num`] BEZOUT_GCD_POW) THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (DISJ_CASES_THEN
     (SUBST1_TAC o SYM))) THEN
    MATCH_MP_TAC DIVIDES_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN ASM_REWRITE_TAC[]]);;

let DIVISION_DECOMP = prove(
  `!a b c. a divides (b * c) ==>
     ?b' c'. (a = b' * c') /\ b' divides b /\ c' divides c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `gcd(a,b)` THEN REWRITE_TAC[GCD] THEN
  MP_TAC(SPECL [`a:num`; `b:num`] GCD_COPRIME_EXISTS) THEN
  ASM_CASES_TAC `gcd(a,b) = 0` THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `1` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GCD_ZERO]) THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; DIVIDES_1];
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':num` (X_CHOOSE_THEN `b':num`
      (STRIP_ASSUME_TAC o GSYM o ONCE_REWRITE_RULE[MULT_SYM]))) THEN
    EXISTS_TAC `a':num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `a divides (b * c)` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC
      (LAND_CONV o LAND_CONV) [GSYM th]) THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV)
     [GSYM th]) THEN REWRITE_TAC[MULT_ASSOC] THEN
    DISCH_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
    EXISTS_TAC `b':num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIVIDES_CMUL2 THEN EXISTS_TAC `gcd(a,b)` THEN
    REWRITE_TAC[MULT_ASSOC] THEN CONJ_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

let DIVIDES_EXP2_REV = prove
 (`!n a b. (a EXP n) divides (b EXP n) /\ ~(n = 0) ==> a divides b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `gcd(a,b) = 0` THENL
   [ASM_MESON_TAC[GCD_ZERO; DIVIDES_REFL]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP GCD_COPRIME_EXISTS) THEN
  STRIP_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[MULT_EXP] THEN
  ASM_SIMP_TAC[EXP_EQ_0; DIVIDES_RMUL2_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (NUMBER_RULE
   `a divides b ==> coprime(a,b) ==> a divides 1`)) THEN
  ASM_SIMP_TAC[COPRIME_EXP2; DIVIDES_ONE; DIVIDES_1; EXP_EQ_1]);;

let DIVIDES_EXP2_EQ = prove
 (`!n a b. ~(n = 0) ==> ((a EXP n) divides (b EXP n) <=> a divides b)`,
  MESON_TAC[DIVIDES_EXP2_REV; DIVIDES_EXP]);;

let DIVIDES_MUL = prove
 (`!m n r. m divides r /\ n divides r /\ coprime(m,n) ==> (m * n) divides r`,
  NUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* A binary form of the Chinese Remainder Theorem.                           *)
(* ------------------------------------------------------------------------- *)

let CHINESE_REMAINDER = prove
 (`!a b u v. coprime(a,b) /\ ~(a = 0) /\ ~(b = 0)
             ==> ?x q1 q2. (x = u + q1 * a) /\ (x = v + q2 * b)`,
  let lemma = prove
   (`(?d x y. (d = 1) /\ P x y d) <=> (?x y. P x y 1)`,
    MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`b:num`; `a:num`] BEZOUT_ADD_STRONG) THEN
  MP_TAC(SPECL [`a:num`; `b:num`] BEZOUT_ADD_STRONG) THEN
  ASM_REWRITE_TAC[CONJ_ASSOC] THEN
  SUBGOAL_THEN `!d. d divides a /\ d divides b <=> (d = 1)`
   (fun th -> REWRITE_TAC[th; ONCE_REWRITE_RULE[CONJ_SYM] th])
  THENL
   [UNDISCH_TAC `coprime(a,b)` THEN
    SIMP_TAC[GSYM DIVIDES_GCD; COPRIME_GCD; DIVIDES_ONE]; ALL_TAC] THEN
  REWRITE_TAC[lemma] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:num` (X_CHOOSE_TAC `y1:num`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `x2:num` (X_CHOOSE_TAC `y2:num`)) THEN
  EXISTS_TAC `v * a * x1 + u * b * x2:num` THEN
  EXISTS_TAC `v * x1 + u * y2:num` THEN
  EXISTS_TAC `v * y1 + u * x2:num` THEN CONJ_TAC THENL
   [SUBST1_TAC(ASSUME `b * x2 = a * y2 + 1`);
    SUBST1_TAC(ASSUME `a * x1 = b * y1 + 1`)] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[MULT_AC] THEN REWRITE_TAC[ADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* Primality                                                                 *)
(* ------------------------------------------------------------------------- *)

let prime = new_definition
  `prime(p) <=> ~(p = 1) /\ !x. x divides p ==> (x = 1) \/ (x = p)`;;

(* ------------------------------------------------------------------------- *)
(* A few useful theorems about primes                                        *)
(* ------------------------------------------------------------------------- *)

let PRIME_0 = prove(
  `~prime(0)`,
  REWRITE_TAC[prime] THEN
  DISCH_THEN(MP_TAC o SPEC `2` o CONJUNCT2) THEN
  REWRITE_TAC[DIVIDES_0; ARITH]);;

let PRIME_1 = prove(
  `~prime(1)`,
  REWRITE_TAC[prime]);;

let PRIME_2 = prove(
  `prime(2)`,
  REWRITE_TAC[prime; ARITH] THEN
  REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  REWRITE_TAC[ARITH] THEN REWRITE_TAC[LE_LT] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; LESS_THM; NOT_LESS_0] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  REWRITE_TAC[] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[DIVIDES_ZERO] THEN
  REWRITE_TAC[ARITH] THEN REWRITE_TAC[]);;

let PRIME_GE_2 = prove(
  `!p. prime(p) ==> 2 <= p`,
  GEN_TAC THEN CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
  REWRITE_TAC[num_CONV `2`; num_CONV `1`; LESS_THM; NOT_LESS_0] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) THEN
  REWRITE_TAC[SYM(num_CONV `1`); PRIME_0; PRIME_1]);;

let PRIME_FACTOR = prove(
  `!n. ~(n = 1) ==> ?p. prime(p) /\ p divides n`,
  MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `prime(n)` THENL
   [EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[DIVIDES_REFL];
    UNDISCH_TAC `~prime(n)` THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[prime]) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC) THEN
    REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(DISJ_CASES_THEN MP_TAC o MATCH_MP DIVIDES_LE) THENL
     [ASM_REWRITE_TAC[LE_LT] THEN
      DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `m:num` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `2` THEN
      REWRITE_TAC[PRIME_2; DIVIDES_0]]]);;

let PRIME_FACTOR_LT = prove(
  `!n m p. prime(p) /\ ~(n = 0) /\ (n = p * m) ==> m < n`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN
  ASM_REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:num` SUBST_ALL_TAC) THEN
  REWRITE_TAC[num_CONV `2`; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  REWRITE_TAC[GSYM ADD_ASSOC] THEN MATCH_MP_TAC LESS_ADD_NONZERO THEN
  REWRITE_TAC[ADD_EQ_0] THEN DISCH_THEN(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
  FIRST_ASSUM(UNDISCH_TAC o check is_eq o concl) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES]);;

let PRIME_FACTOR_INDUCT = prove
 (`!P. P 0 /\ P 1 /\
       (!p n. prime p /\ ~(n = 0) /\ P n ==> P(p * n))
       ==> !n. P n`,
  GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN MAP_EVERY ASM_CASES_TAC [`n = 0`; `n = 1`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(X_CHOOSE_THEN `p:num`
    STRIP_ASSUME_TAC o MATCH_MP PRIME_FACTOR) THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    GEN_REWRITE_RULE I [divides]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `d:num`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[PRIME_FACTOR_LT; MULT_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Infinitude of primes.                                                     *)
(* ------------------------------------------------------------------------- *)

let EUCLID_BOUND = prove
 (`!n. ?p. prime(p) /\ n < p /\ p <= SUC(FACT n)`,
  GEN_TAC THEN MP_TAC(SPEC `FACT n + 1` PRIME_FACTOR) THEN
  SIMP_TAC[ARITH_RULE `0 < n ==> ~(n + 1 = 1)`; ADD1; FACT_LT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[DIVIDES_ADD_REVR; DIVIDES_ONE; PRIME_1; NOT_LT; PRIME_0;
                  ARITH_RULE `(p = 0) \/ 1 <= p`; DIVIDES_FACT];
    ASM_MESON_TAC[DIVIDES_LE; ARITH_RULE `~(x + 1 = 0)`]]);;

let EUCLID = prove
 (`!n. ?p. prime(p) /\ p > n`,
  REWRITE_TAC[GT] THEN MESON_TAC[EUCLID_BOUND]);;

let PRIMES_INFINITE = prove
 (`INFINITE {p | prime p}`,
  REWRITE_TAC[INFINITE; num_FINITE; IN_ELIM_THM] THEN
  MESON_TAC[EUCLID; NOT_LE; GT]);;

let COPRIME_PRIME = prove(
  `!p a b. coprime(a,b) ==> ~(prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[coprime] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p = 1` SUBST_ALL_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `prime 1` THEN REWRITE_TAC[PRIME_1]]);;

let COPRIME_PRIME_EQ = prove(
  `!a b. coprime(a,b) <=> !p. ~(prime(p) /\ p divides a /\ p divides b)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP COPRIME_PRIME th]);
    CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[coprime] THEN
    ONCE_REWRITE_TAC[NOT_FORALL_THM] THEN REWRITE_TAC[NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(X_CHOOSE_TAC `p:num` o MATCH_MP PRIME_FACTOR) THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC DIVIDES_TRANS THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[]]);;

let PRIME_COPRIME = prove(
  `!n p. prime(p) ==> (n = 1) \/ p divides n \/ coprime(p,n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[prime; COPRIME_GCD] THEN
  STRIP_ASSUME_TAC(SPECL [`p:num`; `n:num`] GCD) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `gcd(p,n)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THEN
  ASM_REWRITE_TAC[]);;

let PRIME_COPRIME_STRONG = prove
 (`!n p. prime(p) ==> p divides n \/ coprime(p,n)`,
  MESON_TAC[PRIME_COPRIME; COPRIME_1]);;

let PRIME_COPRIME_EQ = prove
 (`!p n. prime p ==> (coprime(p,n) <=> ~(p divides n))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(b \/ a) /\ ~(a /\ b) ==> (a <=> ~b)`) THEN
  ASM_SIMP_TAC[PRIME_COPRIME_STRONG] THEN
  ASM_MESON_TAC[COPRIME_REFL; PRIME_1; NUMBER_RULE
   `coprime(p,n) /\ p divides n ==> coprime(p,p)`]);;

let COPRIME_PRIMEPOW = prove
 (`!p k m. prime p /\ ~(k = 0) ==> (coprime(m,p EXP k) <=> ~(p divides m))`,
  SIMP_TAC[COPRIME_REXP] THEN ONCE_REWRITE_TAC[COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ]);;

let COPRIME_BEZOUT_STRONG = prove
 (`!a b. coprime(a,b) /\ ~(b = 1) ==> ?x y. a * x = b * y + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
  ASM_MESON_TAC[COPRIME_0; COPRIME_SYM]);;

let COPRIME_BEZOUT_ALT = prove
 (`!a b. coprime(a,b) /\ ~(a = 0) ==> ?x y. a * x = b * y + 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_GCD]) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC BEZOUT_GCD_STRONG THEN
  ASM_MESON_TAC[COPRIME_0; COPRIME_SYM]);;

let BEZOUT_PRIME = prove
 (`!a p. prime p /\ ~(p divides a) ==> ?x y. a * x = p * y + 1`,
  MESON_TAC[PRIME_COPRIME_STRONG; COPRIME_SYM;
     COPRIME_BEZOUT_STRONG; PRIME_1]);;

let PRIME_DIVPROD = prove(
  `!p a b. prime(p) /\ p divides (a * b) ==> p divides a \/ p divides b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `a:num` o MATCH_MP PRIME_COPRIME) THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN UNDISCH_TAC `p divides (a * b)` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES];
    DISJ2_TAC THEN MATCH_MP_TAC COPRIME_DIVPROD THEN
    EXISTS_TAC `a:num` THEN ASM_REWRITE_TAC[]]);;

let PRIME_DIVPROD_EQ = prove
 (`!p a b. prime(p) ==> (p divides (a * b) <=> p divides a \/ p divides b)`,
  MESON_TAC[PRIME_DIVPROD; DIVIDES_LMUL; DIVIDES_RMUL]);;

let PRIME_DIVEXP = prove(
  `!n p x. prime(p) /\ p divides (x EXP n) ==> p divides x`,
  INDUCT_TAC THEN REPEAT GEN_TAC THEN REWRITE_TAC[EXP; DIVIDES_ONE] THENL
   [DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN REWRITE_TAC[DIVIDES_1];
    DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(DISJ_CASES_TAC o MATCH_MP PRIME_DIVPROD) THEN
    ASM_REWRITE_TAC[] THEN FIRST_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let PRIME_DIVEXP_N = prove(
  `!n p x. prime(p) /\ p divides (x EXP n) ==> (p EXP n) divides (x EXP n)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP PRIME_DIVEXP) THEN
  MATCH_ACCEPT_TAC DIVIDES_EXP);;

let PRIME_DIVEXP_EQ = prove
 (`!n p x. prime p ==> (p divides x EXP n <=> p divides x /\ ~(n = 0))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP; DIVIDES_ONE] THEN
  ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_REXP; PRIME_1]);;

let PARITY_EXP = prove(
  `!n x. EVEN(x EXP (SUC n)) = EVEN(x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM DIVIDES_2] THEN EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC PRIME_DIVEXP THEN
    EXISTS_TAC `SUC n` THEN ASM_REWRITE_TAC[PRIME_2];
    REWRITE_TAC[EXP] THEN MATCH_ACCEPT_TAC DIVIDES_RMUL]);;

let COPRIME_SOS = prove
 (`!x y. coprime(x,y) ==> coprime(x * y,(x EXP 2) + (y EXP 2))`,
  NUMBER_TAC);;

let PRIME_IMP_NZ = prove
 (`!p. prime(p) ==> ~(p = 0)`,
  MESON_TAC[PRIME_0]);;

let DISTINCT_PRIME_COPRIME = prove
 (`!p q. prime p /\ prime q /\ ~(p = q) ==> coprime(p,q)`,
  MESON_TAC[prime; coprime; PRIME_1]);;

let PRIME_COPRIME_LT = prove
 (`!x p. prime p /\ 0 < x /\ x < p ==> coprime(x,p)`,
  REWRITE_TAC[coprime; prime] THEN
  MESON_TAC[LT_REFL; DIVIDES_LE; NOT_LT; PRIME_0]);;

let DIVIDES_PRIME_PRIME = prove
 (`!p q. prime p /\ prime q  ==> (p divides q <=> p = q)`,
  MESON_TAC[DIVIDES_REFL; DISTINCT_PRIME_COPRIME; PRIME_COPRIME_EQ]);;

let DIVIDES_PRIME_EXP_LE = prove
 (`!p q m n. prime p /\ prime q
             ==> ((p EXP m) divides (q EXP n) <=> m = 0 \/ p = q /\ m <= n)`,
  GEN_TAC THEN GEN_TAC THEN REPEAT INDUCT_TAC THEN
  ASM_SIMP_TAC[EXP; DIVIDES_1; DIVIDES_ONE; MULT_EQ_1; NOT_SUC] THENL
   [MESON_TAC[PRIME_1; ARITH_RULE `~(SUC m <= 0)`]; ALL_TAC] THEN
  ASM_CASES_TAC `p:num = q` THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2; GSYM(CONJUNCT2 EXP)] THEN
  ASM_MESON_TAC[PRIME_DIVEXP; DIVIDES_PRIME_PRIME; EXP; DIVIDES_RMUL2]);;

let EQ_PRIME_EXP = prove
 (`!p q m n. prime p /\ prime q
             ==> (p EXP m = q EXP n <=> m = 0 /\ n = 0 \/ p = q /\ m = n)`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM DIVIDES_ANTISYM] THEN
  ASM_SIMP_TAC[DIVIDES_PRIME_EXP_LE] THEN ARITH_TAC);;

let PRIME_ODD = prove
 (`!p. prime p ==> p = 2 \/ ODD p`,
  GEN_TAC THEN REWRITE_TAC[prime; GSYM NOT_EVEN; EVEN_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `2`)) THEN
  REWRITE_TAC[divides; ARITH] THEN MESON_TAC[]);;

let DIVIDES_FACT_PRIME = prove
 (`!p. prime p ==> !n. p divides (FACT n) <=> p <= n`,
  GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN REWRITE_TAC[FACT; LE] THENL
   [ASM_MESON_TAC[DIVIDES_ONE; PRIME_0; PRIME_1];
    ASM_MESON_TAC[PRIME_DIVPROD_EQ; DIVIDES_LE; NOT_SUC; DIVIDES_REFL;
                  ARITH_RULE `~(p <= n) /\ p <= SUC n ==> p = SUC n`]]);;

let EQ_PRIMEPOW = prove
 (`!p m n. prime p ==> (p EXP m = p EXP n <=> m = n)`,
  ONCE_REWRITE_TAC[GSYM LE_ANTISYM] THEN
  SIMP_TAC[LE_EXP; PRIME_IMP_NZ] THEN MESON_TAC[PRIME_1]);;

let COPRIME_2 = prove
 (`(!n. coprime(2,n) <=> ODD n) /\ (!n. coprime(n,2) <=> ODD n)`,
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [COPRIME_SYM] THEN
  SIMP_TAC[PRIME_COPRIME_EQ; PRIME_2; DIVIDES_2; NOT_EVEN]);;

let DIVIDES_EXP_PLUS1 = prove
 (`!n k. ODD k ==> (n + 1) divides (n EXP k + 1)`,
  GEN_TAC THEN REWRITE_TAC[ODD_EXISTS; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN REWRITE_TAC[FORALL_UNWIND_THM2] THEN
  INDUCT_TAC THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[EXP_1; DIVIDES_REFL] THEN
  REWRITE_TAC[ARITH_RULE `SUC(2 * SUC n) = SUC(2 * n) + 2`] THEN
  REWRITE_TAC[EXP_ADD; EXP_2] THEN POP_ASSUM MP_TAC THEN NUMBER_TAC);;

let DIVIDES_EXP_MINUS1 = prove
 (`!k n. (n - 1) divides (n EXP k - 1)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [STRUCT_CASES_TAC(SPEC `k:num` num_CASES) THEN
    ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[DIVIDES_REFL];
    REWRITE_TAC[num_divides] THEN
    ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB; LE_1; EXP_EQ_0; ARITH] THEN
    POP_ASSUM(K ALL_TAC) THEN REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN
    SPEC_TAC(`k:num`,`k:num`) THEN INDUCT_TAC THEN REWRITE_TAC[INT_POW] THEN
    REPEAT(POP_ASSUM MP_TAC) THEN INTEGER_TAC]);;

(* ------------------------------------------------------------------------- *)
(* One property of coprimality is easier to prove via prime factors.         *)
(* ------------------------------------------------------------------------- *)

let COPRIME_EXP_DIVPROD = prove
 (`!d n a b.
      (d EXP n) divides (a * b) /\ coprime(d,a) ==> (d EXP n) divides b`,
  MESON_TAC[COPRIME_DIVPROD; COPRIME_EXP; COPRIME_SYM]);;

let PRIME_COPRIME_CASES = prove
 (`!p a b. prime p /\ coprime(a,b) ==> coprime(p,a) \/ coprime(p,b)`,
  MESON_TAC[COPRIME_PRIME; PRIME_COPRIME_EQ]);;

let PRIME_DIVPROD_POW = prove
 (`!n p a b. prime(p) /\ coprime(a,b) /\ (p EXP n) divides (a * b)
             ==> (p EXP n) divides a \/ (p EXP n) divides b`,
  MESON_TAC[COPRIME_EXP_DIVPROD; PRIME_COPRIME_CASES; MULT_SYM]);;

let EXP_MULT_EXISTS = prove
 (`!m n p k. ~(m = 0) /\ m EXP k * n = p EXP k ==> ?q. n = q EXP k`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `k = 0` THEN
  ASM_REWRITE_TAC[EXP; MULT_CLAUSES] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`k:num`; `m:num`; `p:num`] DIVIDES_EXP2_REV) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[divides; MULT_SYM]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN DISCH_THEN(CHOOSE_THEN SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN
  ASM_REWRITE_TAC[MULT_EXP; GSYM MULT_ASSOC; EQ_MULT_LCANCEL; EXP_EQ_0] THEN
  MESON_TAC[]);;

let COPRIME_POW = prove
 (`!n a b c. coprime(a,b) /\ a * b = c EXP n
             ==> ?r s. a = r EXP n /\ b = s EXP n`,
  GEN_TAC THEN GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
  GEN_REWRITE_TAC I [SWAP_FORALL_THM] THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[EXP; MULT_EQ_1] THEN MATCH_MP_TAC PRIME_FACTOR_INDUCT THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[EXP_ZERO; MULT_EQ_0] THEN
    ASM_MESON_TAC[COPRIME_0; EXP_ZERO; COPRIME_0; EXP_ONE];
    SIMP_TAC[EXP_ONE; MULT_EQ_1] THEN MESON_TAC[EXP_ONE];
    REWRITE_TAC[MULT_EXP] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `p EXP n divides a \/ p EXP n divides b` MP_TAC THENL
     [ASM_MESON_TAC[PRIME_DIVPROD_POW; divides]; ALL_TAC] THEN
    REWRITE_TAC[divides] THEN
    DISCH_THEN(DISJ_CASES_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COPRIME_SYM]) THEN
    ASM_SIMP_TAC[COPRIME_RMUL; COPRIME_LMUL; COPRIME_LEXP; COPRIME_REXP] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`b:num`; `d:num`]);
      FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `a:num`])] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL
      [MATCH_MP_TAC(NUM_RING `!p. ~(p = 0) /\ a * p = b * p ==> a = b`) THEN
       EXISTS_TAC `p EXP n` THEN ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ] THEN
       FIRST_X_ASSUM(MP_TAC o SYM) THEN CONV_TAC NUM_RING;
       STRIP_TAC THEN ASM_REWRITE_TAC[GSYM MULT_EXP] THEN MESON_TAC[]])]);;

(* ------------------------------------------------------------------------- *)
(* More useful lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let PRIME_EXP = prove
 (`!p n. prime(p EXP n) <=> prime(p) /\ (n = 1)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[EXP; PRIME_1; ARITH_EQ] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN SPEC_TAC(`n:num`,`n:num`) THEN
  ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[PRIME_0; EXP; MULT_CLAUSES]; ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[ARITH; EXP_1; EXP; MULT_CLAUSES] THEN
  REWRITE_TAC[ARITH_RULE `~(SUC(SUC n) = 1)`] THEN
  REWRITE_TAC[prime; DE_MORGAN_THM] THEN
  ASM_REWRITE_TAC[MULT_EQ_1; EXP_EQ_1] THEN ASM_CASES_TAC `p = 1` THEN
  ASM_REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `p:num`) THEN ASM_REWRITE_TAC[NOT_IMP] THEN
  CONJ_TAC THENL [MESON_TAC[EXP; divides]; ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `p < pn:num ==> ~(p = pn)`) THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 EXP)] THEN
  ASM_REWRITE_TAC[LT_EXP; ARITH_EQ] THEN
  MAP_EVERY UNDISCH_TAC [`~(p = 0)`; `~(p = 1)`] THEN ARITH_TAC);;

let PRIME_POWER_MULT = prove
 (`!k x y p. prime p /\ (x * y = p EXP k)
           ==> ?i j. (x = p EXP i) /\ (y = p EXP j)`,
  INDUCT_TAC THEN REWRITE_TAC[EXP; MULT_EQ_1] THENL
   [MESON_TAC[EXP]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `p divides x \/ p divides y` MP_TAC THENL
   [ASM_MESON_TAC[PRIME_DIVPROD; divides; MULT_AC]; ALL_TAC] THEN
  REWRITE_TAC[divides] THEN
  SUBGOAL_THEN `~(p = 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_0]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `d:num` SUBST_ALL_TAC)) THENL
   [UNDISCH_TAC `(p * d) * y = p * p EXP k`;
    UNDISCH_TAC `x * p * d = p * p EXP k` THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [MULT_SYM]] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN
  ASM_REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `y:num`; `p:num`]);
    FIRST_X_ASSUM(MP_TAC o SPECL [`d:num`; `x:num`; `p:num`])] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[EXP]);;

let PRIME_POWER_EXP = prove
 (`!n x p k. prime p /\ ~(n = 0) /\ (x EXP n = p EXP k) ==> ?i. x = p EXP i`,
  INDUCT_TAC THEN REWRITE_TAC[EXP] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[NOT_SUC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[EXP] THEN
  ASM_MESON_TAC[PRIME_POWER_MULT]);;

let DIVIDES_PRIMEPOW = prove
 (`!p. prime p ==> !d. d divides (p EXP k) <=> ?i. i <= k /\ d = p EXP i`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `e:num` THEN
    DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`; `d:num`; `e:num`; `p:num`] PRIME_POWER_MULT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[GSYM EXP_ADD] THEN
    REWRITE_TAC[GSYM LE_ANTISYM; LE_EXP] THEN REWRITE_TAC[LE_ANTISYM] THEN
    POP_ASSUM MP_TAC THEN ASM_CASES_TAC `p = 0` THEN ASM_SIMP_TAC[PRIME_0] THEN
    ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[PRIME_1; LE_ANTISYM] THEN
    MESON_TAC[LE_ADD];
    REWRITE_TAC[LE_EXISTS] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[EXP_ADD] THEN MESON_TAC[DIVIDES_RMUL; DIVIDES_REFL]]);;

let PRIMEPOW_DIVIDES_PROD = prove
 (`!p k m n.
        prime p /\ (p EXP k) divides (m * n)
        ==> ?i j. (p EXP i) divides m /\ (p EXP j) divides n /\ k = i + j`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION_DECOMP) THEN
  REWRITE_TAC[NUMBER_RULE
   `a = b * c <=> b divides a /\ c divides a /\ b * c = a`] THEN
  ASM_MESON_TAC[EXP_ADD; EQ_PRIMEPOW; DIVIDES_PRIMEPOW]);;

let COPRIME_DIVISORS = prove
 (`!a b d e. d divides a /\ e divides b /\ coprime(a,b) ==> coprime(d,e)`,
  NUMBER_TAC);;

let PRIMEPOW_FACTOR = prove
 (`!n. 2 <= n
       ==> ?p k m. prime p /\ 1 <= k /\ coprime(p,m) /\ n = p EXP k * m`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `n:num` PRIME_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  REWRITE_TAC[divides; LEFT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k + 1`)) THEN
  ASM_REWRITE_TAC[ARITH_RULE `k < k + 1`; EXP_ADD; GSYM MULT_ASSOC] THEN
  ASM_SIMP_TAC[EQ_MULT_LCANCEL; EXP_EQ_0; PRIME_IMP_NZ] THEN
  REWRITE_TAC[EXP_1; GSYM divides] THEN UNDISCH_TAC `(p:num) divides n` THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `k = 0` THEN ASM_SIMP_TAC[EXP; MULT_CLAUSES; LE_1] THEN
  ASM_MESON_TAC[PRIME_COPRIME_STRONG]);;

let PRIMEPOW_DIVISORS_DIVIDES = prove
 (`!m n. m divides n <=>
         !p k. prime p /\ p EXP k divides m ==> p EXP k divides n`,
  REWRITE_TAC[TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN CONJ_TAC THENL
   [MESON_TAC[DIVIDES_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(LABEL_TAC "*") THEN X_GEN_TAC `n:num` THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THENL
   [MP_TAC(SPEC `n:num` EUCLID) THEN REWRITE_TAC[GT] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPECL [`p:num`; `1`]) THEN ASM_REWRITE_TAC[EXP_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
    ASM_SIMP_TAC[GSYM NOT_LT; DIVIDES_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[DIVIDES_1] THEN
  MP_TAC(SPEC `m:num` PRIMEPOW_FACTOR) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`p:num`; `k:num`; `r:num`] THEN STRIP_TAC THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPECL[`p:num`; `k:num`] th) THEN
    ASM_REWRITE_TAC[NUMBER_RULE `a divides (a * b)`] THEN
    ASSUME_TAC th) THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[GSYM divides] THEN
  MATCH_MP_TAC DIVIDES_MUL_L THEN REMOVE_THEN "*" (MP_TAC o SPEC `r:num`) THEN
  ASM_CASES_TAC `r = 0` THENL [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[ARITH_RULE `q < p * q <=> 1 * q < p * q`] THEN
  ASM_SIMP_TAC[LT_MULT_RCANCEL; ARITH_RULE `1 < p <=> ~(p = 0 \/ p = 1)`] THEN
  REWRITE_TAC[EXP_EQ_0; EXP_EQ_1] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PRIME_0; PRIME_1; LE_1]; ALL_TAC] THEN
  DISCH_THEN MATCH_MP_TAC THEN MAP_EVERY X_GEN_TAC [`q:num`; `l:num`] THEN
  ASM_CASES_TAC `l = 0` THEN ASM_REWRITE_TAC[EXP; DIVIDES_1] THEN
  STRIP_TAC THEN ASM_CASES_TAC `q:num = p` THENL
   [UNDISCH_TAC `coprime(p,r)` THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[coprime] THEN DISCH_THEN(MP_TAC o SPEC `p:num`) THEN
    ASM_SIMP_TAC[DIVIDES_REFL; PRIME_GE_2; ARITH_RULE
     `2 <= p ==> ~(p = 1)`] THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    TRANS_TAC DIVIDES_TRANS `p EXP l` THEN
    ASM_MESON_TAC[DIVIDES_REXP; DIVIDES_REFL];
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:num`; `l:num`]) THEN
    ASM_SIMP_TAC[DIVIDES_LMUL] THEN DISCH_THEN(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] COPRIME_EXP_DIVPROD)) THEN
    MATCH_MP_TAC COPRIME_EXP THEN ASM_MESON_TAC[DISTINCT_PRIME_COPRIME]]);;

let PRIMEPOW_DIVISORS_EQ = prove
 (`!m n. m = n <=>
         !p k. prime p ==> (p EXP k divides m <=> p EXP k divides n)`,
  MESON_TAC[DIVIDES_ANTISYM; PRIMEPOW_DIVISORS_DIVIDES]);;

(* ------------------------------------------------------------------------- *)
(* Index of a (usually prime) divisor of a number.                           *)
(* ------------------------------------------------------------------------- *)

let FINITE_EXP_LE = prove
 (`!P p n. 2 <= p ==> FINITE {j | P j /\ p EXP j <= n}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  SIMP_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; LE_0; IN_NUMSEG] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN TRANS_TAC LE_TRANS `p EXP i` THEN
  ASM_REWRITE_TAC[] THEN TRANS_TAC LE_TRANS `2 EXP i` THEN
  ASM_SIMP_TAC[EXP_MONO_LE_IMP; LT_POW2_REFL; LT_IMP_LE]);;

let FINITE_INDICES = prove
 (`!P p n. 2 <= p /\ ~(n = 0) ==> FINITE {j | P j /\ p EXP j divides n}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{j | P j /\ p EXP j <= n}` THEN
  ASM_SIMP_TAC[FINITE_EXP_LE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[DIVIDES_LE]);;

let index_def = new_definition
 `index p n = if p <= 1 \/ n = 0 then 0
              else CARD {j | 1 <= j /\ p EXP j divides n}`;;

let INDEX_0 = prove
 (`!p. index p 0 = 0`,
  REWRITE_TAC[index_def]);;

let PRIMEPOW_DIVIDES_INDEX = prove
 (`!n p k. p EXP k divides n <=> n = 0 \/ p = 1 \/ k <= index p n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INDEX_0; DIVIDES_0; EXP_EQ_0] THEN
  ASM_CASES_TAC `p = 0` THEN
  ASM_REWRITE_TAC[EXP_ZERO; COND_RAND; COND_RATOR] THEN
  ASM_SIMP_TAC[LE_0; DIVIDES_1; ARITH; index_def; DIVIDES_ZERO] THEN
  SIMP_TAC[CONJUNCT1 LE; COND_ID] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[EXP_ONE; DIVIDES_1] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC]  THEN
  SUBGOAL_THEN `2 <= p` ASSUME_TAC THENL  [ASM_ARITH_TAC; ALL_TAC]  THEN
  MP_TAC(ISPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:num` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k. p EXP k divides n <=> k <= a` ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL [ASM_MESON_TAC[NOT_LE]; ALL_TAC] THEN
    DISCH_TAC THEN TRANS_TAC DIVIDES_TRANS `p EXP a` THEN
    ASM_SIMP_TAC[DIVIDES_EXP_LE];
    ASM_REWRITE_TAC[GSYM numseg; CARD_NUMSEG_1]]);;

let LE_INDEX = prove
 (`!n p k. k <= index p n <=> (n = 0 \/ p = 1 ==> k = 0) /\ p EXP k divides n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PRIMEPOW_DIVIDES_INDEX] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[INDEX_0; CONJUNCT1 LE] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[index_def; ARITH; CONJUNCT1 LE]);;

let INDEX_1 = prove
 (`!p. index p 1 = 0`,
  GEN_TAC THEN REWRITE_TAC[index_def; ARITH] THEN COND_CASES_TAC THEN
  REWRITE_TAC[DIVIDES_ONE; EXP_EQ_1] THEN
  ASM_SIMP_TAC[ARITH_RULE `~(p <= 1) ==> ~(p = 1)`;
               ARITH_RULE `~(1 <= j /\ j = 0)`;
               EMPTY_GSPEC; CARD_CLAUSES]);;

let INDEX_MUL = prove
 (`!m n. prime p /\ ~(m = 0) /\ ~(n = 0)
         ==> index p (m * n) = index p m + index p n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  SUBGOAL_THEN `~(p = 1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[PRIME_1]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(MESON[LE_REFL]
     `(!k:num. k <= m ==> k <= n) ==> m <= n`) THEN
    MP_TAC(SPEC `p:num` PRIMEPOW_DIVIDES_PROD) THEN
    ASM_REWRITE_TAC[LE_INDEX; MULT_EQ_0] THEN ASM_MESON_TAC[LE_ADD2; LE_INDEX];
    ASM_REWRITE_TAC[LE_INDEX; MULT_EQ_0; EXP_ADD] THEN
    MATCH_MP_TAC DIVIDES_MUL2 THEN ASM_MESON_TAC[LE_INDEX; LE_REFL]]);;

let INDEX_EXP = prove
 (`!p n k. prime p ==> index p (n EXP k) = k * index p n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP_ZERO; INDEX_0; COND_RAND; COND_RATOR; INDEX_1;
                  MULT_CLAUSES; COND_ID] THEN
  INDUCT_TAC THEN
  ASM_SIMP_TAC[INDEX_MUL; EXP_EQ_0; EXP; INDEX_1; MULT_CLAUSES] THEN
  ARITH_TAC);;

let INDEX_FACT = prove
 (`!p n. prime p ==> index p (FACT n) = nsum(1..n) (\m. index p m)`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[FACT; NSUM_CLAUSES_NUMSEG; INDEX_1; ARITH] THEN
  ASM_SIMP_TAC[INDEX_MUL; NOT_SUC; FACT_NZ] THEN ARITH_TAC);;

let INDEX_FACT_ALT = prove
 (`!p n. prime p
         ==> index p (FACT n) =
             nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INDEX_FACT] THEN
  SUBGOAL_THEN `~(p = 0) /\ ~(p = 1) /\ 2 <= p /\ ~(p <= 1)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2) THEN ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[index_def; LE_1] THEN
  TRANS_TAC EQ_TRANS
   `nsum(1..n) (\m. nsum {j | 1 <= j /\ p EXP j <= n}
                         (\j. if p EXP j divides m then 1 else 0))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ_NUMSEG THEN X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM NSUM_RESTRICT_SET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_INDICES; LE_1; MULT_CLAUSES] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    ASM_MESON_TAC[DIVIDES_LE; LE_1; LE_TRANS];
    W(MP_TAC o PART_MATCH (lhs o rand) NSUM_SWAP o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; FINITE_EXP_LE] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `j:num` THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM NSUM_RESTRICT_SET] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; FINITE_RESTRICT; MULT_CLAUSES] THEN
    SUBGOAL_THEN `{m | m IN 1..n /\ p EXP j divides m} =
                  IMAGE (\q. p EXP j * q) (1..(n DIV p EXP j))`
     (fun th -> ASM_SIMP_TAC[CARD_IMAGE_INJ; FINITE_NUMSEG; EQ_MULT_LCANCEL;
                             th; EXP_EQ_0; PRIME_IMP_NZ; CARD_NUMSEG_1]) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG; IN_ELIM_THM; divides] THEN
    X_GEN_TAC `d:num` THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `q:num` THEN
    ASM_CASES_TAC `d = p EXP j * q` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; EXP_EQ_0; PRIME_IMP_NZ; MULT_EQ_0;
                 ARITH_RULE `1 <= x <=> ~(x = 0)`]]);;

let INDEX_FACT_UNBOUNDED = prove
 (`!p n. prime p
         ==> index p (FACT n) = nsum {j | 1 <= j} (\j. n DIV (p EXP j))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INDEX_FACT_ALT] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM; IMP_CONJ; DIV_EQ_0; EXP_EQ_0;
               PRIME_IMP_NZ; NOT_LE]);;

let PRIMEPOW_DIVIDES_FACT = prove
 (`!p n k. prime p
           ==> (p EXP k divides FACT n <=>
                k <= nsum {j | 1 <= j /\ p EXP j <= n} (\j. n DIV (p EXP j)))`,
  SIMP_TAC[PRIMEPOW_DIVIDES_INDEX; INDEX_FACT_ALT; FACT_NZ] THEN
  MESON_TAC[PRIME_1]);;

let INDEX_REFL = prove
 (`!n. index n n = if n <= 1 then 0 else 1`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[index_def] THEN
  ASM_CASES_TAC `n = 0` THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  ONCE_REWRITE_TAC[MESON[EXP_1] `a divides b <=> a divides b EXP 1`] THEN
  ASM_CASES_TAC `2 <= n` THENL [ALL_TAC; ASM_ARITH_TAC] THEN
  ASM_SIMP_TAC[DIVIDES_EXP_LE; GSYM numseg; CARD_NUMSEG_1]);;

let INDEX_EQ_0 = prove
 (`!p n. index p n = 0 <=> n = 0 \/ p = 1 \/ ~(p divides n)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `n = 0 <=> ~(1 <= n)`] THEN
  REWRITE_TAC[LE_INDEX; EXP_1; ARITH] THEN MESON_TAC[]);;

let INDEX_TRIVIAL_BOUND = prove
 (`!n p. index p n <= n`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `p:num`; `n:num`] PRIMEPOW_DIVIDES_INDEX) THEN
  REWRITE_TAC[index_def] THEN COND_CASES_TAC THEN REWRITE_TAC[LE_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM; NOT_LE]) THEN
  ASM_SIMP_TAC[ARITH_RULE `1 < p ==> ~(p = 1)`] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  MATCH_MP_TAC(ARITH_RULE `~(m:num <= n) ==> n <= m`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP DIVIDES_LE) THEN
  ASM_REWRITE_TAC[NOT_LE] THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 EXP n` THEN
  REWRITE_TAC[LT_POW2_REFL] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC);;

let INDEX_DECOMPOSITION = prove
 (`!n p. ?m. p EXP (index p n) * m = n /\ (n = 0 \/ p = 1 \/ ~(p divides m))`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`; `index p n`] LE_INDEX) THEN
  REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [divides]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`n:num`; `p:num`; `index p n + 1`] LE_INDEX) THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_EQ; ARITH_RULE `~(n + 1 <= n)`] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `p = 1` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXP_ADD; EXP_1; CONTRAPOS_THM] THEN
  FIRST_X_ASSUM(MP_TAC o SYM) THEN POP_ASSUM_LIST(K ALL_TAC) THEN
  NUMBER_TAC);;

let INDEX_DECOMPOSITION_PRIME = prove
 (`!n p. prime p ==> ?m. p EXP (index p n) * m = n /\ (n = 0 \/ coprime(p,m))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`n:num`; `p:num`] INDEX_DECOMPOSITION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
  ASM_CASES_TAC `p = 1` THENL [ASM_MESON_TAC[PRIME_1]; ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PRIME_COPRIME_STRONG]);;

(* ------------------------------------------------------------------------- *)
(* Least common multiples.                                                   *)
(* ------------------------------------------------------------------------- *)

let lcm = new_definition
 `lcm(m,n) = if m * n = 0 then 0 else (m * n) DIV gcd(m,n)`;;

let LCM_DIVIDES = prove
 (`!m n d. lcm(m,n) divides d <=> m divides d /\ n divides d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcm] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[DIVIDES_ZERO] THENL [MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  REWRITE_TAC[DIVIDES_ZERO] THENL [MESON_TAC[DIVIDES_0]; ALL_TAC] THEN
  ASM_REWRITE_TAC[MULT_EQ_0] THEN
  TRANS_TAC EQ_TRANS `(m * n) divides (gcd(m,n) * d)` THEN CONJ_TAC THENL
   [REWRITE_TAC[divides] THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `r:num` THEN TRANS_TAC EQ_TRANS
     `gcd(m,n) * d = gcd(m,n) * ((m * n) DIV gcd (m,n) * r)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[EQ_MULT_LCANCEL; GCD_ZERO];
      AP_TERM_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [MULT_SYM] THEN
      REWRITE_TAC[GSYM DIVIDES_DIV_MULT]];
    ALL_TAC] THEN
   REPEAT(POP_ASSUM MP_TAC) THEN NUMBER_TAC);;

let LCM = prove
 (`!m n. m divides lcm(m,n) /\
         n divides lcm(m,n) /\
         (!d. m divides d /\ n divides d ==> lcm(m,n) divides d)`,
  REPEAT GEN_TAC THEN SIMP_TAC[LCM_DIVIDES] THEN REWRITE_TAC[lcm] THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[DIVIDES_0; MULT_CLAUSES] THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO; DIVIDES_REFL; MULT_EQ_0] THEN
  CONJ_TAC THEN REWRITE_TAC[divides] THENL
   [EXISTS_TAC `n DIV gcd(m,n)`; EXISTS_TAC `m DIV gcd(m,n)`] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[GCD_ZERO; LE_1; ADD_CLAUSES] THEN CONV_TAC SYM_CONV THENL
   [ALL_TAC; GEN_REWRITE_TAC RAND_CONV [MULT_SYM]] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN NUMBER_TAC);;

let DIVIDES_LCM = prove
 (`!m n r. r divides m \/ r divides n
           ==> r divides lcm(m,n)`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM
   (MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] DIVIDES_TRANS)) THEN
  ASM_MESON_TAC[LCM]);;

let LCM_0 = prove
 (`(!n. lcm(0,n) = 0) /\ (!n. lcm(n,0) = 0)`,
  REWRITE_TAC[lcm; MULT_CLAUSES] THEN ARITH_TAC);;

let LCM_1 = prove
 (`(!n. lcm(1,n) = n) /\ (!n. lcm(n,1) = n)`,
  SIMP_TAC[lcm; MULT_CLAUSES; GCD_1; DIV_1] THEN MESON_TAC[]);;

let LCM_SYM = prove
 (`!m n. lcm(m,n) = lcm(n,m)`,
  REWRITE_TAC[lcm; MULT_SYM; GCD_SYM; ARITH_RULE `MAX m n = MAX n m`]);;

let DIVIDES_LCM_GCD = prove
 (`!m n d. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcm] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MULT_EQ_0; DE_MORGAN_THM]) THEN
  MP_TAC(NUMBER_RULE `gcd(m,n) divides m * n`) THEN
  SIMP_TAC[divides; LEFT_IMP_EXISTS_THM] THEN REWRITE_TAC[GSYM divides] THEN
  REPEAT STRIP_TAC THEN MP_TAC(SPECL [`m:num`; `n:num`] GCD_ZERO) THEN
  ASM_SIMP_TAC[DIV_MULT] THEN CONV_TAC NUMBER_RULE);;

let PRIMEPOW_DIVIDES_LCM = prove
 (`!m n p k.
        prime p
        ==> (p EXP k divides lcm(m,n) <=>
             p EXP k divides m \/ p EXP k divides n)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL [STRIP_TAC; MESON_TAC[DIVIDES_LCM]] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[LCM_0; DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[LCM_0; DIVIDES_0] THEN
  MP_TAC(SPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  MP_TAC(SPECL [`m:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; LEFT_IMP_EXISTS_THM; divides;
               LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num`; `q:num`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`b:num`; `r:num`] THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM divides] THEN
  UNDISCH_TAC `p EXP k divides lcm (m,n)` THEN
  ASM_REWRITE_TAC[DIVIDES_LCM_GCD] THEN
  SUBGOAL_THEN
   `gcd(p EXP a * q,p EXP b * r) =
    p EXP (MIN a b) * gcd(p EXP (a - MIN a b) * q,p EXP (b - MIN a b) * r)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM GCD_LMUL; MULT_ASSOC; GSYM EXP_ADD] THEN
    AP_TERM_TAC THEN BINOP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN ARITH_TAC;
    REWRITE_TAC[MULT_ASSOC; GSYM EXP_ADD]] THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP (NUMBER_RULE `a * b divides c ==> a divides c`)) THEN
  REWRITE_TAC[ARITH_RULE `((a * b) * c) * d:num = (a * c) * b * d`] THEN
  REWRITE_TAC[GSYM EXP_ADD] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
   (ONCE_REWRITE_RULE[MULT_SYM] COPRIME_EXP_DIVPROD))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC COPRIME_MUL THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[PRIME_COPRIME_STRONG]
      `prime p /\ ~(p divides n) ==> coprime(p,n)`) THEN
    ASM_REWRITE_TAC[divides] THEN STRIP_TAC THENL
     [UNDISCH_TAC `!l. a < l ==> ~(?x. m = p EXP l * x)` THEN
      DISCH_THEN(MP_TAC o SPEC `a + 1`);
      UNDISCH_TAC `!l. b < l ==> ~(?x. n = p EXP l * x)` THEN
      DISCH_THEN(MP_TAC o SPEC `b + 1`)] THEN
    ASM_REWRITE_TAC[ARITH_RULE `a < a + 1`; EXP_ADD; EXP_1] THEN
    MESON_TAC[MULT_AC];
    ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `k + MIN a b <= a + b ==> k <= a \/ k <= b`)) THEN
    MATCH_MP_TAC MONO_OR THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIVIDES_RMUL THEN ASM_SIMP_TAC[DIVIDES_EXP_LE; PRIME_GE_2]]);;

let LCM_ZERO = prove
 (`!m n. lcm(m,n) = 0 <=> m = 0 \/ n = 0`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [MULTIPLES_EQ] THEN
  REWRITE_TAC[LCM_DIVIDES; DIVIDES_ZERO] THEN
  MAP_EVERY ASM_CASES_TAC [`m = 0`; `n = 0`] THEN
  ASM_REWRITE_TAC[DIVIDES_ZERO] THEN
  ASM_MESON_TAC[DIVIDES_REFL; MULT_EQ_0; DIVIDES_LMUL; DIVIDES_RMUL]);;

let LCM_ASSOC = prove
 (`!m n p. lcm(m,lcm(n,p)) = lcm(lcm(m,n),p)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULTIPLES_EQ] THEN
  REWRITE_TAC[LCM_DIVIDES] THEN X_GEN_TAC `q:num` THEN
  REWRITE_TAC[LCM_ZERO] THEN CONV_TAC TAUT);;

let LCM_REFL = prove
 (`!n. lcm(n,n) = n`,
  REWRITE_TAC[lcm; GCD_REFL; MULT_EQ_0; ARITH_RULE `MAX n n = n`] THEN
  SIMP_TAC[DIV_MULT] THEN MESON_TAC[]);;

let LCM_MULTIPLE = prove
 (`!a b. lcm(b,a * b) = a * b`,
  REWRITE_TAC[MULTIPLES_EQ; LCM_DIVIDES] THEN NUMBER_TAC);;

let LCM_GCD_DISTRIB = prove
 (`!a b c. lcm(a,gcd(b,c)) = gcd(lcm(a,b),lcm(a,c))`,
  REWRITE_TAC[PRIMEPOW_DIVISORS_EQ] THEN
  SIMP_TAC[PRIMEPOW_DIVIDES_LCM; DIVIDES_GCD] THEN CONV_TAC TAUT);;

let GCD_LCM_DISTRIB = prove
 (`!a b c. gcd(a,lcm(b,c)) = lcm(gcd(a,b),gcd(a,c))`,
  REWRITE_TAC[PRIMEPOW_DIVISORS_EQ] THEN
  SIMP_TAC[PRIMEPOW_DIVIDES_LCM; DIVIDES_GCD] THEN CONV_TAC TAUT);;

let LCM_UNIQUE = prove
 (`!d m n.
       m divides d /\ n divides d /\
       (!e. m divides e /\ n divides e ==> d divides e) <=>
       d = lcm(m,n)`,
  REWRITE_TAC[MULTIPLES_EQ; LCM_DIVIDES] THEN
  MESON_TAC[DIVIDES_REFL; DIVIDES_TRANS]);;

let LCM_EQ = prove
 (`!x y u v. (!d. x divides d /\ y divides d <=> u divides d /\ v divides d)
             ==> lcm(x,y) = lcm(u,v)`,
  SIMP_TAC[MULTIPLES_EQ; LCM_DIVIDES]);;

let LCM_LMUL = prove
 (`!a b c. lcm(c * a,c * b) = c * lcm(a,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `c = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LCM_0] THEN
  ASM_REWRITE_TAC[lcm; GCD_LMUL; MULT_EQ_0; DISJ_ACI] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  ASM_SIMP_TAC[GSYM MULT_ASSOC; DIV_MULT2; MULT_EQ_0; GCD_ZERO] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LE_1; GCD_ZERO] THEN
  ONCE_REWRITE_TAC[ARITH_RULE
    `a * c * b:num = (c * d) * g <=> c * d * g = c * a * b`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  CONV_TAC NUMBER_RULE);;

let LCM_RMUL = prove
 (`!a b c. lcm(a * c,b * c) = c * lcm(a,b)`,
  MESON_TAC[LCM_LMUL; MULT_SYM]);;

let LCM_EXP = prove
 (`!n a b. lcm(a EXP n,b EXP n) = lcm(a,b) EXP n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lcm] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[EXP; GCD_REFL; DIV_1; MULT_CLAUSES] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
   [ASM_MESON_TAC[num_CASES; EXP_0]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  REWRITE_TAC[GCD_EXP; GSYM MULT_EXP] THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `0` THEN
  ASM_SIMP_TAC[ADD_CLAUSES; LE_1; GCD_ZERO; EXP_EQ_0] THEN
  REWRITE_TAC[GSYM MULT_EXP] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM DIVIDES_DIV_MULT] THEN
  CONV_TAC NUMBER_RULE);;

(* ------------------------------------------------------------------------- *)
(* Induction principle for multiplicative functions etc.                     *)
(* ------------------------------------------------------------------------- *)

let INDUCT_COPRIME = prove
 (`!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (ARITH_RULE `1 < n ==> ~(n = 1)`)) THEN
  DISCH_THEN(X_CHOOSE_TAC `p:num` o MATCH_MP PRIME_FACTOR) THEN
  MP_TAC(SPECL [`n:num`; `p:num`] FACTORIZATION_INDEX) THEN
  ASM_SIMP_TAC[PRIME_GE_2; ARITH_RULE `1 < n ==> ~(n = 0)`] THEN
  REWRITE_TAC[divides; LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:num`; `m:num`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `m = 1` THEN ASM_SIMP_TAC[MULT_CLAUSES] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 MATCH_MP_TAC MP_TAC) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(TAUT
   `!p. (a /\ b /\ ~p) /\ c /\ (a /\ ~p ==> b ==> d)
        ==> a /\ b /\ c /\ d`) THEN
  EXISTS_TAC `m = 0` THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `0 < 1`)) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[EXP; EXP_1; MULT_CLAUSES; divides];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `1 < p EXP k * m` THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 < x <=> ~(x = 0) /\ ~(x = 1)`] THEN
    ASM_REWRITE_TAC[EXP_EQ_0; EXP_EQ_1; MULT_EQ_0; MULT_EQ_1] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP PRIME_GE_2 o CONJUNCT1) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ARITH_RULE `k < k + 1`)) THEN
    REWRITE_TAC[EXP_ADD; EXP_1; GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
    ASM_SIMP_TAC[EXP_EQ_0; PRIME_IMP_NZ; GSYM divides] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[COPRIME_SYM] THEN MATCH_MP_TAC COPRIME_EXP THEN
    ASM_MESON_TAC[PRIME_COPRIME; COPRIME_SYM];
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `m = 1 * m`] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL]]);;

let INDUCT_COPRIME_STRONG = prove
 (`!P. (!a b. 1 < a /\ 1 < b /\ coprime(a,b) /\ P a /\ P b ==> P(a * b)) /\
       (!p k. prime p /\ ~(k = 0) ==> P(p EXP k))
       ==> !n. 1 < n ==> P n`,
  GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b <=> a ==> a ==> b`] THEN
  MATCH_MP_TAC INDUCT_COPRIME THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`p:num`; `k:num`] THEN ASM_CASES_TAC `k = 0` THEN
    ASM_REWRITE_TAC[LT_REFL; EXP] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A conversion for divisibility.                                            *)
(* ------------------------------------------------------------------------- *)

let DIVIDES_CONV =
  let pth_0 = SPEC `b:num` DIVIDES_ZERO
  and pth_1 = prove
   (`~(a = 0) ==> (a divides b <=> (b MOD a = 0))`,
    REWRITE_TAC[DIVIDES_MOD])
  and a_tm = `a:num` and b_tm = `b:num` and zero_tm = `0`
  and dest_divides = dest_binop `(divides)` in
  fun tm ->
     let a,b = dest_divides tm in
     if a = zero_tm then
       CONV_RULE (RAND_CONV NUM_EQ_CONV) (INST [b,b_tm] pth_0)
     else
       let th1 = INST [a,a_tm; b,b_tm] pth_1 in
       let th2 = MP th1 (EQF_ELIM(NUM_EQ_CONV(rand(lhand(concl th1))))) in
       CONV_RULE (RAND_CONV (LAND_CONV NUM_MOD_CONV THENC NUM_EQ_CONV)) th2;;

(* ------------------------------------------------------------------------- *)
(* A conversion for coprimality.                                             *)
(* ------------------------------------------------------------------------- *)

let COPRIME_CONV =
  let pth_yes_l = prove
   (`(m * x = n * y + 1) ==> (coprime(m,n) <=> T)`,
    MESON_TAC[coprime; DIVIDES_RMUL; DIVIDES_ADD_REVR; DIVIDES_ONE])
  and pth_yes_r = prove
   (`(m * x = n * y + 1) ==> (coprime(n,m) <=> T)`,
    MESON_TAC[coprime; DIVIDES_RMUL; DIVIDES_ADD_REVR; DIVIDES_ONE])
  and pth_no = prove
   (`(m = x * d) /\ (n = y * d) /\ ~(d = 1) ==> (coprime(m,n) <=> F)`,
    REWRITE_TAC[coprime; divides] THEN MESON_TAC[MULT_AC])
  and pth_oo = prove
   (`coprime(0,0) <=> F`,
    MESON_TAC[coprime; DIVIDES_REFL; NUM_REDUCE_CONV `1 = 0`])
  and m_tm = `m:num` and n_tm = `n:num`
  and x_tm = `x:num` and y_tm = `y:num`
  and d_tm = `d:num` and coprime_tm = `coprime` in
  let rec bezout (m,n) =
    if m =/ Int 0 then (Int 0,Int 1) else if n =/ Int 0 then (Int 1,Int 0)
    else if m <=/ n then
      let q = quo_num n m and r = mod_num n m in
      let (x,y) = bezout(m,r) in
      (x -/ q */ y,y)
    else let (x,y) = bezout(n,m) in (y,x) in
  fun tm ->
   let pop,ptm = dest_comb tm in
   if pop <> coprime_tm then failwith "COPRIME_CONV" else
   let l,r = dest_pair ptm in
   let m = dest_numeral l and n = dest_numeral r in
   if m =/ Int 0 & n =/ Int 0 then pth_oo else
   let (x,y) = bezout(m,n) in
   let d = x */ m +/ y */ n in
   let th =
     if d =/ Int 1 then
       if x >/ Int 0 then
          INST [l,m_tm; r,n_tm; mk_numeral x,x_tm;
                mk_numeral(minus_num y),y_tm] pth_yes_l
       else
          INST [r,m_tm; l,n_tm; mk_numeral(minus_num x),y_tm;
                mk_numeral y,x_tm] pth_yes_r
     else
         INST [l,m_tm; r,n_tm; mk_numeral d,d_tm;
              mk_numeral(m // d),x_tm; mk_numeral(n // d),y_tm] pth_no in
    MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

(* ------------------------------------------------------------------------- *)
(* More general (slightly less efficiently coded) GCD_CONV, and LCM_CONV.    *)
(* ------------------------------------------------------------------------- *)

let GCD_CONV =
  let pth0 = prove(`gcd(0,0) = 0`,REWRITE_TAC[GCD_0]) in
  let pth1 = prove
   (`!m n x y d m' n'.
      (m * x = n * y + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)`,
    REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    CONV_TAC(RAND_CONV SYM_CONV) THEN ASM_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
    ASM_MESON_TAC[DIVIDES_LMUL; DIVIDES_RMUL;
                  DIVIDES_ADD_REVR; DIVIDES_REFL]) in
  let pth2 = prove
   (`!m n x y d m' n'.
       (n * y = m * x + d) /\ (m = m' * d) /\ (n = n' * d) ==> (gcd(m,n) = d)`,
    MESON_TAC[pth1; GCD_SYM]) in
  let gcd_tm = `gcd` in
  let rec bezout (m,n) =
    if m =/ Int 0 then (Int 0,Int 1) else if n =/ Int 0 then (Int 1,Int 0)
    else if m <=/ n then
      let q = quo_num n m and r = mod_num n m in
      let (x,y) = bezout(m,r) in
      (x -/ q */ y,y)
    else let (x,y) = bezout(n,m) in (y,x) in
  fun tm -> let gt,lr = dest_comb tm in
            if gt <> gcd_tm then failwith "GCD_CONV" else
            let mtm,ntm = dest_pair lr in
            let m = dest_numeral mtm and n = dest_numeral ntm in
            if m =/ Int 0 & n =/ Int 0 then pth0 else
            let x0,y0 = bezout(m,n) in
            let x = abs_num x0 and y = abs_num y0 in
            let xtm = mk_numeral x and ytm = mk_numeral y in
            let d = abs_num(x */ m -/ y */ n) in
            let dtm = mk_numeral d in
            let m' = m // d and n' = n // d in
            let mtm' = mk_numeral m' and ntm' = mk_numeral n' in
            let th = SPECL [mtm;ntm;xtm;ytm;dtm;mtm';ntm']
             (if m */ x =/ n */ y +/ d then pth1 else pth2) in
            MP th (EQT_ELIM(NUM_REDUCE_CONV(lhand(concl th))));;

let LCM_CONV =
  GEN_REWRITE_CONV I [lcm] THENC
  RATOR_CONV(LAND_CONV(LAND_CONV NUM_MULT_CONV THENC NUM_EQ_CONV)) THENC
  (GEN_REWRITE_CONV I [CONJUNCT1(SPEC_ALL COND_CLAUSES)] ORELSEC
   (GEN_REWRITE_CONV I [CONJUNCT2(SPEC_ALL COND_CLAUSES)] THENC
    COMB2_CONV (RAND_CONV NUM_MULT_CONV) GCD_CONV THENC NUM_DIV_CONV));;

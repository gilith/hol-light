(* ========================================================================= *)
(* Lebesgue measure, measurable functions (defined via the gauge integral).  *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

needs "Library/card.ml";;
needs "Library/permutations.ml";;
needs "Multivariate/integration.ml";;
needs "Multivariate/determinants.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measure in the case where the measure is finite. This is our     *)
(* default notion of "measurable", but we also define "lebesgue_measurable"  *)
(* further down. Note that in neither case do we assume the set is bounded.  *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("has_measure",(12,"right"));;

let has_measure = new_definition
 `s has_measure m <=> ((\x. vec 1) has_integral (lift m)) s`;;

let measurable = new_definition
 `measurable s <=> ?m. s has_measure m`;;

let measure = new_definition
 `measure s = @m. s has_measure m`;;

let HAS_MEASURE_MEASURE = prove
 (`!s. measurable s <=> s has_measure (measure s)`,
  REWRITE_TAC[measure; measurable] THEN MESON_TAC[]);;

let HAS_MEASURE_UNIQUE = prove
 (`!s m1 m2. s has_measure m1 /\ s has_measure m2 ==> m1 = m2`,
  REWRITE_TAC[has_measure; GSYM LIFT_EQ] THEN MESON_TAC[HAS_INTEGRAL_UNIQUE]);;

let MEASURE_UNIQUE = prove
 (`!s m. s has_measure m ==> measure s = m`,
  MESON_TAC[HAS_MEASURE_UNIQUE; HAS_MEASURE_MEASURE; measurable]);;

let HAS_MEASURE_MEASURABLE_MEASURE = prove
 (`!s m. s has_measure m <=> measurable s /\ measure s = m`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN MESON_TAC[MEASURE_UNIQUE]);;

let HAS_MEASURE_IMP_MEASURABLE = prove
 (`!s m. s has_measure m ==> measurable s`,
  REWRITE_TAC[measurable] THEN MESON_TAC[]);;

let HAS_MEASURE = prove
 (`!s m. s has_measure m <=>
              ((\x. if x IN s then vec 1 else vec 0) has_integral (lift m))
              (:real^N)`,
  SIMP_TAC[HAS_INTEGRAL_RESTRICT_UNIV; has_measure]);;

let MEASURABLE = prove
 (`!s. measurable s <=> (\x. vec 1:real^1) integrable_on s`,
  REWRITE_TAC[measurable; integrable_on;
              has_measure; EXISTS_DROP; LIFT_DROP]);;

let MEASURABLE_INTEGRABLE = prove
 (`measurable s <=>
     (\x. if x IN s then vec 1 else vec 0:real^1) integrable_on UNIV`,
  REWRITE_TAC[measurable; integrable_on;
              HAS_MEASURE; EXISTS_DROP; LIFT_DROP]);;

let MEASURE_INTEGRAL = prove
 (`!s. measurable s ==> measure s = drop (integral s (\x. vec 1))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM has_measure; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_INTEGRAL_UNIV = prove
 (`!s. measurable s
       ==> measure s =
           drop(integral UNIV (\x. if x IN s then vec 1 else vec 0))`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[GSYM LIFT_EQ; LIFT_DROP] THEN
  MATCH_MP_TAC INTEGRAL_UNIQUE THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; GSYM HAS_MEASURE_MEASURE]);;

let INTEGRAL_MEASURE = prove
 (`!s. measurable s ==> integral s (\x. vec 1) = lift(measure s)`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; MEASURE_INTEGRAL]);;

let INTEGRAL_MEASURE_UNIV = prove
 (`!s. measurable s
       ==> integral UNIV (\x. if x IN s then vec 1 else vec 0) =
           lift(measure s)`,
  SIMP_TAC[GSYM DROP_EQ; LIFT_DROP; MEASURE_INTEGRAL_UNIV]);;

let HAS_MEASURE_INTERVAL = prove
 (`(!a b:real^N. interval[a,b] has_measure content(interval[a,b])) /\
   (!a b:real^N. interval(a,b) has_measure content(interval[a,b]))`,
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [REWRITE_TAC[has_measure] THEN
    ONCE_REWRITE_TAC[LIFT_EQ_CMUL] THEN REWRITE_TAC[HAS_INTEGRAL_CONST];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN SIMP_TAC[HAS_MEASURE] THEN
  MATCH_MP_TAC(REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
                           HAS_INTEGRAL_SPIKE) THEN
  EXISTS_TAC `interval[a:real^N,b] DIFF interval(a,b)` THEN
  REWRITE_TAC[NEGLIGIBLE_FRONTIER_INTERVAL] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

let MEASURABLE_INTERVAL = prove
 (`(!a b:real^N. measurable (interval[a,b])) /\
   (!a b:real^N. measurable (interval(a,b)))`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_INTERVAL]);;

let MEASURE_INTERVAL = prove
 (`(!a b:real^N. measure(interval[a,b]) = content(interval[a,b])) /\
   (!a b:real^N. measure(interval(a,b)) = content(interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  REWRITE_TAC[HAS_MEASURE_INTERVAL]);;

let MEASURE_INTERVAL_1 = prove
 (`(!a b:real^1. measure(interval[a,b]) =
                    if drop a <= drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a <= drop b then drop b - drop a else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; PRODUCT_1; drop]);;

let MEASURE_INTERVAL_1_ALT = prove
 (`(!a b:real^1. measure(interval[a,b]) =
                    if drop a < drop b then drop b - drop a else &0) /\
   (!a b:real^1. measure(interval(a,b)) =
                    if drop a < drop b then drop b - drop a else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_1] THEN REAL_ARITH_TAC);;

let MEASURE_INTERVAL_2 = prove
 (`(!a b:real^2. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_2; FORALL_2; PRODUCT_2]);;

let MEASURE_INTERVAL_2_ALT = prove
 (`(!a b:real^2. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0) /\
   (!a b:real^2. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2
                 then (b$1 - a$1) * (b$2 - a$2)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_2] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`(a:real^2)$1 = (b:real^2)$1`; `(a:real^2)$2 = (b:real^2)$2`] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  REAL_SUB_REFL; REAL_LE_REFL; REAL_ABS_NUM; COND_ID] THEN
  ASM_REWRITE_TAC[REAL_LT_LE]);;

let MEASURE_INTERVAL_3 = prove
 (`(!a b:real^3. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; PRODUCT_3]);;

let MEASURE_INTERVAL_3_ALT = prove
 (`(!a b:real^3. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0) /\
   (!a b:real^3. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_3] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`(a:real^3)$1 = (b:real^3)$1`;
    `(a:real^3)$2 = (b:real^3)$2`;
    `(a:real^3)$3 = (b:real^3)$3`] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  REAL_SUB_REFL; REAL_LE_REFL; REAL_ABS_NUM; COND_ID] THEN
  ASM_REWRITE_TAC[REAL_LT_LE]);;

let MEASURE_INTERVAL_4 = prove
 (`(!a b:real^4. measure(interval[a,b]) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3 /\ a$4 <= b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0) /\
   (!a b:real^4. measure(interval(a,b)) =
                 if a$1 <= b$1 /\ a$2 <= b$2 /\ a$3 <= b$3 /\ a$4 <= b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[DIMINDEX_4; FORALL_4; PRODUCT_4]);;

let MEASURE_INTERVAL_4_ALT = prove
 (`(!a b:real^4. measure(interval[a,b]) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3 /\ a$4 < b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0) /\
   (!a b:real^4. measure(interval(a,b)) =
                 if a$1 < b$1 /\ a$2 < b$2 /\ a$3 < b$3 /\ a$4 < b$4
                 then (b$1 - a$1) * (b$2 - a$2) * (b$3 - a$3) * (b$4 - a$4)
                 else &0)`,
  REWRITE_TAC[MEASURE_INTERVAL_4] THEN REPEAT GEN_TAC THEN
  MAP_EVERY ASM_CASES_TAC
   [`(a:real^4)$1 = (b:real^4)$1`;
    `(a:real^4)$2 = (b:real^4)$2`;
    `(a:real^4)$3 = (b:real^4)$3`;
    `(a:real^4)$4 = (b:real^4)$4`] THEN
  ASM_REWRITE_TAC[REAL_LT_REFL; REAL_MUL_LZERO; REAL_MUL_RZERO;
                  REAL_SUB_REFL; REAL_LE_REFL; REAL_ABS_NUM; COND_ID] THEN
  ASM_REWRITE_TAC[REAL_LT_LE]);;

let MEASURABLE_INTER = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s INTER t)`,
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  SUBGOAL_THEN
   `(\x. if x IN s INTER t then vec 1 else vec 0):real^N->real^1 =
    (\x. lambda i. min (((if x IN s then vec 1 else vec 0):real^1)$i)
                       (((if x IN t then vec 1 else vec 0):real^1)$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(x:real^N) IN s`; `(x:real^N) IN t`] THEN
    ASM_SIMP_TAC[IN_INTER; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN THEN
  CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS]);;

let MEASURABLE_UNION = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s UNION t)`,
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  SUBGOAL_THEN
   `(\x. if x IN s UNION t then vec 1 else vec 0):real^N->real^1 =
    (\x. lambda i. max (((if x IN s then vec 1 else vec 0):real^1)$i)
                       (((if x IN t then vec 1 else vec 0):real^1)$i))`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
    X_GEN_TAC `x:real^N` THEN REPEAT STRIP_TAC THEN
    MAP_EVERY ASM_CASES_TAC [`(x:real^N) IN s`; `(x:real^N) IN t`] THEN
    ASM_SIMP_TAC[IN_UNION; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX THEN
  CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
  ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[VEC_COMPONENT; REAL_POS]);;

let HAS_MEASURE_DISJOINT_UNION = prove
 (`!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ DISJOINT s1 s2
                 ==> (s1 UNION s2) has_measure (m1 + m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_MEASURE; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_ADD) THEN
  REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN REWRITE_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID]) THEN
  ASM SET_TAC[]);;

let MEASURE_DISJOINT_UNION = prove
 (`!s t. measurable s /\ measurable t /\ DISJOINT s t
         ==> measure(s UNION t) = measure s + measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNION; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_DISJOINT_UNION_EQ = prove
 (`!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ DISJOINT s t
        ==> measure s + measure t = measure u`,
  MESON_TAC[MEASURE_DISJOINT_UNION]);;

let HAS_MEASURE_POS_LE = prove
 (`!m s:real^N->bool. s has_measure m ==> &0 <= m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  REWRITE_TAC[drop] THEN MATCH_MP_TAC(ISPEC
   `(\x. if x IN s then vec 1 else vec 0):real^N->real^1`
   HAS_INTEGRAL_COMPONENT_POS) THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[DIMINDEX_1; ARITH; IN_UNIV] THEN
  GEN_TAC THEN COND_CASES_TAC THEN
  REWRITE_TAC[GSYM drop; DROP_VEC; REAL_POS]);;

let MEASURE_POS_LE = prove
 (`!s. measurable s ==> &0 <= measure s`,
  REWRITE_TAC[HAS_MEASURE_MEASURE; HAS_MEASURE_POS_LE]);;

let HAS_MEASURE_SUBSET = prove
 (`!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ s1 SUBSET s2
        ==> m1 <= m2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[has_measure] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  MATCH_MP_TAC(ISPEC `(\x. vec 1):real^N->real^1`
    HAS_INTEGRAL_SUBSET_DROP_LE) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[DROP_VEC; REAL_POS]);;

let MEASURE_SUBSET = prove
 (`!s t. measurable s /\ measurable t /\ s SUBSET t
         ==> measure s <= measure t`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN MESON_TAC[HAS_MEASURE_SUBSET]);;

let HAS_MEASURE_0 = prove
 (`!s:real^N->bool. s has_measure &0 <=> negligible s`,
  GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[NEGLIGIBLE; has_measure] THEN
    DISCH_THEN(MP_TAC o SPEC `(:real^N)`) THEN
    ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC[IN_UNIV; indicator; LIFT_NUM]] THEN
  REWRITE_TAC[negligible] THEN REWRITE_TAC[has_measure] THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[LIFT_NUM] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [HAS_INTEGRAL_ALT]) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  REWRITE_TAC[integrable_on; IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[indicator] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^1`) THEN
  SUBGOAL_THEN `y:real^1 = vec 0` (fun th -> ASM_MESON_TAC[th]) THEN
  REWRITE_TAC[GSYM DROP_EQ; GSYM REAL_LE_ANTISYM] THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ISPEC
     `(\x. if x IN interval [a,b]
           then if x IN s then vec 1 else vec 0 else vec 0):real^N->real^1`
     HAS_INTEGRAL_DROP_LE) THEN
    EXISTS_TAC `(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    REWRITE_TAC[DROP_VEC] THEN MATCH_MP_TAC(ISPEC
     `(\x. if x IN interval [a,b]
           then if x IN s then vec 1 else vec 0 else vec 0):real^N->real^1`
     HAS_INTEGRAL_DROP_POS)] THEN
  EXISTS_TAC `(:real^N)` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]);;

let MEASURE_EQ_0 = prove
 (`!s. negligible s ==> measure s = &0`,
  MESON_TAC[MEASURE_UNIQUE; HAS_MEASURE_0]);;

let NEGLIGIBLE_IMP_MEASURABLE = prove
 (`!s:real^N->bool. negligible s ==> measurable s`,
  MESON_TAC[HAS_MEASURE_0; measurable]);;

let HAS_MEASURE_EMPTY = prove
 (`{} has_measure &0`,
  REWRITE_TAC[HAS_MEASURE_0; NEGLIGIBLE_EMPTY]);;

let MEASURE_EMPTY = prove
 (`measure {} = &0`,
  SIMP_TAC[MEASURE_EQ_0; NEGLIGIBLE_EMPTY]);;

let MEASURABLE_EMPTY = prove
 (`measurable {}`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_EMPTY]);;

let MEASURABLE_SING = prove
 (`!a:real^N. measurable {a}`,
  MESON_TAC[NEGLIGIBLE_IMP_MEASURABLE; NEGLIGIBLE_SING]);;

let MEASURABLE_MEASURE_EQ_0 = prove
 (`!s. measurable s ==> (measure s = &0 <=> negligible s)`,
  REWRITE_TAC[HAS_MEASURE_MEASURE; GSYM HAS_MEASURE_0] THEN
  MESON_TAC[MEASURE_UNIQUE]);;

let NEGLIGIBLE_EQ_MEASURE_0 = prove
 (`!s:real^N->bool.
        negligible s <=> measurable s /\ measure s = &0`,
  MESON_TAC[NEGLIGIBLE_IMP_MEASURABLE; MEASURABLE_MEASURE_EQ_0]);;

let MEASURE_SING = prove
 (`!a:real^N. measure {a} = &0`,
  MESON_TAC[NEGLIGIBLE_EQ_MEASURE_0; NEGLIGIBLE_SING]);;

let MEASURABLE_MEASURE_POS_LT = prove
 (`!s. measurable s ==> (&0 < measure s <=> ~negligible s)`,
  SIMP_TAC[REAL_LT_LE; MEASURE_POS_LE; GSYM MEASURABLE_MEASURE_EQ_0] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

let NEGLIGIBLE_INTERVAL = prove
 (`(!a b. negligible(interval[a,b]) <=> interval(a,b) = {}) /\
   (!a b. negligible(interval(a,b)) <=> interval(a,b) = {})`,
  REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
  MESON_TAC[HAS_MEASURE_INTERVAL; CONTENT_EQ_0_INTERIOR;
            INTERIOR_CLOSED_INTERVAL; HAS_MEASURE_UNIQUE]);;

let MEASURABLE_UNIONS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measurable (UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; MEASURABLE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_UNION THEN ASM_SIMP_TAC[]);;

let HAS_MEASURE_DIFF_SUBSET = prove
 (`!s1 s2 m1 m2. s1 has_measure m1 /\ s2 has_measure m2 /\ s2 SUBSET s1
                 ==> (s1 DIFF s2) has_measure (m1 - m2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_MEASURE; CONJ_ASSOC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
  REWRITE_TAC[LIFT_SUB] THEN MATCH_MP_TAC EQ_IMP THEN
  AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
  REWRITE_TAC[VECTOR_SUB_REFL; VECTOR_SUB_RZERO] THEN
  ASM SET_TAC[]);;

let MEASURABLE_DIFF = prove
 (`!s t:real^N->bool. measurable s /\ measurable t ==> measurable (s DIFF t)`,
  SUBGOAL_THEN
   `!s t:real^N->bool. measurable s /\ measurable t /\ t SUBSET s
         ==> measurable (s DIFF t)`
  ASSUME_TAC THENL
   [REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_DIFF_SUBSET];
    ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s DIFF (s INTER t)`] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[MEASURABLE_INTER] THEN
    SET_TAC[]]);;

let MEASURE_DIFF_SUBSET = prove
 (`!s t. measurable s /\ measurable t /\ t SUBSET s
         ==> measure(s DIFF t) = measure s - measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_SUBSET; GSYM HAS_MEASURE_MEASURE]);;

let HAS_MEASURE_UNION_NEGLIGIBLE = prove
 (`!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s UNION t) has_measure m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    `t:real^N->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF; IN_UNIV; IN_UNION]);;

let HAS_MEASURE_DIFF_NEGLIGIBLE = prove
 (`!s t:real^N->bool m.
        s has_measure m /\ negligible t ==> (s DIFF t) has_measure m`,
  REWRITE_TAC[HAS_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
    `t:real^N->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF; IN_UNIV; IN_UNION]);;

let HAS_MEASURE_UNION_NEGLIGIBLE_EQ = prove
 (`!s t:real^N->bool m.
     negligible t ==> ((s UNION t) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_UNION_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s UNION t) DIFF (t DIFF s)`) THEN
  MATCH_MP_TAC HAS_MEASURE_DIFF_NEGLIGIBLE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFF THEN ASM_REWRITE_TAC[]);;

let HAS_MEASURE_DIFF_NEGLIGIBLE_EQ = prove
 (`!s t:real^N->bool m.
     negligible t ==> ((s DIFF t) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE] THEN
  SUBST1_TAC(SET_RULE `s:real^N->bool = (s DIFF t) UNION (t INTER s)`) THEN
  MATCH_MP_TAC HAS_MEASURE_UNION_NEGLIGIBLE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_INTER]);;

let HAS_MEASURE_ALMOST = prove
 (`!s s' t m. s has_measure m /\ negligible t /\ s UNION t = s' UNION t
              ==> s' has_measure m`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `s UNION t = s' UNION t ==> s' = (s UNION t) DIFF (t DIFF s')`)) THEN
  ASM_SIMP_TAC[HAS_MEASURE_DIFF_NEGLIGIBLE; HAS_MEASURE_UNION_NEGLIGIBLE;
               NEGLIGIBLE_DIFF]);;

let HAS_MEASURE_ALMOST_EQ = prove
 (`!s s' t. negligible t /\ s UNION t = s' UNION t
            ==> (s has_measure m <=> s' has_measure m)`,
  MESON_TAC[HAS_MEASURE_ALMOST]);;

let MEASURABLE_ALMOST = prove
 (`!s s' t. measurable s /\ negligible t /\ s UNION t = s' UNION t
            ==> measurable s'`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_ALMOST]);;

let HAS_MEASURE_NEGLIGIBLE_UNION = prove
 (`!s1 s2:real^N->bool m1 m2.
        s1 has_measure m1 /\ s2 has_measure m2 /\ negligible(s1 INTER s2)
        ==> (s1 UNION s2) has_measure (m1 + m2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
   [`(s1 DIFF (s1 INTER s2)) UNION (s2 DIFF (s1 INTER s2)):real^N->bool`;
    `s1 INTER s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  MATCH_MP_TAC HAS_MEASURE_DISJOINT_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HAS_MEASURE_ALMOST THEN EXISTS_TAC `s1:real^N->bool`;
    MATCH_MP_TAC HAS_MEASURE_ALMOST THEN EXISTS_TAC `s2:real^N->bool`;
    SET_TAC[]] THEN
  EXISTS_TAC `s1 INTER s2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MEASURE_NEGLIGIBLE_UNION = prove
 (`!s t. measurable s /\ measurable t /\ negligible(s INTER t)
         ==> measure(s UNION t) = measure s + measure t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNION; GSYM HAS_MEASURE_MEASURE]);;

let MEASURE_NEGLIGIBLE_UNION_EQ = prove
 (`!s t u.
        measurable s /\ measurable t /\ s UNION t = u /\ negligible(s INTER t)
        ==> measure s + measure t = measure u`,
  MESON_TAC[MEASURE_NEGLIGIBLE_UNION]);;

let HAS_MEASURE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool m.
        s has_measure m /\
        negligible((s DIFF t) UNION (t DIFF s))
        ==> t has_measure m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_ALMOST THEN
  MAP_EVERY EXISTS_TAC
   [`s:real^N->bool`; `(s DIFF t) UNION (t DIFF s):real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MEASURABLE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool.
        measurable s /\ negligible((s DIFF t) UNION (t DIFF s))
        ==> measurable t`,
  REWRITE_TAC[measurable] THEN
  MESON_TAC[HAS_MEASURE_NEGLIGIBLE_SYMDIFF]);;

let MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ = prove
 (`!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s)
        ==> (measurable s <=> measurable t)`,
  MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF; UNION_COMM]);;

let MEASURE_NEGLIGIBLE_SYMDIFF = prove
 (`!s t:real^N->bool.
        negligible(s DIFF t UNION t DIFF s) ==> measure s = measure t`,
  REPEAT STRIP_TAC THEN MAP_EVERY ASM_CASES_TAC
   [`measurable(s:real^N->bool)`; `measurable(t:real^N->bool)`]
  THENL
   [ASM_MESON_TAC[HAS_MEASURE_NEGLIGIBLE_SYMDIFF; MEASURE_UNIQUE;
                  HAS_MEASURE_MEASURE];
    ASM_MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ];
    ASM_MESON_TAC[MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ];
    REWRITE_TAC[measure] THEN AP_TERM_TAC THEN ABS_TAC THEN
    ASM_MESON_TAC[measurable]]);;

let NEGLIGIBLE_SYMDIFF_EQ = prove
 (`!s t:real^N->bool.
        negligible (s DIFF t UNION t DIFF s)
        ==> (negligible s <=> negligible t)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[IMP_IMP; GSYM NEGLIGIBLE_UNION_EQ] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  SET_TAC[]);;

let NEGLIGIBLE_DELETE = prove
 (`!a:real^N. negligible(s DELETE a) <=> negligible s`,
  GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SYMDIFF_EQ THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{a:real^N}` THEN REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> (UNIONS f) has_measure (sum f m)`,
  GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SUM_CLAUSES; UNIONS_0; UNIONS_INSERT; HAS_MEASURE_EMPTY] THEN
  REWRITE_TAC[IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  STRIP_TAC THEN STRIP_TAC THEN MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNION THEN
  REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MEASURE_NEGLIGIBLE_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> negligible(s INTER t))
        ==> measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS]);;

let HAS_MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> (UNIONS f) has_measure (sum f m)`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS = prove
 (`!m f:(real^N->bool)->bool.
        FINITE f /\
        (!s. s IN f ==> s has_measure (m s)) /\
        (!s t. s IN f /\ t IN f /\ ~(s = t) ==> DISJOINT s t)
        ==> measure(UNIONS f) = sum f m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `sum s (\x. measure(f x)) = sum (IMAGE (f:A->real^N->bool) s) measure`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[GSYM o_DEF] THEN
    MATCH_MP_TAC SUM_IMAGE_NONZERO THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:A`; `y:A`]) THEN
    ASM_SIMP_TAC[INTER_ACI; MEASURABLE_MEASURE_EQ_0];
    MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
    ASM_MESON_TAC[FINITE_IMAGE; HAS_MEASURE_MEASURE]]);;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE]);;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS_IMAGE = prove
 (`!f:A->real^N->bool s.
        FINITE s /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS_IMAGE]);;

let HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->real^N->bool`;
                 `{x | x IN s /\ ~((f:A->real^N->bool) x = {})}`]
        HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[NOT_IN_EMPTY];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
    SIMP_TAC[SUBSET; IN_ELIM_THM; TAUT `a /\ ~(a /\ b) <=> a /\ ~b`] THEN
    REWRITE_TAC[MEASURE_EMPTY]]);;

let MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> negligible((f x) INTER (f y)))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG]);;

let HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> (UNIONS (IMAGE f s)) has_measure (sum s (\x. measure(f x)))`,
  REWRITE_TAC[DISJOINT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
  ASM_SIMP_TAC[NEGLIGIBLE_EMPTY]);;

let MEASURE_DISJOINT_UNIONS_IMAGE_STRONG = prove
 (`!f:A->real^N->bool s.
        FINITE {x | x IN s /\ ~(f x = {})} /\
        (!x. x IN s ==> measurable(f x)) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (f x) (f y))
        ==> measure(UNIONS (IMAGE f s)) = sum s (\x. measure(f x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
  ASM_SIMP_TAC[HAS_MEASURE_DISJOINT_UNIONS_IMAGE_STRONG]);;

let MEASURE_UNION = prove
 (`!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) = measure(s) + measure(t) - measure(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE
   `s UNION t = (s INTER t) UNION (s DIFF t) UNION (t DIFF s)`] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `a + b - c:real = c + (a - c) + (b - c)`] THEN
  MP_TAC(ISPECL [`s DIFF t:real^N->bool`; `t DIFF s:real^N->bool`]
        MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`;
                 `(s DIFF t) UNION (t DIFF s):real^N->bool`]
                MEASURE_DISJOINT_UNION) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_INTER] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN AP_TERM_TAC THEN BINOP_TAC THEN
  REWRITE_TAC[REAL_EQ_SUB_LADD] THEN MATCH_MP_TAC EQ_TRANS THENL
   [EXISTS_TAC `measure((s DIFF t) UNION (s INTER t):real^N->bool)`;
    EXISTS_TAC `measure((t DIFF s) UNION (s INTER t):real^N->bool)`] THEN
  (CONJ_TAC THENL
    [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_DISJOINT_UNION THEN
     ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTER];
     AP_TERM_TAC] THEN
   SET_TAC[]));;

let MEASURE_UNION_LE = prove
 (`!s t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s UNION t) <= measure s + measure t`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MEASURE_UNION] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c <= a + b <=> &0 <= c`] THEN
  MATCH_MP_TAC MEASURE_POS_LE THEN ASM_SIMP_TAC[MEASURABLE_INTER]);;

let MEASURE_UNIONS_LE = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> measurable s)
        ==> measure(UNIONS f) <= sum f (\s. measure s)`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; UNIONS_INSERT; SUM_CLAUSES] THEN
  REWRITE_TAC[MEASURE_EMPTY; REAL_LE_REFL] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:(real^N->bool)->bool`] THEN
  REWRITE_TAC[IN_INSERT] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(s:real^N->bool) + measure(UNIONS f:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURE_UNION_LE; MEASURABLE_UNIONS] THEN
  REWRITE_TAC[REAL_LE_LADD] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_SIMP_TAC[]);;

let MEASURABLE_INSERT = prove
 (`!x s:real^N->bool. measurable(x INSERT s) <=> measurable s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURABLE_NEGLIGIBLE_SYMDIFF_EQ THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{x:real^N}` THEN
  REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[]);;

let MEASURE_INSERT = prove
 (`!x s:real^N->bool. measure(x INSERT s) = measure s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{x:real^N}` THEN
  REWRITE_TAC[NEGLIGIBLE_SING] THEN SET_TAC[]);;

let MEASURE_UNIONS_LE_IMAGE = prove
 (`!f:A->bool s:A->(real^N->bool).
        FINITE f /\ (!a. a IN f ==> measurable(s a))
        ==> measure(UNIONS (IMAGE s f)) <= sum f (\a. measure(s a))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum (IMAGE s (f:A->bool)) (\k:real^N->bool. measure k)` THEN
  ASM_SIMP_TAC[MEASURE_UNIONS_LE; FORALL_IN_IMAGE; FINITE_IMAGE] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM o_DEF] THEN
  REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC SUM_IMAGE_LE THEN
  ASM_SIMP_TAC[MEASURE_POS_LE]);;

let MEASURE_SUB_LE_MEASURE_DIFF = prove
 (`!s t:real^N->bool.
      measurable s /\ measurable t
      ==> measure s - measure t <= measure(s DIFF t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_LE_SUB_RADD] THEN
  TRANS_TAC REAL_LE_TRANS `measure((s DIFF t) UNION t:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURE_UNION_LE; MEASURABLE_DIFF] THEN
  MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_UNION; MEASURABLE_DIFF] THEN SET_TAC[]);;

let MEASURE_SUB_LE_MEASURE_SYMDIFF = prove
 (`!s t:real^N->bool.
      measurable s /\ measurable t
      ==> abs(measure s - measure t) <= measure((s DIFF t) UNION (t DIFF s))`,
  REWRITE_TAC[REAL_ARITH `abs(s - t) <= e <=> s - t <= e /\ t - s <= e`] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_SUB_LE_MEASURE_DIFF o
        lhand o snd) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_UNION; MEASURABLE_DIFF] THEN SET_TAC[]);;

let MEASURABLE_INNER_OUTER = prove
 (`!s:real^N->bool.
        measurable s <=>
                !e. &0 < e
                    ==> ?t u. t SUBSET s /\ s SUBSET u /\
                              measurable t /\ measurable u /\
                              abs(measure t - measure u) < e`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT(EXISTS_TAC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; REAL_SUB_REFL; REAL_ABS_NUM];
    ALL_TAC] THEN
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN MATCH_MP_TAC INTEGRABLE_STRADDLE THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `u:real^N->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(\x. if x IN t then vec 1 else vec 0):real^N->real^1`;
    `(\x. if x IN u then vec 1 else vec 0):real^N->real^1`;
    `lift(measure(t:real^N->bool))`;
    `lift(measure(u:real^N->bool))`] THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; GSYM HAS_MEASURE_MEASURE] THEN
  ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN REPEAT STRIP_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL]) THEN
  ASM SET_TAC[]);;

let HAS_MEASURE_INNER_OUTER = prove
 (`!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e < measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u < m + e)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURABLE_MEASURE] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t") (LABEL_TAC "u")) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    REMOVE_THEN "u" (MP_TAC o SPEC `e / &2`) THEN
    REMOVE_THEN "t" (MP_TAC o SPEC `e / &2`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
    REWRITE_TAC[IMP_IMP; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e /\ t <= u /\ m - e / &2 < t /\ u < m + e / &2
                          ==> abs(t - u) < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `~(&0 < x - y) /\ ~(&0 < y - x) ==> x = y`) THEN
    CONJ_TAC THEN DISCH_TAC THENL
     [REMOVE_THEN "u" (MP_TAC o SPEC `measure(s:real^N->bool) - m`) THEN
      ASM_REWRITE_TAC[REAL_SUB_ADD2; GSYM REAL_NOT_LE];
      REMOVE_THEN "t" (MP_TAC o SPEC `m - measure(s:real^N->bool)`) THEN
      ASM_REWRITE_TAC[REAL_SUB_SUB2; GSYM REAL_NOT_LE]] THEN
    ASM_MESON_TAC[MEASURE_SUBSET]]);;

let HAS_MEASURE_INNER_OUTER_LE = prove
 (`!s:real^N->bool m.
        s has_measure m <=>
                (!e. &0 < e ==> ?t. t SUBSET s /\ measurable t /\
                                    m - e <= measure t) /\
                (!e. &0 < e ==> ?u. s SUBSET u /\ measurable u /\
                                    measure u <= m + e)`,
  REWRITE_TAC[HAS_MEASURE_INNER_OUTER] THEN
  MESON_TAC[REAL_ARITH `&0 < e /\ m - e / &2 <= t ==> m - e < t`;
            REAL_ARITH `&0 < e /\ u <= m + e / &2 ==> u < m + e`;
            REAL_ARITH `&0 < e <=> &0 < e / &2`; REAL_LT_IMP_LE]);;

let NEGLIGIBLE_OUTER = prove
 (`!s:real^N->bool.
      negligible s <=>
      !e. &0 < e ==> ?t. s SUBSET t /\ measurable t /\ measure t < e`,
  GEN_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_INNER_OUTER] THEN
  REWRITE_TAC[REAL_ADD_LID] THEN MATCH_MP_TAC(TAUT `a ==> (a /\ b <=> b)`) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN EXISTS_TAC `{}:real^N->bool` THEN
  REWRITE_TAC[EMPTY_SUBSET; MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  ASM_REAL_ARITH_TAC);;

let NEGLIGIBLE_OUTER_LE = prove
 (`!s:real^N->bool.
      negligible s <=>
      !e. &0 < e ==> ?t. s SUBSET t /\ measurable t /\ measure t <= e`,
  REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
  MESON_TAC[REAL_LT_IMP_LE; REAL_ARITH
    `&0 < e ==> &0 < e / &2 /\ (x <= e / &2 ==> x < e)`]);;

let HAS_MEASURE_LIMIT = prove
 (`!s. s has_measure m <=>
        !e. &0 < e
            ==> ?B. &0 < B /\
                    !a b. ball(vec 0,B) SUBSET interval[a,b]
                          ==> ?z. (s INTER interval[a,b]) has_measure z /\
                                  abs(z - m) < e`,
  GEN_TAC THEN REWRITE_TAC[HAS_MEASURE] THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_INTEGRAL] THEN
  REWRITE_TAC[IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
    [GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  REWRITE_TAC[MESON[IN_INTER]
        `(if x IN k INTER s then a else b) =
         (if x IN s then if x IN k then a else b else b)`] THEN
  REWRITE_TAC[EXISTS_LIFT; GSYM LIFT_SUB; NORM_LIFT]);;

let MEASURE_LIMIT = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?B. &0 < B /\
                !a b. ball(vec 0,B) SUBSET interval[a,b]
                      ==> abs(measure(s INTER interval[a,b]) -
                              measure s) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MEASURE_UNIQUE]);;

let INTEGRABLE_ON_CONST = prove
 (`!c:real^N. (\x:real^M. c) integrable_on s <=> c = vec 0 \/ measurable s`,
  GEN_TAC THEN ASM_CASES_TAC `c:real^N = vec 0` THEN
  ASM_REWRITE_TAC[INTEGRABLE_0; MEASURABLE] THEN EQ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; VEC_COMPONENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o
      ISPEC `(\y. lambda i. y$k / (c:real^N)$k):real^N->real^1` o
      MATCH_MP(REWRITE_RULE[IMP_CONJ] INTEGRABLE_LINEAR)) THEN
    ASM_SIMP_TAC[vec; o_DEF; REAL_DIV_REFL] THEN DISCH_THEN MATCH_MP_TAC THEN
    SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o
      ISPEC `(\y. lambda i. (c:real^N)$i * y$i):real^1->real^N` o
      MATCH_MP(REWRITE_RULE[IMP_CONJ] INTEGRABLE_LINEAR)) THEN
    ANTS_TAC THENL
     [SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               LAMBDA_BETA] THEN REAL_ARITH_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; o_THM; LAMBDA_BETA; VEC_COMPONENT] THEN
      REWRITE_TAC[REAL_MUL_RID]]]);;

let ABSOLUTELY_INTEGRABLE_ON_CONST = prove
 (`!c. (\x. c) absolutely_integrable_on s <=> c = vec 0 \/ measurable s`,
  REWRITE_TAC[absolutely_integrable_on; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC; NORM_EQ_0]);;

let OPEN_NOT_NEGLIGIBLE = prove
 (`!s:real^N->bool. open s /\ ~(s = {}) ==> ~(negligible s)`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `a:real^N` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_CBALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN DISCH_TAC THEN
  SUBGOAL_THEN `negligible(interval[a - e / (&(dimindex(:N))) % vec 1:real^N,
                                    a + e / (&(dimindex(:N))) % vec 1])`
  MP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `cball(a:real^N,e)` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_CBALL; VECTOR_ADD_COMPONENT;
      VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID;
      REAL_ARITH `a - e <= x /\ x <= a + e <=> abs(x - a) <= e`; dist] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC SUM_BOUND_GEN THEN
    REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1; NUMSEG_EMPTY; NOT_LT] THEN
    REWRITE_TAC[IN_NUMSEG; VECTOR_SUB_COMPONENT; DIMINDEX_GE_1] THEN
    ASM_MESON_TAC[REAL_ABS_SUB];
    REWRITE_TAC[NEGLIGIBLE_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; REAL_MUL_RID;
      VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[REAL_ARITH `a - e < a + e <=> &0 < e`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1]]);;

let NOT_NEGLIGIBLE_UNIV = prove
 (`~negligible(:real^N)`,
  SIMP_TAC[OPEN_NOT_NEGLIGIBLE; OPEN_UNIV; UNIV_NOT_EMPTY]);;

let NEGLIGIBLE_EMPTY_INTERIOR = prove
 (`!s:real^N->bool. negligible s ==> interior s = {}`,
  MESON_TAC[OPEN_NOT_NEGLIGIBLE; INTERIOR_SUBSET; OPEN_INTERIOR;
            NEGLIGIBLE_SUBSET]);;

let HAS_INTEGRAL_NEGLIGIBLE_EQ_AE = prove
 (`!f:real^M->real^N s t.
        negligible t /\
        (!x i. x IN s DIFF t /\ 1 <= i /\ i <= dimindex (:N) ==> &0 <= f x$i)
        ==> ((f has_integral vec 0) s <=>
             negligible {x | x IN s /\ ~(f x = vec 0)})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN t then vec 0 else (f:real^M->real^N) x`;
    `s:real^M->bool`] HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[VEC_COMPONENT; IN_DIFF; REAL_LE_REFL]; ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THENL
   [MATCH_MP_TAC HAS_INTEGRAL_SPIKE_EQ;
    MATCH_MP_TAC NEGLIGIBLE_SYMDIFF_EQ THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET] THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Properties of measure under simple affine transformations.                *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_AFFINITY = prove
 (`!s m c y. s has_measure y
             ==> (IMAGE (\x:real^N. m % x + c) s)
                 has_measure abs(m) pow (dimindex(:N)) * y`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `m = &0` THENL
   [ASM_REWRITE_TAC[REAL_ABS_NUM; VECTOR_ADD_LID; VECTOR_MUL_LZERO] THEN
    ONCE_REWRITE_TAC[MATCH_MP (ARITH_RULE `~(x = 0) ==> x = SUC(x - 1)`)
     (SPEC_ALL DIMINDEX_NONZERO)] THEN DISCH_TAC THEN
    REWRITE_TAC[real_pow; REAL_MUL_LZERO; HAS_MEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{c:real^N}` THEN
    SIMP_TAC[NEGLIGIBLE_FINITE; FINITE_RULES] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(m) pow dimindex(:N)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_POW_LT; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `abs(m) * B + norm(c:real^N)` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < B /\ &0 <= x ==> &0 < B + x`;
               NORM_POS_LE; REAL_LT_MUL; GSYM REAL_ABS_NZ; REAL_POW_LT] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN
  ASM_SIMP_TAC[VECTOR_EQ_AFFINITY; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`if &0 <= m then inv m % u + --(inv m % c):real^N
                 else inv m % v + --(inv m % c)`;
     `if &0 <= m then inv m % v + --(inv m % c):real^N
                 else inv m % u + --(inv m % c)`]) THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPEC `m % x + c:real^N`) THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[IN_BALL; IN_INTERVAL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NORM_ARITH `dist(vec 0,x) = norm(x:real^N)`] THEN
      DISCH_TAC THEN MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) < a ==> norm(x + y) < a + norm(y)`) THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_LT_LMUL; GSYM REAL_ABS_NZ];
      ALL_TAC] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VECTOR_NEG_COMPONENT;
             COND_COMPONENT] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN MATCH_MP_TAC MONO_IMP THEN
    REWRITE_TAC[REAL_ARITH `m * u + --(m * c):real = (u - c) * m`] THEN
    SUBST1_TAC(REAL_ARITH
      `inv(m) = if &0 <= inv(m) then abs(inv m) else --(abs(inv m))`) THEN
    SIMP_TAC[REAL_LE_INV_EQ] THEN
    REWRITE_TAC[REAL_ARITH `(x - y:real) * --z = (y - x) * z`] THEN
    REWRITE_TAC[REAL_ABS_INV; GSYM real_div] THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; GSYM REAL_ABS_NZ] THEN
    ASM_REWRITE_TAC[real_abs] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
  ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN DISCH_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^1`
   (fun th -> EXISTS_TAC `(abs m pow dimindex (:N)) % z:real^1` THEN
              MP_TAC th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP(REAL_FIELD `~(x = &0) ==> ~(inv x = &0)`)) THEN
  REWRITE_TAC[TAUT `a ==> b ==> c <=> b /\ a ==> c`] THEN
  DISCH_THEN(MP_TAC o SPEC `--(inv m % c):real^N` o
    MATCH_MP HAS_INTEGRAL_AFFINITY) THEN
  ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_INV_INV] THEN
  SIMP_TAC[COND_ID] THEN COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC;
               VECTOR_MUL_LNEG; VECTOR_MUL_RNEG] THEN
  ASM_SIMP_TAC[REAL_MUL_RINV; VECTOR_MUL_LID; VECTOR_NEG_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(u + --c) + c:real^N = u`] THEN
  REWRITE_TAC[REAL_ABS_INV; REAL_INV_INV; GSYM REAL_POW_INV] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[LIFT_CMUL; GSYM VECTOR_SUB_LDISTRIB] THEN
  REWRITE_TAC[NORM_MUL; REAL_ABS_POW; REAL_ABS_ABS] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_POW_LT; GSYM REAL_ABS_NZ]);;

let STRETCH_GALOIS = prove
 (`!x:real^N y:real^N m.
        (!k. 1 <= k /\ k <= dimindex(:N) ==>  ~(m k = &0))
        ==> ((y = (lambda k. m k * x$k)) <=> (lambda k. inv(m k) * y$k) = x)`,
  REPEAT GEN_TAC THEN SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. p x ==> (q x <=> r x))
    ==> (!x. p x) ==> ((!x. q x) <=> (!x. r x))`) THEN
  GEN_TAC THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_FIELD);;

let HAS_MEASURE_STRETCH = prove
 (`!s m y. s has_measure y
           ==> (IMAGE (\x:real^N. lambda k. m k * x$k) s :real^N->bool)
               has_measure abs(product (1..dimindex(:N)) m) * y`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC
   `!k. 1 <= k /\ k <= dimindex(:N) ==> ~(m k = &0)`
  THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
    REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `product(1..dimindex (:N)) m = &0` SUBST1_TAC THENL
     [ASM_MESON_TAC[PRODUCT_EQ_0_NUMSEG]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LZERO; HAS_MEASURE_0] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | x$k = &0}` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; SUBSET; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; REAL_MUL_LZERO]] THEN
  UNDISCH_TAC `(s:real^N->bool) has_measure y` THEN
  REWRITE_TAC[HAS_MEASURE] THEN
  ONCE_REWRITE_TAC[HAS_INTEGRAL] THEN REWRITE_TAC[IN_UNIV] THEN
  DISCH_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < abs(product(1..dimindex(:N)) m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_ABS_NZ; REAL_LT_DIV; PRODUCT_EQ_0_NUMSEG];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real / abs(product(1..dimindex(:N)) m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `sup(IMAGE (\k. abs(m k) * B) (1..dimindex(:N)))` THEN
  MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; NUMSEG_EMPTY; FINITE_NUMSEG;
                 IN_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1; IMAGE_EQ_EMPTY;
                 EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[IN_NUMSEG; DIMINDEX_GE_1; LE_REFL; REAL_LT_MUL; REAL_ABS_NZ];
    DISCH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[IN_IMAGE; STRETCH_GALOIS; UNWIND_THM1] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
    [`(lambda k. min (inv(m k) * (u:real^N)$k)
                     (inv(m k) * (v:real^N)$k)):real^N`;
     `(lambda k. max (inv(m k) * (u:real^N)$k)
                 (inv(m k) * (v:real^N)$k)):real^N`]) THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> a ==> c) ==> (a ==> b) ==> c`) THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `z:real^1` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    SUBGOAL_THEN `!k. 1 <= k /\ k <= dimindex (:N) ==> ~(inv(m k) = &0)`
    MP_TAC THENL [ASM_SIMP_TAC[REAL_INV_EQ_0]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_STRETCH)] THEN
  (MP_TAC(ISPECL [`u:real^N`; `v:real^N`; `\i:num. inv(m i:real)`]
    IMAGE_STRETCH_INTERVAL) THEN
   SUBGOAL_THEN `~(interval[u:real^N,v] = {})` ASSUME_TAC THENL
    [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
      `s SUBSET t ==> ~(s = {}) ==> ~(t = {})`)) THEN
     ASM_REWRITE_TAC[BALL_EQ_EMPTY; GSYM REAL_NOT_LT];
     ALL_TAC] THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM))
  THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `b SUBSET s ==> b' SUBSET IMAGE f b ==> b' SUBSET IMAGE f s`)) THEN
    REWRITE_TAC[IN_BALL; SUBSET; NORM_ARITH `dist(vec 0:real^N,x) = norm x`;
                IN_IMAGE] THEN
    ASM_SIMP_TAC[STRETCH_GALOIS; REAL_INV_EQ_0; UNWIND_THM1; REAL_INV_INV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC
     `norm(sup(IMAGE(\k. abs(m k)) (1..dimindex(:N))) % x:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
      SIMP_TAC[LAMBDA_BETA; VECTOR_MUL_COMPONENT; REAL_ABS_MUL] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      REWRITE_TAC[REAL_ABS_POS] THEN
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
      ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[REAL_LE_REFL];
      ALL_TAC] THEN
    REWRITE_TAC[NORM_MUL] THEN MATCH_MP_TAC REAL_LTE_TRANS THEN
    EXISTS_TAC `abs(sup(IMAGE(\k. abs(m k)) (1..dimindex(:N)))) * B` THEN
    SUBGOAL_THEN `&0 < sup(IMAGE(\k. abs(m k)) (1..dimindex(:N)))`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; GSYM REAL_ABS_NZ; IN_NUMSEG] THEN
      ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL];
      ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sup(IMAGE(\k. abs(m k)) (1..dimindex(:N))) * B` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL_EQ; REAL_ARITH `&0 < x ==> abs x <= x`] THEN
    ASM_SIMP_TAC[REAL_LE_SUP_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                  NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    ASM_SIMP_TAC[EXISTS_IN_IMAGE; REAL_LE_RMUL_EQ] THEN
    ASM_SIMP_TAC[REAL_SUP_LE_FINITE; FINITE_IMAGE; IMAGE_EQ_EMPTY;
                 NUMSEG_EMPTY; FINITE_NUMSEG; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    MP_TAC(ISPEC `IMAGE (\k. abs (m k)) (1..dimindex(:N))` SUP_FINITE) THEN
    REWRITE_TAC[FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_EQ_EMPTY; NUMSEG_EMPTY;
                 GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];

    MATCH_MP_TAC(MESON[]
     `s = t /\ P z ==> (f has_integral z) s ==> Q
                       ==> ?w. (f has_integral w) t /\ P w`) THEN
    SIMP_TAC[GSYM PRODUCT_INV; FINITE_NUMSEG; GSYM REAL_ABS_INV] THEN
    REWRITE_TAC[REAL_INV_INV] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC(SET_RULE
       `(!x. f x = x) ==> IMAGE f s = s`) THEN
      SIMP_TAC[o_THM; LAMBDA_BETA; CART_EQ] THEN
      ASM_SIMP_TAC[REAL_MUL_ASSOC; REAL_MUL_RINV; REAL_MUL_LID];
      REWRITE_TAC[ABS_DROP; DROP_SUB; LIFT_DROP; DROP_CMUL] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; ETA_AX] THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_ABS] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ] THEN
      ASM_MESON_TAC[ABS_DROP; DROP_SUB; LIFT_DROP]]]);;

let HAS_MEASURE_TRANSLATION = prove
 (`!s m a. s has_measure m ==> (IMAGE (\x:real^N. a + x) s) has_measure m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `&1`; `a:real^N`; `m:real`]
                HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_MUL_LID; REAL_ABS_NUM; REAL_POW_ONE; REAL_MUL_LID] THEN
  REWRITE_TAC[VECTOR_ADD_SYM]);;

let NEGLIGIBLE_TRANSLATION = prove
 (`!s a. negligible s ==> negligible (IMAGE (\x:real^N. a + x) s)`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION]);;

let HAS_MEASURE_TRANSLATION_EQ = prove
 (`!a s m. (IMAGE (\x:real^N. a + x) s) has_measure m <=> s has_measure m`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_MEASURE_TRANSLATION] THEN
  DISCH_THEN(MP_TAC o SPEC `--a:real^N` o
    MATCH_MP HAS_MEASURE_TRANSLATION) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `--a + a + b:real^N = b`] THEN
  SET_TAC[]);;

add_translation_invariants [HAS_MEASURE_TRANSLATION_EQ];;

let MEASURE_TRANSLATION = prove
 (`!a s. measure(IMAGE (\x:real^N. a + x) s) = measure s`,
  REWRITE_TAC[measure; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [MEASURE_TRANSLATION];;

let NEGLIGIBLE_TRANSLATION_REV = prove
 (`!s a. negligible (IMAGE (\x:real^N. a + x) s) ==> negligible s`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION_EQ]);;

let NEGLIGIBLE_TRANSLATION_EQ = prove
 (`!a s. negligible (IMAGE (\x:real^N. a + x) s) <=> negligible s`,
  SIMP_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [NEGLIGIBLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION_EQ = prove
 (`!a:real^N s. measurable (IMAGE (\x. a + x) s) <=> measurable s`,
  REWRITE_TAC[measurable; HAS_MEASURE_TRANSLATION_EQ]);;

add_translation_invariants [MEASURABLE_TRANSLATION_EQ];;

let MEASURABLE_TRANSLATION = prove
 (`!s a:real^N. measurable s ==> measurable (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[MEASURABLE_TRANSLATION_EQ]);;

let HAS_MEASURE_SCALING = prove
 (`!s m c. s has_measure m
           ==> (IMAGE (\x:real^N. c % x) s) has_measure
               (abs(c) pow dimindex(:N)) * m`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c:real`; `vec 0:real^N`; `m:real`]
                HAS_MEASURE_AFFINITY) THEN
  REWRITE_TAC[VECTOR_ADD_RID]);;

let HAS_MEASURE_SCALING_EQ = prove
 (`!s m c. ~(c = &0)
           ==> (IMAGE (\x:real^N. c % x) s
                  has_measure (abs(c) pow dimindex(:N)) * m <=>
                s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[HAS_MEASURE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(c):real` o MATCH_MP HAS_MEASURE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL; VECTOR_MUL_ASSOC; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM REAL_ABS_MUL; REAL_MUL_LINV] THEN
  REWRITE_TAC[REAL_POW_ONE; REAL_ABS_NUM; REAL_MUL_LID; VECTOR_MUL_LID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let MEASURABLE_SCALING = prove
 (`!s c. measurable s ==> measurable (IMAGE (\x:real^N. c % x) s)`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_SCALING]);;

let MEASURABLE_SCALING_EQ = prove
 (`!s c. ~(c = &0)
         ==> (measurable (IMAGE (\x:real^N. c % x) s) <=> measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REWRITE_TAC[MEASURABLE_SCALING] THEN
  DISCH_THEN(MP_TAC o SPEC `inv c:real` o MATCH_MP MEASURABLE_SCALING) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; GSYM REAL_ABS_MUL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  SET_TAC[]);;

let MEASURE_SCALING = prove
 (`!s c. measurable s
         ==> measure(IMAGE (\x:real^N. c % x) s) =
             (abs(c) pow dimindex(:N)) * measure s`,
  REWRITE_TAC[HAS_MEASURE_MEASURE] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_UNIQUE THEN ASM_SIMP_TAC[HAS_MEASURE_SCALING]);;

let NOT_MEASURABLE_UNIV = prove
 (`~measurable(:real^N)`,
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `&2` o MATCH_MP MEASURE_SCALING) THEN
  MATCH_MP_TAC(REAL_RING
   `a = b /\ ~(b = &0) /\ ~(c = &1) ==> a = c * b ==> F`) THEN
  REWRITE_TAC[REAL_POW_EQ_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ASM_SIMP_TAC[MEASURABLE_MEASURE_EQ_0; NOT_NEGLIGIBLE_UNIV] THEN
  SIMP_TAC[DIMINDEX_GE_1; LE_1] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
  X_GEN_TAC `x:real^N` THEN EXISTS_TAC `inv(&2) % x:real^N` THEN
  REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of countable unions and intersections of various kinds.     *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_NESTED_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n)))
                  --> lift(measure(UNIONS { s(n) | n IN (:num) })))
            sequentially`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b /\ (b ==> c))`] THEN
  SIMP_TAC[MEASURE_INTEGRAL_UNIV; LIFT_DROP] THEN
  REWRITE_TAC[MEASURABLE_INTEGRABLE] THEN
  STRIP_TAC THEN MATCH_MP_TAC(TAUT `b /\ c ==> b /\ (b ==> c)`) THEN
  MATCH_MP_TAC MONOTONE_CONVERGENCE_INCREASING THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    REWRITE_TAC[DROP_VEC; REAL_POS; REAL_LE_REFL] THEN ASM SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o PART_MATCH (rand o rand)
                  TRANSITIVE_STEPWISE_LE_EQ o concl) THEN
      ASM_REWRITE_TAC[SUBSET_TRANS; SUBSET_REFL] THEN ASM SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN REWRITE_TAC[EXISTS_IN_IMAGE] THEN
      SIMP_TAC[NOT_EXISTS_THM; IN_UNIV; LIM_CONST]];
     RULE_ASSUM_TAC(REWRITE_RULE[GSYM MEASURABLE_INTEGRABLE]) THEN
     ASM_SIMP_TAC[INTEGRAL_MEASURE_UNIV] THEN
     REWRITE_TAC[bounded; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
     EXISTS_TAC `B:real` THEN REWRITE_TAC[IN_UNIV; NORM_LIFT] THEN
     REWRITE_TAC[real_abs] THEN ASM_MESON_TAC[MEASURE_POS_LE]]);;

let MEASURABLE_NESTED_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(s n) <= B) /\
        (!n. s(n) SUBSET s(SUC n))
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_NESTED_UNIONS) THEN
  SIMP_TAC[]);;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS (IMAGE s (0..n)):real^N->bool`; `B:real`]
               HAS_MEASURE_NESTED_UNIONS) THEN
  REWRITE_TAC[sums; FROM_0; INTER_UNIV] THEN
  SUBGOAL_THEN
   `!n. (UNIONS (IMAGE s (0..n)):real^N->bool) has_measure
        (sum(0..n) (\k. measure(s k)))`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    ASSUME_TAC(GEN `n:num` (MATCH_MP MEASURE_UNIQUE (SPEC `n:num` th)))) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
    GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[LIFT_SUM; FINITE_NUMSEG; o_DEF] THEN
  SUBGOAL_THEN
   `UNIONS {UNIONS (IMAGE s (0..n)) | n IN (:num)}:real^N->bool =
    UNIONS (IMAGE s (:num))`
   (fun th -> REWRITE_TAC[th] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
              REWRITE_TAC[]) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_IN_UNIONS; IN_UNIV] THEN
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
  REWRITE_TAC[IN_NUMSEG; LE_0] THEN MESON_TAC[LE_REFL]);;

let NEGLIGIBLE_COUNTABLE_UNIONS_GEN = prove
 (`!f. COUNTABLE f /\ (!s:real^N->bool. s IN f ==> negligible s)
       ==> negligible(UNIONS f)`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; NEGLIGIBLE_EMPTY] THEN
  MP_TAC(ISPEC `f:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN ASM_REWRITE_TAC[]);;

let HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        (!m n. ~(m = n) ==> negligible(s m INTER s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) }) /\
            ((\n. lift(measure(s n))) sums
             lift(measure(UNIONS { s(n) | n IN (:num) }))) (from 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  MATCH_MP_TAC HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS THEN
  EXISTS_TAC `measure(interval[a:real^N,b])` THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (s:num->real^N->bool) (0..n)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_SIMP_TAC[FINITE_NUMSEG];
    MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE];
      ASM SET_TAC[]]]);;

let MEASURABLE_COUNTABLE_UNIONS_BOUNDED = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        bounded(UNIONS { s(n) | n IN (:num) })
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS { s(n):real^N->bool | n IN (:num) } =
    UNIONS { UNIONS {s(m) | m IN 0..n} | n IN (:num)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_NUMSEG; IN_UNIV; LE_0] THEN MESON_TAC[LE_REFL];
    MATCH_MP_TAC MEASURABLE_NESTED_UNIONS THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    EXISTS_TAC `measure(interval[a:real^N,b])` THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FORALL_IN_GSPEC] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG];
      DISCH_TAC] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_INTERVAL] THEN ASM SET_TAC[];
      GEN_TAC THEN REWRITE_TAC[NUMSEG_CLAUSES; LE_0] THEN SET_TAC[]]]);;

let MEASURE_COUNTABLE_UNIONS_LE_STRONG = prove
 (`!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. measure(UNIONS {d k | k <= n}) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\n. UNIONS {(d:num->(real^N->bool)) k | k IN (0..n)}`;
                 `B:real`]
         HAS_MEASURE_NESTED_UNIONS) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS {UNIONS {d k | k IN (0..n)} | n IN (:num)} =
                UNIONS {d n:real^N->bool | n IN (:num)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_NUMSEG; LE_0] THEN
    MESON_TAC[LE_REFL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_REWRITE_TAC[FORALL_IN_IMAGE];
      ASM_REWRITE_TAC[IN_NUMSEG; LE_0];
      GEN_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET_NUMSEG] THEN ARITH_TAC];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_DROP_UBOUND) THEN
    EXISTS_TAC `\n. lift(measure(UNIONS {d k | k IN 0..n} :real^N->bool))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `0` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[LIFT_DROP; IN_NUMSEG; LE_0]]);;

let MEASURE_COUNTABLE_UNIONS_LE = prove
 (`!d:num->(real^N->bool) B.
        (!n. measurable(d n)) /\
        (!n. sum(0..n) (\k. measure(d k)) <= B)
        ==> measurable(UNIONS {d n | n IN (:num)}) /\
            measure(UNIONS {d n | n IN (:num)}) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
  MP_TAC(ISPECL [`0..n`;`d:num->real^N->bool`] MEASURE_UNIONS_LE_IMAGE) THEN
  ASM_REWRITE_TAC[FINITE_NUMSEG] THEN
  REPEAT(FIRST_X_ASSUM (MP_TAC o SPEC `n:num`)) THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; numseg; LE_0; IN_ELIM_THM] THEN
  MESON_TAC[REAL_LE_TRANS]);;

let MEASURABLE_COUNTABLE_UNIONS_STRONG = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. measure(UNIONS {s k | k <= n}) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  MESON_TAC[MEASURE_COUNTABLE_UNIONS_LE_STRONG; REAL_LE_REFL]);;

let MEASURABLE_COUNTABLE_UNIONS = prove
 (`!s:num->real^N->bool B.
        (!n. measurable(s n)) /\
        (!n. sum (0..n) (\k. measure(s k)) <= B)
        ==> measurable(UNIONS { s(n) | n IN (:num) })`,
  MESON_TAC[MEASURE_COUNTABLE_UNIONS_LE; REAL_LE_REFL]);;

let MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN = prove
 (`!D B. COUNTABLE D /\
         (!d:real^N->bool. d IN D ==> measurable d) /\
         (!D'. D' SUBSET D /\ FINITE D' ==> measure(UNIONS D') <= B)
         ==> measurable(UNIONS D) /\ measure(UNIONS D) <= B`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `D:(real^N->bool)->bool = {}` THENL
   [ASM_SIMP_TAC[UNIONS_0; MEASURABLE_EMPTY; SUBSET_EMPTY] THEN
    MESON_TAC[FINITE_EMPTY];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPEC `D:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num->real^N->bool` SUBST1_TAC) THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; FORALL_SUBSET_IMAGE] THEN
    REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN REPEAT DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{k:num | k <= n}`) THEN
    SIMP_TAC[FINITE_NUMSEG_LE; FINITE_IMAGE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN
    REPLICATE_TAC 3 AP_TERM_TAC THEN SET_TAC[]]);;

let MEASURE_COUNTABLE_UNIONS_LE_GEN = prove
 (`!D B. COUNTABLE D /\
         (!d:real^N->bool. d IN D ==> measurable d) /\
         (!D'. D' SUBSET D /\ FINITE D' ==> sum D' (\d. measure d) <= B)
         ==> measurable(UNIONS D) /\ measure(UNIONS D) <= B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `D':(real^N->bool)->bool` THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `D':(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
  MATCH_MP_TAC MEASURE_UNIONS_LE THEN ASM SET_TAC[]);;

let MEASURABLE_COUNTABLE_INTERS = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n))
        ==> measurable(INTERS { s(n) | n IN (:num) })`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `INTERS { s(n):real^N->bool | n IN (:num) } =
                s 0 DIFF (UNIONS {s 0 DIFF s n | n IN (:num)})`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_INTERS; IN_DIFF; IN_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_COUNTABLE_UNIONS_STRONG THEN
  EXISTS_TAC `measure(s 0:real^N->bool)` THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; LE_0] THEN
  GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[IN_DIFF]] THEN
  ONCE_REWRITE_TAC[GSYM IN_NUMSEG_0] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               MEASURABLE_DIFF; MEASURABLE_UNIONS]);;

let MEASURABLE_COUNTABLE_INTERS_GEN = prove
 (`!D. COUNTABLE D /\ ~(D = {}) /\
       (!d:real^N->bool. d IN D ==> measurable d)
       ==> measurable(INTERS D)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `D:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
  GEN_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  MATCH_MP_TAC MEASURABLE_COUNTABLE_INTERS THEN ASM SET_TAC[]);;

let MEASURE_COUNTABLE_UNIONS_APPROACHABLE = prove
 (`!D B e.
        COUNTABLE D /\
        (!d. d IN D ==> measurable d) /\
        (!D'. D' SUBSET D /\ FINITE D' ==> measure(UNIONS D') <= B) /\
        &0 < e
        ==> ?D'. D' SUBSET D /\ FINITE D' /\
                 measure(UNIONS D) - e < measure(UNIONS D':real^N->bool)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `D:(real^N->bool)->bool = {}` THENL
   [DISCH_TAC THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[EMPTY_SUBSET; FINITE_EMPTY; UNIONS_0; MEASURE_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MP_TAC(ISPEC `D:(real^N->bool)->bool` COUNTABLE_AS_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num->real^N->bool` SUBST1_TAC) THEN
    REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; EXISTS_SUBSET_IMAGE;
                FORALL_SUBSET_IMAGE] THEN
    REWRITE_TAC[IN_UNIV; SUBSET_UNIV] THEN REPEAT DISCH_TAC THEN
    MP_TAC(ISPECL
     [`\n. UNIONS(IMAGE (d:num->real^N->bool) {k | k <= n})`;
                   `B:real`] HAS_MEASURE_NESTED_UNIONS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FINITE_IMAGE;
                   FINITE_NUMSEG_LE; IN_ELIM_THM] THEN
      GEN_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `UNIONS {UNIONS (IMAGE d {k | k <= n}) | n IN (:num)}:real^N->bool =
      UNIONS (IMAGE d (:num))`
    SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_IMAGE] THEN REWRITE_TAC[UNIONS_GSPEC] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM; EXTENSION] THEN
      MESON_TAC[LE_REFL];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_REAL; GSYM drop; LIFT_DROP] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN DISCH_TAC THEN
    EXISTS_TAC `{k:num | k <= n}` THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LE] THEN
    ASM_SIMP_TAC[REAL_ARITH `abs(x - u) < e /\ &0 < e ==> u - e < x`]]);;

let HAS_MEASURE_NESTED_INTERS = prove
 (`!s:num->real^N->bool.
        (!n. measurable(s n)) /\
        (!n. s(SUC n) SUBSET s(n))
        ==> measurable(INTERS {s n | n IN (:num)}) /\
            ((\n. lift(measure (s n))) -->
                  lift(measure (INTERS {s n | n IN (:num)}))) sequentially`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\n. (s:num->real^N->bool) 0 DIFF s n`; `measure(s 0:real^N->bool)`]
        HAS_MEASURE_NESTED_UNIONS) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_DIFF; SUBSET_DIFF] THEN SET_TAC[];
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `n:num`)) THEN SET_TAC[]];
    SUBGOAL_THEN
     `UNIONS {s 0 DIFF s n | n IN (:num)} =
      s 0 DIFF INTERS {s n :real^N->bool | n IN (:num)}`
     (fun th -> REWRITE_TAC[th])
    THENL [REWRITE_TAC[DIFF_INTERS] THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN
       `measurable(s 0 DIFF (s 0 DIFF INTERS {s n | n IN (:num)})
                   :real^N->bool)`
      MP_TAC THENL [ASM_SIMP_TAC[MEASURABLE_DIFF]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
       `t SUBSET s ==> s DIFF (s DIFF t) = t`) THEN
      REWRITE_TAC[SUBSET; INTERS_GSPEC; IN_ELIM_THM] THEN SET_TAC[];

      MP_TAC(ISPECL [`sequentially`; `lift(measure(s 0:real^N->bool))`]
        LIM_CONST) THEN REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
      REWRITE_TAC[GSYM LIFT_SUB] THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN BINOP_TAC THEN REWRITE_TAC[LIFT_EQ; FUN_EQ_THM] THEN
      REPEAT GEN_TAC THEN
      REWRITE_TAC[REAL_ARITH `s - m:real = n <=> m = s - n`] THEN
      MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_COUNTABLE_INTERS] THENL
       [ALL_TAC; SET_TAC[]] THEN
      MP_TAC(ISPEC `\m n:num. (s n :real^N->bool) SUBSET (s m)`
          TRANSITIVE_STEPWISE_LE) THEN
      ASM_REWRITE_TAC[] THEN
      ANTS_TAC THENL [SET_TAC[]; MESON_TAC[LE_0]]]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of compact and bounded open sets.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_COMPACT = prove
 (`!s:real^N->bool. compact s ==> measurable s`,
  let lemma = prove
   (`!f s:real^N->bool.
          (!n. FINITE(f n)) /\
          (!n. s SUBSET UNIONS(f n)) /\
          (!x. ~(x IN s) ==> ?n. ~(x IN UNIONS(f n))) /\
          (!n a. a IN f(SUC n) ==> ?b. b IN f(n) /\ a SUBSET b) /\
          (!n a. a IN f(n) ==> measurable a)
          ==> measurable s`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!n. UNIONS(f(SUC n):(real^N->bool)->bool) SUBSET UNIONS(f n)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s = INTERS { UNIONS(f n) | n IN (:num) }:real^N->bool`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      REWRITE_TAC[SUBSET; IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM SET_TAC[];
      MATCH_MP_TAC MEASURABLE_COUNTABLE_INTERS THEN
      ASM_REWRITE_TAC[] THEN GEN_TAC THEN
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[]]) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  EXISTS_TAC
   `\n. { k | ?u:real^N. (!i. 1 <= i /\ i <= dimindex(:N)
                              ==> integer(u$i)) /\
                  k = { x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> u$i / &2 pow n <= x$i /\
                                           x$i < (u$i + &1) / &2 pow n } /\
                  ~(s INTER k = {})}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    SUBGOAL_THEN
     `?N. !x:real^N i. x IN s /\ 1 <= i /\ i <= dimindex(:N)
                       ==> abs(x$i * &2 pow n) < &N`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `B:real` THEN STRIP_TAC THEN
      MP_TAC(SPEC `B * &2 pow n` (MATCH_MP REAL_ARCH REAL_LT_01)) THEN
      MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MUL_RID] THEN
      X_GEN_TAC `N:num` THEN
      REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_POW; REAL_ABS_NUM] THEN
      SIMP_TAC[GSYM REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LET_TRANS];
      ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `IMAGE (\u. {x | !i. 1 <= i /\ i <= dimindex(:N)
                          ==> (u:real^N)$i <= (x:real^N)$i * &2 pow n /\
                              x$i * &2 pow n < u$i + &1})
            {u | !i. 1 <= i /\ i <= dimindex(:N) ==> integer (u$i) /\
                                                     abs(u$i) <= &N}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_CART THEN
      REWRITE_TAC[GSYM REAL_BOUNDS_LE; FINITE_INTSEG];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `l:real^N->bool` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N` THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_SIMP_TAC[] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_REVERSE_INTEGERS THEN
      ASM_SIMP_TAC[INTEGER_CLOSED] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` MP_TAC) THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `k:num`)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `k:num`]) THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    X_GEN_TAC `n:num` THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    EXISTS_TAC `(lambda i. floor(&2 pow n * (x:real^N)$i)):real^N` THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN SIMP_TAC[LAMBDA_BETA; FLOOR] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_MUL_SYM; FLOOR];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_CLOSED) THEN
    REWRITE_TAC[closed; open_def] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPECL [`inv(&2)`; `e / &(dimindex(:N))`] REAL_ARCH_POW_INV) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_RDIV_EQ; REAL_OF_NUM_LT;
                 DIMINDEX_GE_1; ARITH_RULE `0 < x <=> 1 <= x`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
    X_GEN_TAC `u:real^N` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `d < e ==> x <= d ==> x < e`)) THEN
    REWRITE_TAC[dist] THEN
    W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
    MATCH_MP_TAC(REAL_ARITH `a <= b ==> x <= a ==> x <= b`) THEN
    GEN_REWRITE_TAC (funpow 3 RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC SUM_BOUND THEN
    SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; VECTOR_SUB_COMPONENT] THEN
    X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `k:num`)) THEN
    ASM_REWRITE_TAC[real_div; REAL_ADD_RDISTRIB] THEN
    REWRITE_TAC[REAL_MUL_LID; GSYM REAL_POW_INV] THEN REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[TAUT `(a /\ b /\ c) /\ d <=> b /\ a /\ c /\ d`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN
    EXISTS_TAC `(lambda i. floor((u:real^N)$i / &2)):real^N` THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA; FLOOR] THEN
    MATCH_MP_TAC(SET_RULE `~(s INTER a = {}) /\ a SUBSET b
                           ==> ~(s INTER b = {}) /\ a SUBSET b`) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN REWRITE_TAC[SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[real_pow; real_div; REAL_INV_MUL; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[GSYM real_div] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
    MP_TAC(SPEC `(u:real^N)$k / &2` FLOOR) THEN
    REWRITE_TAC[REAL_ARITH `u / &2 < floor(u / &2) + &1 <=>
                            u < &2 * floor(u / &2) + &2`] THEN
    ASM_SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED; FLOOR_FRAC] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `a:real^N->bool`; `u:real^N`] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1 o CONJUNCT2) THEN
    ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
    GEN_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `interval(inv(&2 pow n) % u:real^N,
                         inv(&2 pow n) % (u + vec 1))` THEN
    EXISTS_TAC `interval[inv(&2 pow n) % u:real^N,
                         inv(&2 pow n) % (u + vec 1)]` THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURE_INTERVAL] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; IN_ELIM_THM] THEN
    CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT;
                 VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MEASURABLE_OPEN = prove
 (`!s:real^N->bool. bounded s /\ open s ==> measurable s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `s SUBSET t ==> s = t DIFF (t DIFF s)`)) THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN
  REWRITE_TAC[MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC MEASURABLE_COMPACT THEN
  SIMP_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_DIFF; BOUNDED_INTERVAL] THEN
  MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[CLOSED_INTERVAL]);;

let MEASURE_OPEN_POS_LT = prove
 (`!s. open s /\ bounded s /\ ~(s = {}) ==> &0 < measure s`,
  MESON_TAC[OPEN_NOT_NEGLIGIBLE; MEASURABLE_MEASURE_POS_LT; MEASURABLE_OPEN]);;

let MEASURABLE_CLOSURE = prove
 (`!s. bounded s ==> measurable(closure s)`,
  SIMP_TAC[MEASURABLE_COMPACT; COMPACT_EQ_BOUNDED_CLOSED; CLOSED_CLOSURE;
           BOUNDED_CLOSURE]);;

let MEASURABLE_INTERIOR = prove
 (`!s. bounded s ==> measurable(interior s)`,
  SIMP_TAC[MEASURABLE_OPEN; OPEN_INTERIOR; BOUNDED_INTERIOR]);;

let MEASURABLE_FRONTIER = prove
 (`!s:real^N->bool. bounded s ==> measurable(frontier s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC MEASURABLE_DIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; MEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);;

let MEASURE_FRONTIER = prove
 (`!s:real^N->bool.
        bounded s
        ==> measure(frontier s) = measure(closure s) - measure(interior s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier] THEN
  MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE; MEASURABLE_INTERIOR] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET]);;

let MEASURE_CLOSURE = prove
 (`!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(closure s) = measure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  ASM_SIMP_TAC[MEASURABLE_CLOSURE] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

let MEASURE_INTERIOR = prove
 (`!s:real^N->bool.
        bounded s /\ negligible(frontier s)
        ==> measure(interior s) = measure s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
  ASM_SIMP_TAC[MEASURABLE_INTERIOR] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    NEGLIGIBLE_SUBSET)) THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `s:real^N->bool` CLOSURE_SUBSET) THEN
  REWRITE_TAC[frontier] THEN SET_TAC[]);;

let MEASURABLE_JORDAN = prove
 (`!s:real^N->bool. bounded s /\ negligible(frontier s) ==> measurable s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
  GEN_TAC THEN DISCH_TAC THEN
  EXISTS_TAC `interior(s):real^N->bool` THEN
  EXISTS_TAC `closure(s):real^N->bool` THEN
  ASM_SIMP_TAC[MEASURABLE_INTERIOR; MEASURABLE_CLOSURE] THEN
  REWRITE_TAC[INTERIOR_SUBSET; CLOSURE_SUBSET] THEN
  ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
  ASM_SIMP_TAC[GSYM MEASURE_FRONTIER; REAL_ABS_NUM; MEASURE_EQ_0]);;

let HAS_MEASURE_ELEMENTARY = prove
 (`!d s. d division_of s ==> s has_measure (sum d content)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[has_measure] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
  ASM_SIMP_TAC[LIFT_SUM] THEN
  MATCH_MP_TAC HAS_INTEGRAL_COMBINE_DIVISION THEN
  ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[GSYM has_measure] THEN
  ASM_MESON_TAC[HAS_MEASURE_INTERVAL; division_of]);;

let MEASURABLE_ELEMENTARY = prove
 (`!d s. d division_of s ==> measurable s`,
  REWRITE_TAC[measurable] THEN MESON_TAC[HAS_MEASURE_ELEMENTARY]);;

let MEASURE_ELEMENTARY = prove
 (`!d s. d division_of s ==> measure s = sum d content`,
  MESON_TAC[HAS_MEASURE_ELEMENTARY; MEASURE_UNIQUE]);;

let MEASURABLE_INTER_INTERVAL = prove
 (`!s a b:real^N. measurable s ==> measurable (s INTER interval[a,b])`,
  SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL]);;

let MEASURABLE_INSIDE = prove
 (`!s:real^N->bool. compact s ==> measurable(inside s)`,
  SIMP_TAC[MEASURABLE_OPEN; BOUNDED_INSIDE; COMPACT_IMP_CLOSED;
           OPEN_INSIDE; COMPACT_IMP_BOUNDED]);;

(* ------------------------------------------------------------------------- *)
(* We can split off part of a measurable set of chosen size.                 *)
(* ------------------------------------------------------------------------- *)

let PART_MEASURES = prove
 (`!s:real^N->bool m.
        measurable s /\ &0 <= m /\ m <= measure s
        ==> ?t u. DISJOINT t u /\ t UNION u = s /\
                  measurable t /\ measure t = m /\
                  measurable u /\ measure u = measure s - m`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURE_POS_LE) THEN
  ASM_CASES_TAC `measure(s:real^N->bool) = m` THENL
   [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `{}:real^N->bool`] THEN
    ASM_REWRITE_TAC[UNION_EMPTY; DISJOINT_EMPTY; MEASURE_EMPTY] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[MEASURABLE_EMPTY] THEN
    REWRITE_TAC[REAL_SUB_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) - m`]
        MEASURE_LIMIT) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`\x. lift(measure(s INTER
           interval[--(lambda i. drop x):real^N,(lambda i. drop x)]))`;
    `vec 0:real^1`; `lift B`; `m:real`; `1`]
        IVT_INCREASING_COMPONENT_ON_1) THEN
  ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; DIMINDEX_1; LE_REFL; DROP_VEC] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ANTS_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC; GSYM EXISTS_DROP] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` MP_TAC) THEN
    ABBREV_TAC `c:real^N = lambda i. b` THEN STRIP_TAC THEN
    EXISTS_TAC `s INTER interval[--c:real^N,c]` THEN
    EXISTS_TAC `s DIFF interval[--c:real^N,c]` THEN
    REPLICATE_TAC 2
     (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
      CONJ_TAC THENL [SET_TAC[]; DISCH_TAC]) THEN
    MP_TAC(ISPECL
     [`s INTER interval[--c:real^N,c]`; `s DIFF interval[--c:real^N,c]`]
     MEASURE_DISJOINT_UNION) THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
    REAL_ARITH_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[INTERVAL_SING; GSYM vec; VECTOR_NEG_0] THEN
    TRANS_TAC REAL_LE_TRANS `measure {vec 0:real^N}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_SING; MEASURE_SING] THEN
      REWRITE_TAC[INTER_SUBSET];
      REWRITE_TAC[MEASURE_SING] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(REAL_ARITH
     `abs(measure (s INTER i) - measure s) < measure s - m
      ==> m <= measure(s INTER i:real^N->bool)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    SIMP_TAC[SUBSET; IN_BALL_0; IN_INTERVAL; LAMBDA_BETA; VECTOR_NEG_COMPONENT;
             GSYM REAL_ABS_BOUNDS] THEN
    MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_LT_IMP_LE]] THEN
  MATCH_MP_TAC(INST_TYPE [`:N`,`:P`] CONTINUOUS_ON_COMPARISON) THEN
  EXISTS_TAC
   `\x. lift(measure(interval[--(lambda i. drop x):real^N,
                              (lambda i. drop x)]))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MEASURE_INTERVAL; continuous_on] THEN
    REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
    SIMP_TAC[LAMBDA_BETA; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SIMP_TAC[REAL_ARITH `--x <= x <=> &0 <= x`; LIFT_DROP] THEN
    SIMP_TAC[PRODUCT_CONST; CARD_NUMSEG_1; REAL_ARITH `x - --x = &2 * x`;
             FINITE_NUMSEG] THEN
    SUBGOAL_THEN
     `(\x. lift((&2 * drop x) pow (dimindex(:N)))) continuous_on (:real^1)`
    MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_POW THEN
      SIMP_TAC[LIFT_CMUL; LIFT_DROP; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID];
      REWRITE_TAC[continuous_on; IN_UNIV] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_LIFT] THEN MATCH_MP_TAC REAL_WLOG_LE THEN
    CONJ_TAC THENL [MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[LIFT_DROP; IN_INTERVAL_1; DROP_VEC; DIST_LIFT] THEN
    MAP_EVERY X_GEN_TAC [`x:real`; `y:real`] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DIFF_SUBSET o
      rand o lhand o snd) THEN
    W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DIFF_SUBSET o
      funpow 3 rand o snd) THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
    ASM_SIMP_TAC[SUBSET_INTERVAL; VECTOR_NEG_COMPONENT; LAMBDA_BETA;
      REAL_LE_NEG2; SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    ASM_SIMP_TAC[real_abs; MEASURE_POS_LE; MEASURABLE_DIFF; MEASURABLE_INTER;
                   MEASURABLE_INTERVAL] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
    SET_TAC[]]);;

let HALF_MEASURES = prove
 (`!s:real^N->bool.
        measurable s
        ==> ?t u. DISJOINT t u /\ t UNION u = s /\
                  measurable t /\ measure t = measure s / &2 /\
                  measurable u /\ measure u = measure s / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &2`]
        PART_MEASURES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURE_POS_LE) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A nice lemma for negligibility proofs.                                    *)
(* ------------------------------------------------------------------------- *)

let STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE = prove
 (`!s. measurable s /\ bounded s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(&0 < measure(s:real^N->bool))`
   (fun th -> ASM_MESON_TAC[th; MEASURABLE_MEASURE_POS_LT]) THEN
  DISCH_TAC THEN
  MP_TAC(SPEC `(vec 0:real^N) INSERT s`
      BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  ASM_SIMP_TAC[BOUNDED_INSERT; COMPACT_IMP_BOUNDED; NOT_EXISTS_THM] THEN
  X_GEN_TAC `a:real^N` THEN REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?N. EVEN N /\ &0 < &N /\
        measure(interval[--a:real^N,a])
         < (&N * measure(s:real^N->bool)) / &4 pow dimindex (:N)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC
     `measure(interval[--a:real^N,a]) * &4 pow (dimindex(:N))` o
     MATCH_MP REAL_ARCH) THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    SIMP_TAC[GSYM REAL_LT_LDIV_EQ; ASSUME `&0 < measure(s:real^N->bool)`] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `2 * (N DIV 2 + 1)` THEN REWRITE_TAC[EVEN_MULT; ARITH] THEN
    CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < a ==> a <= b ==> x < b`)) THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (IMAGE (\m. IMAGE (\x:real^N. (&m / &N) % x) s)
                                (1..N))`;
                  `interval[--a:real^N,a]`] MEASURE_SUBSET) THEN
  MP_TAC(ISPECL [`measure:(real^N->bool)->real`;
                 `IMAGE (\m. IMAGE (\x:real^N. (&m / &N) % x) s) (1..N)`]
                HAS_MEASURE_DISJOINT_UNIONS) THEN
  SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
    MATCH_MP_TAC MEASURABLE_SCALING THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
  ONCE_REWRITE_TAC[TAUT `(a /\ b) /\ ~c ==> d <=> a /\ b /\ ~d ==> c`] THEN
  SUBGOAL_THEN
   `!m n. m IN 1..N /\ n IN 1..N /\
          ~(DISJOINT (IMAGE (\x:real^N. &m / &N % x) s)
                     (IMAGE (\x. &n / &N % x) s))
          ==> m = n`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N`
     (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N`
     (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(MP_TAC o AP_TERM `(%) (&N / &m) :real^N->real^N`) THEN
    SUBGOAL_THEN `~(&N = &0) /\ ~(&m = &0)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[REAL_OF_NUM_EQ] THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG])) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(ASSUME_TAC o GEN_REWRITE_RULE (BINDER_CONV o BINDER_CONV)
     [GSYM CONTRAPOS_THM]) THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_FIELD
     `~(x = &0) /\ ~(y = &0) ==> x / y * y / x = &1`] THEN
    ASM_SIMP_TAC[REAL_FIELD
     `~(x = &0) /\ ~(y = &0) ==> x / y * z / x = z / y`] THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`&n / &m`; `y:real^N`]) THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_POS; REAL_FIELD
     `~(y = &0) ==> (x / y = &1 <=> x = y)`] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; EQ_SYM_EQ];
    ALL_TAC] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[measurable] THEN ASM_MESON_TAC[];
    REWRITE_TAC[MEASURABLE_INTERVAL];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`--a:real^N`; `a:real^N`] CONVEX_INTERVAL) THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[CONVEX_ALT] o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `x:real^N`; `&n / &N`]) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    DISCH_THEN MATCH_MP_TAC THEN SIMP_TAC[REAL_LE_DIV; REAL_POS] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_NUMSEG]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ARITH_RULE
     `1 <= n /\ n <= N ==> 0 < N /\ n <= N`)) THEN
    SIMP_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_LT; REAL_LE_LDIV_EQ] THEN
    SIMP_TAC[REAL_MUL_LID];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  ASM_SIMP_TAC[MEASURE_SCALING; REAL_NOT_LE] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `&0`) THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC
   `sum (1..N) (measure o (\m. IMAGE (\x:real^N. &m / &N % x) s))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SUM_IMAGE THEN REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[SET_RULE `DISJOINT s s <=> s = {}`; IMAGE_EQ_EMPTY] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[REAL_LT_REFL; MEASURE_EMPTY]] THEN
  FIRST_X_ASSUM(K ALL_TAC o SPEC `0`) THEN
  ASM_SIMP_TAC[o_DEF; MEASURE_SCALING; SUM_RMUL] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < a ==> a <= b ==> x < b`)) THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  ONCE_REWRITE_TAC[REAL_ARITH `(a * b) * c:real = (a * c) * b`] THEN
  ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REWRITE_TAC[GSYM SUM_RMUL] THEN
  REWRITE_TAC[GSYM REAL_POW_MUL] THEN
  REWRITE_TAC[REAL_ABS_DIV; REAL_ABS_NUM] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `M:num` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_MUL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM REAL_OF_NUM_MUL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_ARITH `&0 < &2 * x <=> &0 < x`]) THEN
  ASM_SIMP_TAC[REAL_FIELD `&0 < y ==> x / (&2 * y) * &4 = x * &2 / y`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\i. (&i * &2 / &M) pow dimindex (:N))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
    SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_LE_DIV; REAL_POS] THEN
    REWRITE_TAC[IN_NUMSEG; FINITE_NUMSEG; SUBSET] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_OF_NUM_LT]) THEN
    ARITH_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum(M..(2*M)) (\i. &2)` THEN CONJ_TAC THENL
   [REWRITE_TAC[SUM_CONST_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(2 * M + 1) - M = M + 1`] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN STRIP_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&2 pow (dimindex(:N))` THEN
  CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_POW_1] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN REWRITE_TAC[DIMINDEX_GE_1] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_POW_LE2 THEN
  REWRITE_TAC[REAL_POS; ARITH; real_div; REAL_MUL_ASSOC] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_RDIV_EQ] THEN
  REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN
  UNDISCH_TAC `M:num <= n` THEN ARITH_TAC);;

let STARLIKE_NEGLIGIBLE_LEMMA = prove
 (`!s. compact s /\
       (!c x:real^N. &0 <= c /\ x IN s /\ (c % x) IN s ==> c = &1)
       ==> negligible s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_BOUNDED_MEASURABLE THEN
  ASM_MESON_TAC[MEASURABLE_COMPACT; COMPACT_IMP_BOUNDED]);;

let STARLIKE_NEGLIGIBLE = prove
 (`!s a. closed s /\
         (!c x:real^N. &0 <= c /\ (a + x) IN s /\ (a + c % x) IN s ==> c = &1)
         ==> negligible s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_TRANSLATION_REV THEN
  EXISTS_TAC `--a:real^N` THEN ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N`; `v:real^N`] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_LEMMA THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
    ASM_SIMP_TAC[CLOSED_TRANSLATION];
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --a + y <=> y = a + x`] THEN
    REWRITE_TAC[UNWIND_THM2] THEN ASM MESON_TAC[]]);;

let STARLIKE_NEGLIGIBLE_STRONG = prove
 (`!s a. closed s /\
         (!c x:real^N. &0 <= c /\ c < &1 /\ (a + x) IN s
                       ==> ~((a + c % x) IN s))
         ==> negligible s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real`; `x:real^N`] THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `~(x < y) /\ ~(y < x) ==> x = y`) THEN
  STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv c:real`; `c % x:real^N`]) THEN
  ASM_REWRITE_TAC[REAL_LE_INV_EQ; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `&1 < c ==> ~(c = &0)`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM REAL_INV_1] THEN
  MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_LT_01]);;

(* ------------------------------------------------------------------------- *)
(* In particular.                                                            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_HYPERPLANE = prove
 (`!a b. ~(a = vec 0 /\ b = &0) ==> negligible {x:real^N | a dot x = b}`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `a:real^N = vec 0` THEN
  ASM_SIMP_TAC[DOT_LZERO; SET_RULE `{x | F} = {}`; NEGLIGIBLE_EMPTY] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE THEN
  SUBGOAL_THEN `?x:real^N. ~(a dot x = b)` MP_TAC THENL
   [MATCH_MP_TAC(MESON[] `!a:real^N. P a \/ P(--a) ==> ?x. P x`) THEN
    EXISTS_TAC `a:real^N` THEN REWRITE_TAC[DOT_RNEG] THEN
    MATCH_MP_TAC(REAL_ARITH `~(a = &0) ==> ~(a = b) \/ ~(--a = b)`) THEN
    ASM_REWRITE_TAC[DOT_EQ_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `c:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[CLOSED_HYPERPLANE; IN_ELIM_THM; DOT_RADD; DOT_RMUL] THEN
  MAP_EVERY X_GEN_TAC [`t:real`; `y:real^N`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
   `&0 <= t /\ ac + ay = b /\ ac + t * ay = b
    ==> ((ay = &0 ==> ac = b) /\ (t - &1) * ay = &0)`)) THEN
  ASM_SIMP_TAC[REAL_ENTIRE; REAL_SUB_0] THEN CONV_TAC TAUT);;

let NEGLIGIBLE_LOWDIM = prove
 (`!s:real^N->bool. dim(s) < dimindex(:N) ==> negligible s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `span(s):real^N->bool` THEN REWRITE_TAC[SPAN_INC] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = &0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);;

let NEGLIGIBLE_AFFINE_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(affine hull s)`,
  REWRITE_TAC[IMP_CONJ] THEN  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[AFFINE_HULL_EMPTY; NEGLIGIBLE_EMPTY] THEN
  SUBGOAL_THEN
   `!x s:real^N->bool n.
        ~(x IN s) /\ (x INSERT s) HAS_SIZE n /\ n <= dimindex(:N)
        ==> negligible(affine hull(x INSERT s))`
   (fun th -> MESON_TAC[th; HAS_SIZE; FINITE_INSERT]) THEN
  X_GEN_TAC `orig:real^N` THEN GEOM_ORIGIN_TAC `orig:real^N` THEN
  SIMP_TAC[AFFINE_HULL_EQ_SPAN; IN_INSERT; SPAN_INSERT_0; HULL_INC] THEN
  REWRITE_TAC[HAS_SIZE; FINITE_INSERT; IMP_CONJ] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(s:real^N->bool)` THEN
  ASM_SIMP_TAC[DIM_LE_CARD; DIM_SPAN] THEN ASM_ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_1 = prove
 (`!a:real^1. negligible (affine hull {a})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_1] THEN
  ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_2 = prove
 (`!a b:real^2. negligible (affine hull {a,b})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_2] THEN
  ARITH_TAC);;

let NEGLIGIBLE_AFFINE_HULL_3 = prove
 (`!a b c:real^3. negligible (affine hull {a,b,c})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_AFFINE_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_3] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL = prove
 (`!s:real^N->bool.
        FINITE s /\ CARD(s) <= dimindex(:N) ==> negligible(convex hull s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP NEGLIGIBLE_AFFINE_HULL) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL]);;

let NEGLIGIBLE_CONVEX_HULL_1 = prove
 (`!a:real^1. negligible (convex hull {a})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_1] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL_2 = prove
 (`!a b:real^2. negligible (convex hull {a,b})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_2] THEN
  ARITH_TAC);;

let NEGLIGIBLE_CONVEX_HULL_3 = prove
 (`!a b c:real^3. negligible (convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NEGLIGIBLE_CONVEX_HULL THEN
  SIMP_TAC[FINITE_INSERT; CARD_CLAUSES; FINITE_EMPTY; DIMINDEX_3] THEN
  ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Measurability of bounded convex sets.                                     *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_CONVEX_FRONTIER = prove
 (`!s:real^N->bool. convex s ==> negligible(frontier s)`,
  SUBGOAL_THEN
   `!s:real^N->bool. convex s /\ (vec 0) IN s ==> negligible(frontier s)`
  ASSUME_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN
    ASM_REWRITE_TAC[FRONTIER_EMPTY; NEGLIGIBLE_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (\x:real^N. --a + x) s`) THEN
    ASM_SIMP_TAC[CONVEX_TRANSLATION; IN_IMAGE] THEN
    ASM_REWRITE_TAC[UNWIND_THM2;
                    VECTOR_ARITH `vec 0:real^N = --a + x <=> x = a`] THEN
    REWRITE_TAC[FRONTIER_TRANSLATION; NEGLIGIBLE_TRANSLATION_EQ]] THEN
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:real^N->bool` DIM_SUBSET_UNIV) THEN
  REWRITE_TAC[ARITH_RULE `d:num <= e <=> d < e \/ d = e`] THEN STRIP_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `closure s:real^N->bool` THEN
    REWRITE_TAC[frontier; SUBSET_DIFF] THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN ASM_REWRITE_TAC[DIM_CLOSURE];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN interior s` CHOOSE_TAC THENL
   [X_CHOOSE_THEN `b:real^N->bool` STRIP_ASSUME_TAC
     (ISPEC `s:real^N->bool` BASIS_EXISTS) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MP_TAC(ISPEC `b:real^N->bool` INTERIOR_SIMPLEX_NONEMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[INSERT_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC STARLIKE_NEGLIGIBLE_STRONG THEN
  EXISTS_TAC `a:real^N` THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[frontier; IN_DIFF; DE_MORGAN_THM] THEN DISJ2_TAC THEN
  SIMP_TAC[VECTOR_ARITH
   `a + c % x:real^N = (a + x) - (&1 - c) % ((a + x) - a)`] THEN
  MATCH_MP_TAC IN_INTERIOR_CLOSURE_CONVEX_SHRINK THEN
  RULE_ASSUM_TAC(REWRITE_RULE[frontier; IN_DIFF]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MEASURABLE_CONVEX = prove
 (`!s:real^N->bool. convex s /\ bounded s ==> measurable s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_JORDAN THEN
  ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER]);;

let NEGLIGIBLE_CONVEX_INTERIOR = prove
 (`!s:real^N->bool. convex s ==> (negligible s <=> interior s = {})`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [MESON_TAC[OPEN_NOT_NEGLIGIBLE; INTERIOR_SUBSET; OPEN_INTERIOR;
              NEGLIGIBLE_SUBSET];
    DISCH_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `frontier s:real^N->bool` THEN
    ASM_SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER] THEN
    ASM_REWRITE_TAC[frontier; DIFF_EMPTY; CLOSURE_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* Various special cases.                                                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_SPHERE = prove
 (`!a:real^N r. negligible (sphere(a,e))`,
  REWRITE_TAC[GSYM FRONTIER_CBALL] THEN
  SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_CBALL]);;

let MEASURABLE_BALL = prove
 (`!a r. measurable(ball(a,r))`,
  SIMP_TAC[MEASURABLE_OPEN; BOUNDED_BALL; OPEN_BALL]);;

let MEASURABLE_CBALL = prove
 (`!a r. measurable(cball(a,r))`,
  SIMP_TAC[MEASURABLE_COMPACT; COMPACT_CBALL]);;

let MEASURE_BALL_POS = prove
 (`!x:real^N e. &0 < e ==> &0 < measure(ball(x,e))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_OPEN_POS_LT THEN
  REWRITE_TAC[OPEN_BALL; BOUNDED_BALL; BALL_EQ_EMPTY] THEN
  ASM_REAL_ARITH_TAC);;

let MEASURE_CBALL_POS = prove
 (`!x:real^N e. &0 < e ==> &0 < measure(cball(x,e))`,
  MESON_TAC[MEASURE_SUBSET; REAL_LTE_TRANS; MEASURABLE_BALL; MEASURABLE_CBALL;
            BALL_SUBSET_CBALL; MEASURE_BALL_POS]);;

let HAS_INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b y. (f has_integral y) (interval(a,b)) <=>
             (f has_integral y) (interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM INTERIOR_CLOSED_INTERVAL] THEN
  MATCH_MP_TAC HAS_INTEGRAL_INTERIOR THEN
  MATCH_MP_TAC NEGLIGIBLE_CONVEX_FRONTIER THEN
  REWRITE_TAC[CONVEX_INTERVAL]);;

let INTEGRABLE_ON_OPEN_INTERVAL = prove
 (`!f a b. f integrable_on interval(a,b) <=>
           f integrable_on interval[a,b]`,
  REWRITE_TAC[integrable_on; HAS_INTEGRAL_OPEN_INTERVAL]);;

let INTEGRAL_OPEN_INTERVAL = prove
 (`!f a b. integral(interval(a,b)) f = integral(interval[a,b]) f`,
  REWRITE_TAC[integral; HAS_INTEGRAL_OPEN_INTERVAL]);;

let MEASURABLE_SEGMENT = prove
 (`(!a b:real^N. measurable(segment[a,b])) /\
   (!a b:real^N. measurable(segment(a,b)))`,
  SIMP_TAC[MEASURABLE_CONVEX; CONVEX_SEGMENT; BOUNDED_SEGMENT]);;

let MEASURE_SEGMENT_1 = prove
 (`(!a b:real^1. measure(segment[a,b]) = norm(b - a)) /\
   (!a b:real^1. measure(segment(a,b)) = norm(b - a))`,
  REWRITE_TAC[SEGMENT_1] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[MEASURE_INTERVAL_1] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An existence theorem for "improper" integrals. Hake's theorem implies     *)
(* that if the integrals over subintervals have a limit then the integral    *)
(* exists. This is incomparable: we only need a priori to assume that        *)
(* the integrals are bounded, and we get absolute integrability, but we      *)
(* also need a (rather weak) bound assumption on the function.               *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_IMPROPER = prove
 (`!net:A net f:real^M->real^N a b.
     (!c d. interval[c,d] SUBSET interval(a,b)
            ==> f integrable_on interval[c,d]) /\
     bounded { integral (interval[c,d]) f |
               interval[c,d] SUBSET interval(a,b)} /\
     (!i. 1 <= i /\ i <= dimindex(:N)
          ==> ?g. g absolutely_integrable_on interval[a,b] /\
                  ((!x. x IN interval[a,b] ==> (f x)$i <= drop(g x)) \/
                   (!x. x IN interval[a,b] ==> (f x)$i >= drop(g x))))
   ==> f absolutely_integrable_on interval[a,b]`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `content(interval[a:real^M,b]) = &0` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_NULL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONTENT_LT_NZ; CONTENT_POS_LT_EQ]) THEN
  STRIP_TAC THEN
  ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[real_ge] THEN
  SUBGOAL_THEN
   `(!n. interval[a + inv(&n + &1) % (b - a),b - inv(&n + &1) % (b - a)] SUBSET
         interval(a:real^M,b)) /\
    (!n. interval[a + inv(&n + &1) % (b - a),b - inv(&n + &1) % (b - a)] SUBSET
         interval[a:real^M,b])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ t SUBSET u ==> s SUBSET t /\ s SUBSET u`) THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    REWRITE_TAC[SUBSET_INTERVAL] THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_ARITH `a < a + x <=> &0 < x`;
                 REAL_ARITH `b - x < b <=> &0 < x`; REAL_LT_MUL;
                 REAL_SUB_LT; REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!n. interval[a + inv(&n + &1) % (b - a),b - inv(&n + &1) % (b - a)] SUBSET
        interval[a + inv(&(SUC n) + &1) % (b - a):real^M,
                 b - inv(&(SUC n) + &1) % (b - a)]`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL] THEN GEN_TAC THEN DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `a + x * y <= a + w * y <=> &0 <= (w - x) * y`;
                REAL_ARITH `b - w * y <= b - x * y <=> &0 <= (w - x) * y`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_SUB_LE; REAL_LT_IMP_LE; GSYM REAL_OF_NUM_SUC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^1` STRIP_ASSUME_TAC) THENL
   [MATCH_MP_TAC
     ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_UBOUND THEN
    EXISTS_TAC `g:real^M->real^1` THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DIMINDEX_1] THEN
    ASM_REWRITE_TAC[IMP_IMP; FORALL_1; GSYM drop; LIFT_DROP] THEN
    SUBGOAL_THEN
     `(\x. lift((f:real^M->real^N) x$i)) = (\x. g x - (g x - lift(f x$i)))`
    SUBST1_TAC THENL [ABS_TAC THEN CONV_TAC VECTOR_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MP_TAC(ISPECL
     [`\n x. if x IN interval[a + inv(&n + &1) % (b - a),
                              b - inv(&n + &1) % (b - a)]
             then g x - lift((f:real^M->real^N) x $i) else vec 0`;
      `\x. g x - lift((f:real^M->real^N) x$i)`;
      `interval(a:real^M,b)`] MONOTONE_CONVERGENCE_INCREASING) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[INTEGRABLE_ON_OPEN_INTERVAL]] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRAL_RESTRICT_INTER] THEN
    ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL;
                      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
        RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
        ASM_MESON_TAC[]];
      ALL_TAC];
    MATCH_MP_TAC
     ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_COMPONENT_LBOUND THEN
    EXISTS_TAC `g:real^M->real^1` THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; DIMINDEX_1] THEN
    ASM_REWRITE_TAC[IMP_IMP; FORALL_1; GSYM drop; LIFT_DROP] THEN
    SUBGOAL_THEN
     `(\x. lift((f:real^M->real^N) x$i)) = (\x. (lift(f x$i) - g x) + g x)`
    SUBST1_TAC THENL [ABS_TAC THEN CONV_TAC VECTOR_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_ADD THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    MP_TAC(ISPECL
     [`\n x. if x IN interval[a + inv(&n + &1) % (b - a),
                              b - inv(&n + &1) % (b - a)]
             then lift((f:real^M->real^N) x $i) - g x else vec 0`;
      `\x. lift((f:real^M->real^N) x$i) - g x`;
      `interval(a:real^M,b)`] MONOTONE_CONVERGENCE_INCREASING) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ALL_TAC; SIMP_TAC[INTEGRABLE_ON_OPEN_INTERVAL]] THEN
    REWRITE_TAC[INTEGRABLE_RESTRICT_INTER; INTEGRAL_RESTRICT_INTER] THEN
    ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> s INTER t = s`] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
       [RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
        ASM_MESON_TAC[];
        ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL;
                      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]];
      ALL_TAC]] THEN
  (REPEAT CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN
     REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
     ASM_SIMP_TAC[DROP_SUB; DROP_VEC; REAL_SUB_LE; LIFT_DROP] THEN
     ASM SET_TAC[];
     X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTERVAL] THEN
     DISCH_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN MP_TAC(SPEC
      `inf({(x - a:real^M)$i / (b - a)$i | i IN 1..dimindex(:M)} UNION
           {(b - x:real^M)$i / (b - a)$i | i IN 1..dimindex(:M)})`
       REAL_ARCH_INV) THEN
     SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
              IMAGE_EQ_EMPTY; NUMSEG_EMPTY; NOT_LT; DIMINDEX_GE_1;
              FINITE_UNION; IMAGE_UNION; EMPTY_UNION] THEN
     REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_IMAGE] THEN
     SIMP_TAC[VECTOR_SUB_COMPONENT; IN_NUMSEG; EVENTUALLY_SEQUENTIALLY] THEN
     ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_RDIV_EQ; REAL_MUL_LZERO] THEN
     MATCH_MP_TAC MONO_EXISTS THEN
     X_GEN_TAC `N:num` THEN STRIP_TAC THEN
     X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [NOT_FORALL_THM]) THEN
     MATCH_MP_TAC(MESON[] `(!x. ~P x) ==> (?x. P x) ==> Q`) THEN
     X_GEN_TAC `k:num` THEN REWRITE_TAC[] THEN STRIP_TAC THEN
     REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                 VECTOR_MUL_COMPONENT; REAL_ARITH
            `a + y <= x /\ x <= b - y <=> y <= x - a /\ y <= b - x`] THEN
     ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
     CONJ_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
     EXISTS_TAC `inv(&N)` THEN
     ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_SUB_LT; REAL_LT_IMP_LE] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT; LE_1] THEN
     ASM_ARITH_TAC;
     FIRST_ASSUM(MP_TAC o MATCH_MP
       ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
     DISCH_THEN(MP_TAC o MATCH_MP BOUNDED_INTEGRALS_OVER_SUBINTERVALS) THEN
     FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
     REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC; IN_UNIV] THEN
     DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
     DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
     EXISTS_TAC `B + C:real` THEN ASM_SIMP_TAC[REAL_LT_ADD] THEN
     RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_COMPONENTWISE]) THEN
     GEN_TAC THEN W(MP_TAC o PART_MATCH (lhs o rand) INTEGRAL_SUB o
       rand o lhand o snd) THEN
     ASM_SIMP_TAC[] THEN ANTS_TAC THENL
      [ASM_MESON_TAC[INTEGRABLE_SUBINTERVAL;
                     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
       DISCH_THEN SUBST1_TAC]])
  THENL
   [MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= c /\ norm(y) <= b ==> norm(x - y) <= b + c`);
    MATCH_MP_TAC(NORM_ARITH
       `norm(x:real^N) <= c /\ norm(y) <= b ==> norm(x - y) <= c + b`)] THEN
  ASM_SIMP_TAC[] THEN IMP_REWRITE_TAC[GSYM LIFT_INTEGRAL_COMPONENT] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[GSYM INTEGRABLE_COMPONENTWISE]) THEN
  ASM_SIMP_TAC[NORM_LIFT] THEN
  W(MP_TAC o PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Crude upper bounds for measure of balls.                                  *)
(* ------------------------------------------------------------------------- *)

let MEASURE_CBALL_BOUND = prove
 (`!x:real^N d.
        &0 <= d ==> measure(cball(x,d)) <= (&2 * d) pow (dimindex(:N))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(interval[x - d % vec 1:real^N,x + d % vec 1])` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_CBALL; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL; IN_INTERVAL] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; dist] THEN
    REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x - y:real^N`; `i:num`] COMPONENT_LE_NORM) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN ASM_REAL_ARITH_TAC;
    SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_LE_MUL; REAL_POS] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `(x + a) - (x - a):real = &2 * a`] THEN
    REWRITE_TAC[PRODUCT_CONST_NUMSEG; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    REWRITE_TAC[REAL_MUL_RID; ADD_SUB; REAL_LE_REFL]]);;

let MEASURE_BALL_BOUND = prove
 (`!x:real^N d.
        &0 <= d ==> measure(ball(x,d)) <= (&2 * d) pow (dimindex(:N))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(cball(x:real^N,d))` THEN
  ASM_SIMP_TAC[MEASURE_CBALL_BOUND] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  REWRITE_TAC[BALL_SUBSET_CBALL; MEASURABLE_BALL; MEASURABLE_CBALL]);;

(* ------------------------------------------------------------------------- *)
(* Negligibility of image under non-injective linear map.                    *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LINEAR_SINGULAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ ~(!x y. f(x) = f(y) ==> x = y)
        ==> negligible(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP LINEAR_SINGULAR_IMAGE_HYPERPLANE) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `{x:real^N | a dot x = &0}` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_HYPERPLANE]);;

(* ------------------------------------------------------------------------- *)
(* Some technical lemmas used in the approximation results that follow.      *)
(* Proof of the covering lemma is an obvious multidimensional generalization *)
(* of Lemma 3, p65 of Swartz's "Introduction to Gauge Integrals".            *)
(* ------------------------------------------------------------------------- *)

let COVERING_LEMMA = prove
 (`!a b:real^N s g.
        s SUBSET interval[a,b] /\ ~(interval(a,b) = {}) /\ gauge g
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!k. k IN d ==> ?x. x IN (s INTER k) /\ k SUBSET g(x)) /\
                (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
                s SUBSET UNIONS d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                        (?c d:real^N. k = interval[c,d])) /\
        (!k1 k2. k1 IN d /\ k2 IN d
                 ==> k1 SUBSET k2 \/ k2 SUBSET k1 \/
                     interior k1 INTER interior k2 = {}) /\
        (!x. x IN s ==> ?k. k IN d /\ x IN k /\ k SUBSET g(x)) /\
        (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
        (!k. k IN d ==> FINITE {l | l IN d /\ k SUBSET l})`
  ASSUME_TAC THENL
   [EXISTS_TAC
     `IMAGE (\(n,v).
             interval[(lambda i. a$i + &(v$i) / &2 pow n *
                                       ((b:real^N)$i - (a:real^N)$i)):real^N,
                      (lambda i. a$i + (&(v$i) + &1) / &2 pow n * (b$i - a$i))])
            {n,v | n IN (:num) /\
                   v IN {v:num^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> v$i < 2 EXP n}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_IMAGE THEN
      MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[NUM_COUNTABLE; IN_UNIV] THEN
      GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
      SIMP_TAC[INTERVAL_NE_EMPTY; SUBSET_INTERVAL; LAMBDA_BETA] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT; REAL_LE_MUL_EQ;
                   REAL_LT_LADD; REAL_LT_RMUL_EQ; REAL_LE_ADDR; REAL_ARITH
                     `a + x * (b - a) <= b <=> &0 <= (&1 - x) * (b - a)`] THEN
      SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_DIV2_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `x <= x + &1 /\ x < x + &1`] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_MUL_LZERO; REAL_POS; REAL_MUL_LID] THEN
      SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_POW; REAL_OF_NUM_LE] THEN
      ASM_SIMP_TAC[ARITH_RULE `x + 1 <= y <=> x < y`; REAL_LT_IMP_LE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[IMP_CONJ] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IN_ELIM_PAIR_THM; IN_UNIV] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
      GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
      MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN
        GEN_REWRITE_TAC RAND_CONV [SWAP_FORALL_THM] THEN
        REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`v:num^N`; `w:num^N`] THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; SUBSET_INTERVAL] THEN
      SIMP_TAC[DISJOINT_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC(TAUT `p \/ q \/ r ==> (a ==> p) \/ (b ==> q) \/ r`) THEN
      ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT; LAMBDA_BETA] THEN
      REWRITE_TAC[NOT_IMP; REAL_LE_LADD] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      REWRITE_TAC[REAL_ARITH `~(x + &1 <= x)`] THEN DISJ2_TAC THEN
      MATCH_MP_TAC(MESON[]
       `(!i. ~P i ==> Q i) ==> (!i. Q i) \/ (?i. P i)`) THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
      UNDISCH_TAC `m:num <= n` THEN REWRITE_TAC[LE_EXISTS] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num` SUBST1_TAC) THEN
      ONCE_REWRITE_TAC[ADD_SYM] THEN
      REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_MUL] THEN
      REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2; REAL_LT_DIV2_EQ] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2;
                   REAL_LT_LDIV_EQ; REAL_LT_RDIV_EQ] THEN
      SIMP_TAC[REAL_LT_INTEGERS; INTEGER_CLOSED] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `?e. &0 < e /\ !y. (!i. 1 <= i /\ i <= dimindex(:N)
                                ==> abs((x:real^N)$i - (y:real^N)$i) <= e)
                           ==> y IN g(x)`
      STRIP_ASSUME_TAC THENL
       [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [gauge]) THEN
        STRIP_TAC THEN
        FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `e / &2 / &(dimindex(:N))` THEN
        ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1;
                     ARITH] THEN
        X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
        MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ x IN s ==> x IN t`) THEN
        EXISTS_TAC `ball(x:real^N,e)` THEN ASM_REWRITE_TAC[IN_BALL] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
        ASM_REWRITE_TAC[dist] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((x - y:real^N)$i))` THEN
        REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_GEN THEN
        ASM_SIMP_TAC[IN_NUMSEG; FINITE_NUMSEG; NUMSEG_EMPTY; NOT_LT;
                     DIMINDEX_GE_1; VECTOR_SUB_COMPONENT; CARD_NUMSEG_1];
        ALL_TAC] THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
      MP_TAC(SPECL [`&1 / &2`; `e / norm(b - a:real^N)`]
        REAL_ARCH_POW_INV) THEN
      SUBGOAL_THEN `&0 < norm(b - a:real^N)` ASSUME_TAC THENL
       [ASM_MESON_TAC[VECTOR_SUB_EQ; NORM_POS_LT; INTERVAL_SING]; ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_SIMP_TAC[REAL_LT_DIV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV] THEN DISCH_TAC THEN
      SIMP_TAC[IN_ELIM_THM; IN_INTERVAL; SUBSET; LAMBDA_BETA] THEN
      MATCH_MP_TAC(MESON[]
       `(!x. Q x ==> R x) /\ (?x. P x /\ Q x) ==> ?x. P x /\ Q x /\ R x`) THEN
      CONJ_TAC THENL
       [REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
        MAP_EVERY X_GEN_TAC [`w:num^N`; `y:real^N`] THEN
        REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
        DISCH_THEN(fun th -> FIRST_X_ASSUM MATCH_MP_TAC THEN MP_TAC th) THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
         `(a + n <= x /\ x <= a + m) /\
          (a + n <= y /\ y <= a + m) ==> abs(x - y) <= m - n`)) THEN
        MATCH_MP_TAC(REAL_ARITH
         `y * z <= e
          ==> a <= ((x + &1) * y) * z - ((x * y) * z) ==> a <= e`) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_SUB_LT] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
        (REAL_ARITH `n < e * x ==> &0 <= e * (inv y - x) ==> n <= e / y`)) THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        ASM_SIMP_TAC[REAL_SUB_LT] THEN
        MP_TAC(SPECL [`b - a:real^N`; `i:num`] COMPONENT_LE_NORM) THEN
        ASM_SIMP_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIV; AND_FORALL_THM] THEN
      REWRITE_TAC[TAUT `(a ==> c) /\ (a ==> b) <=> a ==> b /\ c`] THEN
      REWRITE_TAC[GSYM LAMBDA_SKOLEM] THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN interval[a,b]` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN REWRITE_TAC[IN_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN STRIP_TAC THEN
      DISJ_CASES_TAC(MATCH_MP (REAL_ARITH `x <= y ==> x = y \/ x < y`)
       (ASSUME `(x:real^N)$i <= (b:real^N)$i`))
      THENL
       [EXISTS_TAC `2 EXP n - 1` THEN
        SIMP_TAC[GSYM REAL_OF_NUM_SUB; GSYM REAL_OF_NUM_LT;
                 EXP_LT_0; LE_1; ARITH] THEN
        ASM_REWRITE_TAC[REAL_SUB_ADD; REAL_ARITH `a - &1 < a`] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&1 * (b - a) = x /\ y <= x ==> a + y <= b /\ b <= a + x`) THEN
        ASM_SIMP_TAC[REAL_EQ_MUL_RCANCEL; REAL_LT_IMP_NZ; REAL_LE_RMUL_EQ;
                     REAL_SUB_LT; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
        SIMP_TAC[GSYM REAL_OF_NUM_POW; REAL_MUL_RINV; REAL_POW_EQ_0;
                 REAL_OF_NUM_EQ; ARITH_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(SPEC `&2 pow n * ((x:real^N)$i - (a:real^N)$i) /
                              ((b:real^N)$i - (a:real^N)$i)` FLOOR_POS) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[REAL_LE_MUL; REAL_LE_MUL; REAL_POW_LE; REAL_POS;
                      REAL_SUB_LE; REAL_LT_IMP_LE; REAL_LE_DIV];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
      REWRITE_TAC[GSYM REAL_OF_NUM_LT; GSYM REAL_OF_NUM_POW] THEN
      DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[REAL_ARITH `a + b * c <= x /\ x <= a + b' * c <=>
                              b * c <= x - a /\ x - a <= b' * c`] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; GSYM REAL_LE_RDIV_EQ;
                   REAL_SUB_LT; GSYM real_div] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_RDIV_EQ; REAL_LT_POW2] THEN
      SIMP_TAC[FLOOR; REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `((x:real^N)$i - (a:real^N)$i) /
                  ((b:real^N)$i - (a:real^N)$i) *
                  &2 pow n` THEN
      REWRITE_TAC[FLOOR] THEN GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
      ASM_SIMP_TAC[REAL_LT_RMUL_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID; REAL_SUB_LT] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM] THEN
      REWRITE_TAC[EQ_INTERVAL; IN_ELIM_PAIR_THM] THEN
      REWRITE_TAC[INTERVAL_EQ_EMPTY; IN_UNIV; IN_ELIM_THM] THEN
      SIMP_TAC[TAUT `a /\ b /\ c <=> ~(a /\ b ==> ~c)`; LAMBDA_BETA] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
      ASM_SIMP_TAC[REAL_LT_LADD; REAL_LT_RMUL_EQ; REAL_SUB_LT;
                   REAL_LT_DIV2_EQ; REAL_LT_POW2;
                   REAL_ARITH `~(v + &1 < v)`] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      STRIP_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `v:num^N`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN DISCH_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `IMAGE (\(n,v).
            interval[(lambda i. a$i + &(v$i) / &2 pow n *
                                      ((b:real^N)$i - (a:real^N)$i)):real^N,
                     (lambda i. a$i + (&(v$i) + &1) / &2 pow n * (b$i - a$i))])
            {m,v | m IN 0..n /\
                   v IN {v:num^N | !i. 1 <= i /\ i <= dimindex(:N)
                                       ==> v$i < 2 EXP m}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_CART THEN REWRITE_TAC[FINITE_NUMSEG_LT];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `w:num^N`] THEN DISCH_TAC THEN
    DISCH_TAC THEN SIMP_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
    MAP_EVERY EXISTS_TAC [`m:num`; `w:num^N`] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_NUMSEG; GSYM NOT_LT; LT] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET_INTERVAL]) THEN
    SIMP_TAC[NOT_IMP; LAMBDA_BETA] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
    ASM_SIMP_TAC[REAL_LE_LADD; REAL_LE_RMUL_EQ; REAL_SUB_LT] THEN
    ASM_SIMP_TAC[REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[REAL_ARITH `x <= x + &1`] THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[LE_REFL; DIMINDEX_GE_1] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
     `w / m <= v / n /\ (v + &1) / n <= (w + &1) / m
      ==> inv n <= inv m`)) THEN
    REWRITE_TAC[REAL_NOT_LE] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
    ASM_REWRITE_TAC[REAL_LT_POW2] THEN MATCH_MP_TAC REAL_POW_MONO_LT THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(interior k = {}) /\
                        (?c d:real^N. k = interval[c,d])) /\
        (!k1 k2. k1 IN d /\ k2 IN d
                 ==> k1 SUBSET k2 \/ k2 SUBSET k1 \/
                     interior k1 INTER interior k2 = {}) /\
        (!k. k IN d ==> (?x. x IN s INTER k /\ k SUBSET g x)) /\
        (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
        (!k. k IN d ==> FINITE {l | l IN d /\ k SUBSET l}) /\
        s SUBSET UNIONS d`
  MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC
     `{k:real^N->bool | k IN d /\ ?x. x IN (s INTER k) /\ k SUBSET g x}` THEN
    ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_SUBSET THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      X_GEN_TAC `k:real^N->bool` THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{l:real^N->bool | l IN d /\ k SUBSET l}` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `{k:real^N->bool | k IN d /\ !k'. k' IN d /\ ~(k = k')
                                     ==> ~(k SUBSET k')}` THEN
  ASM_SIMP_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[FORALL_IN_UNIONS] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `x:real^N`] THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPEC `\k l:real^N->bool. k IN d /\ l IN d /\ l SUBSET k /\ ~(k = l)`
     WF_FINITE) THEN
  REWRITE_TAC[WF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN X_GEN_TAC `l:real^N->bool` THEN
    ASM_CASES_TAC `(l:real^N->bool) IN d` THEN
    ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_RULES] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:real^N->bool | m IN d /\ l SUBSET m}` THEN
    ASM_SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\l:real^N->bool. l IN d /\ x IN l`) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[]);;

let COUNTABLE_ELEMENTARY_DIVISION = prove
 (`!d. COUNTABLE d /\ (!k. k IN d ==> ?a b:real^N. k = interval[a,b])
       ==> ?d'. COUNTABLE d' /\
                (!k. k IN d' ==> ~(k = {}) /\ ?a b. k = interval[a,b]) /\
                (!k l. k IN d' /\ l IN d' /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                UNIONS d' = UNIONS d`,
  let lemma = prove
   (`!s. UNIONS(s DELETE {}) = UNIONS s`,
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_DELETE] THEN
    MESON_TAC[NOT_IN_EMPTY]) in
  REWRITE_TAC[IMP_CONJ; FORALL_COUNTABLE_AS_IMAGE] THEN
  REWRITE_TAC[UNIONS_0; EMPTY_UNIONS] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[NOT_IN_EMPTY; COUNTABLE_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`d:num->real^N->bool`; `a:num->real^N`; `b:num->real^N`] THEN
  DISCH_TAC THEN
  (CHOOSE_THEN MP_TAC o prove_recursive_functions_exist num_RECURSION)
   `x 0 = ({}:(real^N->bool)->bool) /\
    (!n. x(SUC n) = @q. (x n) SUBSET q /\
                        q division_of (d n) UNION UNIONS(x n))` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n:num. (x n) division_of UNIONS {d k:real^N->bool | k < n}`
  ASSUME_TAC THENL
   [INDUCT_TAC THEN
    ASM_REWRITE_TAC[LT; SET_RULE `UNIONS {f x |x| F} = {}`;
                    DIVISION_OF_TRIVIAL] THEN
    FIRST_ASSUM(MP_TAC o SPECL [`(a:num->real^N) n`; `(b:num->real^N) n`] o
      MATCH_MP ELEMENTARY_UNION_INTERVAL_STRONG o
      MATCH_MP DIVISION_OF_UNION_SELF) THEN
    DISCH_THEN(ASSUME_TAC o SELECT_RULE) THEN
    REWRITE_TAC[SET_RULE `{f x | x = a \/ q x} = f a INSERT {f x | q x}`] THEN
    REWRITE_TAC[UNIONS_INSERT] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o last o CONJUNCTS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m n. m <= n ==> (x:num->(real^N->bool)->bool) m SUBSET x n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    REPEAT(CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`(a:num->real^N) n`; `(b:num->real^N) n`] o
      MATCH_MP ELEMENTARY_UNION_INTERVAL_STRONG o
      MATCH_MP DIVISION_OF_UNION_SELF o SPEC `n:num`) THEN
    DISCH_THEN(ASSUME_TAC o SELECT_RULE) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS(IMAGE x (:num)) DELETE ({}:real^N->bool)` THEN
  REWRITE_TAC[COUNTABLE_DELETE; IMP_CONJ; RIGHT_FORALL_IMP_THM;
              FORALL_IN_UNIONS; FORALL_IN_IMAGE; IN_DELETE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
    GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN
    ASM_MESON_TAC[DIVISION_OF_FINITE];
    MAP_EVERY X_GEN_TAC [`n:num`; `k:real^N->bool`] THEN
    ASM_MESON_TAC[division_of];
    REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
    GEN_REWRITE_TAC BINDER_CONV [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC WLOG_LE THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
      SPEC `n:num`) THEN ASM SET_TAC[];
    REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV;
                FORALL_IN_UNIONS; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE]
    THENL
     [X_GEN_TAC `k:real^N->bool` THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
         SPEC `n:num`) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`n:num`; `y:real^N`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [division_of] o
         SPEC `SUC n`) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_MESON_TAC[ARITH_RULE `n < SUC n`]]]);;

let EXPAND_CLOSED_OPEN_INTERVAL = prove
 (`!a b:real^N e.
        &0 < e
        ==> ?c d. interval[a,b] SUBSET interval(c,d) /\
                  measure(interval(c,d)) <= measure(interval[a,b]) + e`,
  let lemma = prove
   (`!f n. (\x. lift(product(1..n) (\i. f i + drop x))) continuous at (vec 0)`,
    GEN_TAC THEN INDUCT_TAC THEN
    REWRITE_TAC[PRODUCT_CLAUSES_NUMSEG; ARITH_EQ; CONTINUOUS_CONST] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n`] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC CONTINUOUS_MUL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[o_DEF; LIFT_ADD; LIFT_DROP] THEN
    SIMP_TAC[CONTINUOUS_ADD; CONTINUOUS_AT_ID; CONTINUOUS_CONST]) in
  REPEAT GEN_TAC THEN ABBREV_TAC `m:real^N = midpoint(a,b)` THEN
  POP_ASSUM MP_TAC THEN GEOM_ORIGIN_TAC `m:real^N` THEN
  REWRITE_TAC[midpoint; VECTOR_ARITH
   `inv(&2) % (a + b):real^N = vec 0 <=> a = --b`] THEN
  REPEAT GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_TAC THEN ASM_CASES_TAC `interval[--b:real^N,b] = {}` THENL
   [MAP_EVERY EXISTS_TAC [`--b:real^N`; `b:real^N`] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_REWRITE_TAC[CONTENT_EMPTY; EMPTY_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= x <=> &0 <= x`] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`\i. &2 * (b:real^N)$i`; `dimindex(:N)`] lemma) THEN
  REWRITE_TAC[continuous_at; DIST_LIFT; FORALL_LIFT; DIST_0; DROP_VEC] THEN
  REWRITE_TAC[NORM_LIFT; LIFT_DROP; REAL_ADD_RID] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`--(b + k / &4 % vec 1:real^N)`; `b + k / &4 % vec 1:real^N`] THEN
  REWRITE_TAC[MEASURE_INTERVAL; SUBSET_INTERVAL;
              CONTENT_CLOSED_INTERVAL_CASES] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  ASM_SIMP_TAC[REAL_ARITH `--x <= x <=> &0 <= x`; REAL_LT_ADDR;
               REAL_ARITH `&0 < k / &4 <=> &0 < k`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> --(b + k) < b`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> --(b + k) < --b`;
               REAL_ARITH `&0 <= b /\ &0 < k ==> &0 <= b + k`] THEN
  REWRITE_TAC[REAL_ARITH `b - --b = &2 * b`; REAL_ADD_LDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `abs(a - b) < e ==> a <= b + e`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Outer and inner approximation of measurable set by well-behaved sets.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_OUTER_INTERVALS_BOUNDED = prove
 (`!s a b:real^N e.
        measurable s /\ s SUBSET interval[a,b] /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(k = {}) /\
                                (?c d. k = interval[c,d])) /\
                (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                         ==> interior k1 INTER interior k2 = {}) /\
                (!u v. interval[u,v] IN d
                       ==> ?n. !i. 1 <= i /\ i <= dimindex(:N)
                                   ==> v$i - u$i = (b$i - a$i) / &2 pow n) /\
                (!k. k IN d /\ ~(interval(a,b) = {}) ==> ~(interior k = {})) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`(!x y. (x,y) IN IMAGE (\z. f z,g z) s ==> P x y) <=>
     (!z. z IN s ==> P (f z) (g z))`,
  REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN MESON_TAC[]) in
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; MEASURE_EMPTY; REAL_ADD_LID;
                    SUBSET_REFL; COUNTABLE_EMPTY; MEASURABLE_EMPTY] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_CASES_TAC `interval(a:real^N,b) = {}` THEN
  ASM_REWRITE_TAC[] THENL
   [EXISTS_TAC `{interval[a:real^N,b]}` THEN
    REWRITE_TAC[UNIONS_1; COUNTABLE_SING] THEN
    ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_INSERT;
                    NOT_IN_EMPTY; SUBSET_REFL; MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_SING; EQ_INTERVAL] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC[real_pow; REAL_DIV_1];
      SUBGOAL_THEN
       `measure(interval[a:real^N,b]) = &0 /\ measure(s:real^N->bool) = &0`
       (fun th -> ASM_SIMP_TAC[th; REAL_LT_IMP_LE; REAL_ADD_LID]) THEN
      SUBGOAL_THEN
        `interval[a:real^N,b] has_measure &0 /\
         (s:real^N->bool) has_measure &0`
        (fun th -> MESON_TAC[th; MEASURE_UNIQUE]) THEN
      REWRITE_TAC[HAS_MEASURE_0] THEN
      MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
       [ASM_REWRITE_TAC[NEGLIGIBLE_INTERVAL];
        ASM_MESON_TAC[NEGLIGIBLE_SUBSET]]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable]) THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real`) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURE_UNIQUE) THEN
  SUBGOAL_THEN
   `((\x:real^N. if x IN s then vec 1 else vec 0) has_integral (lift m))
    (interval[a,b])`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE]) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] HAS_INTEGRAL_EQ) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_integral]) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`a:real^N`; `b:real^N`; `s:real^N->bool`;
                `g:real^N->real^N->bool`] COVERING_LEMMA) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `d:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INTERIOR_EMPTY]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(\x. if x IN s then vec 1 else vec 0):real^N->real^1`;
                 `a:real^N`; `b:real^N`; `g:real^N->real^N->bool`;
                 `e:real`]
                HENSTOCK_LEMMA_PART1) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "*") THEN
  SUBGOAL_THEN
   `!k l:real^N->bool. k IN d /\ l IN d /\ ~(k = l)
                       ==> negligible(k INTER l)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^N->bool`; `l:real^N->bool`]) THEN
    ASM_SIMP_TAC[] THEN
    SUBGOAL_THEN
     `?x y:real^N u v:real^N. k = interval[x,y] /\ l = interval[u,v]`
    MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL CHOOSE_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THEN
    REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN DISCH_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(interval[x:real^N,y] DIFF interval(x,y)) UNION
                (interval[u:real^N,v] DIFF interval(u,v)) UNION
                (interval (x,y) INTER interval (u,v))` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    ASM_REWRITE_TAC[UNION_EMPTY] THEN
    SIMP_TAC[NEGLIGIBLE_UNION; NEGLIGIBLE_FRONTIER_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!D. FINITE D /\ D SUBSET d
         ==> measurable(UNIONS D :real^N->bool) /\ measure(UNIONS D) <= m + e`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?t:(real^N->bool)->real^N. !k. k IN D ==> t(k) IN (s INTER k) /\
                                                k SUBSET (g(t k))`
    (CHOOSE_THEN (LABEL_TAC "+")) THENL
     [REWRITE_TAC[GSYM SKOLEM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "*" (MP_TAC o SPEC
     `IMAGE (\k. (t:(real^N->bool)->real^N) k,k) D`) THEN
    ASM_SIMP_TAC[VSUM_IMAGE; PAIR_EQ] THEN REWRITE_TAC[o_DEF] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[tagged_partial_division_of; fine] THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[lemma; RIGHT_FORALL_IMP_THM; IMP_CONJ; PAIR_EQ] THEN
      ASM_SIMP_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    USE_THEN "+" (MP_TAC o REWRITE_RULE[IN_INTER]) THEN
    SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_SIMP_TAC[VSUM_SUB] THEN
    SUBGOAL_THEN `D division_of (UNIONS D:real^N->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[division_of] THEN ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURABLE_ELEMENTARY) THEN
    SUBGOAL_THEN `vsum D (\k:real^N->bool. content k % vec 1) =
                  lift(measure(UNIONS D))`
    SUBST1_TAC THENL
     [ONCE_REWRITE_TAC[GSYM DROP_EQ] THEN
      ASM_SIMP_TAC[LIFT_DROP; DROP_VSUM; o_DEF; DROP_CMUL; DROP_VEC] THEN
      SIMP_TAC[REAL_MUL_RID; ETA_AX] THEN ASM_MESON_TAC[MEASURE_ELEMENTARY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `vsum D (\k. integral k (\x:real^N. if x IN s then vec 1 else vec 0)) =
      lift(sum D (\k. measure(k INTER s)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[LIFT_SUM; o_DEF] THEN MATCH_MP_TAC VSUM_EQ THEN
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `measurable(k:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
      ASM_SIMP_TAC[GSYM INTEGRAL_MEASURE_UNIV; MEASURABLE_INTER] THEN
      REWRITE_TAC[MESON[IN_INTER]
        `(if x IN k INTER s then a else b) =
         (if x IN k then if x IN s then a else b else b)`] THEN
      REWRITE_TAC[INTEGRAL_RESTRICT_UNIV];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= m ==> abs(x - y) <= e ==> x <= m + e`) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(UNIONS D INTER s:real^N->bool)` THEN
    CONJ_TAC THENL
     [ALL_TAC;
      EXPAND_TAC "m" THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      MATCH_MP_TAC MEASURABLE_INTER THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[INTER_UNIONS] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE_STRONG THEN
    ASM_SIMP_TAC[FINITE_RESTRICT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_INTER];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `l:real^N->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `k INTER l:real^N->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
   [ASM_MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
  ASM_REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
   (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:num->real^N->bool`; `m + e:real`]
    HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  MATCH_MP_TAC(TAUT `a /\ (a /\ b ==> c) ==> (a ==> b) ==> c`) THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                              FORALL_IN_IMAGE; IN_UNIV]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_INTERVAL; MEASURABLE_INTER];
    ASM_MESON_TAC[];
    X_GEN_TAC `n:num` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (s:num->real^N->bool) (0..n)`) THEN
    SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG; IMAGE_SUBSET; SUBSET_UNIV] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= e ==> y <= e`) THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE THEN
    ASM_MESON_TAC[FINITE_NUMSEG; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(CONJUNCT2 LIFT_DROP)] THEN
  REWRITE_TAC[drop] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_UBOUND) THEN
  EXISTS_TAC
   `\n. vsum(from 0 INTER (0..n)) (\n. lift(measure(s n:real^N->bool)))` THEN
  ASM_REWRITE_TAC[GSYM sums; TRIVIAL_LIMIT_SEQUENTIALLY] THEN
  REWRITE_TAC[DIMINDEX_1; ARITH; EVENTUALLY_SEQUENTIALLY] THEN
  SIMP_TAC[VSUM_COMPONENT; ARITH; DIMINDEX_1] THEN
  ASM_REWRITE_TAC[GSYM drop; LIFT_DROP; FROM_INTER_NUMSEG]);;

let MEASURABLE_OUTER_CLOSED_INTERVALS = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval[a,b])) /\
                (!k l. k IN d /\ l IN d /\ ~(k = l)
                       ==> interior k INTER interior l = {}) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`UNIONS (UNIONS {d n | n IN (:num)}) =
     UNIONS {UNIONS(d n) | n IN (:num)}`,
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> ?a b:real^N. k = interval[a,b]) /\
        s SUBSET UNIONS d /\
        measurable (UNIONS d) /\
        measure (UNIONS d) <= measure s + e`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_THEN `d1:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `d1:(real^N->bool)->bool` COUNTABLE_ELEMENTARY_DIVISION) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `d:(real^N->bool)->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL
   [`\n. s INTER (ball(vec 0:real^N,&n + &1) DIFF ball(vec 0,&n))`;
    `measure(s:real^N->bool)`] HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS) THEN
  ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
  SUBGOAL_THEN
   `!m n. ~(m = n)
          ==> (s INTER (ball(vec 0,&m + &1) DIFF ball(vec 0,&m))) INTER
              (s INTER (ball(vec 0,&n + &1) DIFF ball(vec 0,&n))) =
              ({}:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `m1 SUBSET n
      ==> (s INTER (m1 DIFF m)) INTER (s INTER (n1 DIFF n)) = {}`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[NEGLIGIBLE_EMPTY] THEN X_GEN_TAC `n:num` THEN
    W(MP_TAC o PART_MATCH (rand o rand)
      MEASURE_DISJOINT_UNIONS_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; DISJOINT] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    SIMP_TAC[SUBSET; FORALL_IN_UNIONS; IMP_CONJ; FORALL_IN_IMAGE;
             RIGHT_FORALL_IMP_THM; IN_INTER] THEN
    ASM_SIMP_TAC[MEASURABLE_UNIONS; FINITE_NUMSEG; FORALL_IN_IMAGE;
            FINITE_IMAGE; MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {s INTER (ball(vec 0,&n + &1) DIFF ball(vec 0,&n)) | n IN (:num)} =
    (s:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNIV; IN_INTER] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?n. (x:real^N) IN ball(vec 0,&n)` MP_TAC THENL
     [REWRITE_TAC[IN_BALL_0; REAL_ARCH_LT];
      GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN ASM_CASES_TAC `n = 0` THENL
       [ASM_REWRITE_TAC[IN_BALL_0; GSYM REAL_NOT_LE; NORM_POS_LE];
        STRIP_TAC THEN EXISTS_TAC `n - 1` THEN REWRITE_TAC[IN_DIFF] THEN
        ASM_SIMP_TAC[REAL_OF_NUM_ADD; SUB_ADD; LE_1] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]];
    ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `n:num`
   (ISPECL
     [`s INTER (ball(vec 0:real^N,&n + &1) DIFF ball(vec 0,&n))`;
      `--(vec(n + 1)):real^N`; `vec(n + 1):real^N`;
      `e / &2 / &2 pow n`]
        MEASURABLE_OUTER_INTERVALS_BOUNDED))) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_LT_POW2] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_BALL] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_INTERVAL; IN_BALL_0; IN_DIFF; REAL_NOT_LT;
      REAL_OF_NUM_ADD; VECTOR_NEG_COMPONENT; VEC_COMPONENT; REAL_BOUNDS_LE] THEN
    MESON_TAC[COMPONENT_LE_NORM; REAL_LET_TRANS; REAL_LT_IMP_LE];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM]] THEN
  X_GEN_TAC `d:num->(real^N->bool)->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS {d n | n IN (:num)} :(real^N->bool)->bool` THEN
  REWRITE_TAC[lemma] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COUNTABLE_UNIONS THEN
    ASM_REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th]) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; IN_UNIV; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_GSPEC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(0..n) (\k. measure(s INTER (ball(vec 0:real^N,&k + &1) DIFF
                                  ball(vec 0,&k))) + e / &2 / &2 pow k)` THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG] THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNIONS_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[DISJOINT; FINITE_NUMSEG; MEASURABLE_DIFF; MEASURABLE_INTER;
                 MEASURABLE_BALL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FINITE_NUMSEG;
      FINITE_IMAGE; MEASURABLE_DIFF; MEASURABLE_INTER; MEASURABLE_BALL] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [GSYM th]) THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET_UNIV];
    REWRITE_TAC[real_div; SUM_LMUL; REAL_INV_POW; SUM_GP; LT] THEN
    REWRITE_TAC[GSYM real_div] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[REAL_ARITH `e / &2 * (&1 - x) / (&1 / &2) <= e <=>
                            &0 <= e * x`] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MEASURABLE_OUTER_OPEN_INTERVALS = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?d. COUNTABLE d /\
                (!k. k IN d ==> ~(k = {}) /\ (?a b. k = interval(a,b))) /\
                s SUBSET UNIONS d /\
                measurable (UNIONS d) /\
                measure (UNIONS d) <= measure s + e`,
  let lemma = prove
   (`!s. UNIONS(s DELETE {}) = UNIONS s`,
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_DELETE] THEN
    MESON_TAC[NOT_IN_EMPTY]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`]
    MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `dset:(real^N->bool)->bool` THEN
  ASM_CASES_TAC `dset:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[UNIONS_0; SUBSET_EMPTY] THEN STRIP_TAC THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[UNIONS_0; NOT_IN_EMPTY; MEASURE_EMPTY; SUBSET_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN
   `?f. dset = IMAGE (f:num->(real^N->bool)) (:num) DELETE {} /\
        (!m n. f m = f n ==> m = n \/ f n = {})`
  MP_TAC THENL
   [ASM_CASES_TAC `FINITE(dset:(real^N->bool)->bool)` THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FINITE_HAS_SIZE]) THEN
      DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN
      ABBREV_TAC `m = CARD(dset:(real^N->bool)->bool)` THEN
      DISCH_THEN(X_CHOOSE_THEN `f:num->real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `\i. if i < m then (f:num->real^N->bool) i else {}` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_DELETE; IN_IMAGE; IN_UNIV] THEN ASM_MESON_TAC[];
      MP_TAC(ISPEC `dset:(real^N->bool)->bool`
        COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[SET_RULE `s = s DELETE a <=> ~(a IN s)`] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num->real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (is_forall o concl)) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV; FORALL_AND_THM; SKOLEM_THM;
              IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_DELETE; lemma] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
   `(!x. ~(P x) ==> ~(P x) /\ Q x) ==> (!x. P x ==> Q x) ==> !x. Q x`)) THEN
  ANTS_TAC THENL [MESON_TAC[EMPTY_AS_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:num->real^N`; `b:num->real^N`] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP; GSYM CONJ_ASSOC] THEN
  GEN_REWRITE_TAC I [IMP_CONJ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP(MESON[]
   `(!x y. ~(P x) /\ ~(P y) /\ ~(f x = f y) ==> Q x y)
    ==> (!x y. P x ==> Q x y) /\ (!x y. P y ==> Q x y)
        ==> (!x y. ~(f x = f y) ==> Q x y)`)) THEN
  SIMP_TAC[INTERIOR_EMPTY; INTER_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?d. COUNTABLE d /\
        (!k. k IN d ==> ?a b:real^N. k = interval(a,b)) /\
        s SUBSET UNIONS d /\
        measurable (UNIONS d) /\
        measure (UNIONS d) <= measure s + e`
  MP_TAC THENL
   [ALL_TAC;
    DISCH_THEN(X_CHOOSE_TAC `d:(real^N->bool)->bool`) THEN
    EXISTS_TAC `d DELETE ({}:real^N->bool)` THEN
    ASM_SIMP_TAC[lemma; COUNTABLE_DELETE; IN_DELETE]] THEN
  MP_TAC(GEN `n:num` (ISPECL [`(a:num->real^N) n`; `(b:num->real^N) n`;
    `e / &2 pow (n + 2)`] EXPAND_CLOSED_OPEN_INTERVAL)) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2; SKOLEM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  MAP_EVERY X_GEN_TAC [`A:num->real^N`; `B:num->real^N`] THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (\n. interval(A n:real^N,B n)) (:num)` THEN
  SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] SUBSET_TRANS)) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN
    ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_UNIV] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
  REWRITE_TAC[MEASURABLE_INTERVAL] THEN X_GEN_TAC `n:num` THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC
   `sum(0..n) (\i. measure(interval[a i:real^N,b i]) + e / &2 pow (i + 2))` THEN
  ASM_SIMP_TAC[SUM_LE_NUMSEG] THEN REWRITE_TAC[SUM_ADD_NUMSEG] THEN
  REWRITE_TAC[real_div; REAL_INV_MUL; SUM_LMUL; REAL_POW_ADD; SUM_RMUL] THEN
  REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  MATCH_MP_TAC(REAL_ARITH
   `s <= m + e / &2 /\ &0 <= e * x
    ==> s + e * (&1 - x) / (&1 / &2) * &1 / &4 <= m + e`) THEN
  ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_LT_IMP_LE;
               REAL_LE_DIV; REAL_POS] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
  W(MP_TAC o PART_MATCH (rhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o snd) THEN
  REWRITE_TAC[FINITE_NUMSEG; MEASURABLE_INTERVAL] THEN ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `interval[(a:num->real^N) i,b i] = interval[a j,b j]` THENL
     [UNDISCH_TAC
       `!m n. (d:num->real^N->bool) m = d n ==> m = n \/ d n = {}` THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INTER_EMPTY; NEGLIGIBLE_EMPTY];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE
       (BINDER_CONV o BINDER_CONV o RAND_CONV o LAND_CONV)
       [GSYM INTERIOR_INTER]) THEN
      DISCH_THEN(MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM HAS_MEASURE_0; HAS_MEASURE_MEASURABLE_MEASURE] THEN
      SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL] THEN
      MATCH_MP_TAC(MESON[MEASURE_EMPTY]
       `measure(interior s) = measure s
        ==> interior s = {} ==> measure s = &0`) THEN
      MATCH_MP_TAC MEASURE_INTERIOR THEN
      SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL; NEGLIGIBLE_CONVEX_FRONTIER;
               CONVEX_INTER; CONVEX_INTERVAL]];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC MEASURE_SUBSET THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_UNIONS THEN
    SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL;
             FINITE_NUMSEG];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN MESON_TAC[]]);;

let MEASURABLE_OUTER_OPEN = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. open t /\ s SUBSET t /\
                measurable t /\ measure t < measure s + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`]
    MEASURABLE_OUTER_OPEN_INTERVALS) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:(real^N->bool)->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS d :real^N->bool` THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e /\ m <= s + e / &2 ==> m < s + e`] THEN
  MATCH_MP_TAC OPEN_UNIONS THEN ASM_MESON_TAC[OPEN_INTERVAL]);;

let MEASURABLE_INNER_COMPACT = prove
 (`!s:real^N->bool e.
        measurable s /\ &0 < e
        ==> ?t. compact t /\ t SUBSET s /\
                measurable t /\ measure s < measure t + e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e ==> &0 < e / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `z:real` THEN STRIP_TAC THEN
  MP_TAC(ISPECL  [`interval[a:real^N,b] DIFF s`; `e/ &4`]
        MEASURABLE_OUTER_OPEN) THEN
  ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL;
               REAL_ARITH `&0 < e ==> &0 < e / &4`] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `interval[a:real^N,b] DIFF t` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    ASM_SIMP_TAC[CLOSED_DIFF; CLOSED_INTERVAL; BOUNDED_DIFF; BOUNDED_INTERVAL];
    ASM SET_TAC[];
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL];
    MATCH_MP_TAC(REAL_ARITH
        `&0 < e /\
         measure(s) < measure(interval[a,b] INTER s) + e / &4 /\
         measure(t) < measure(interval[a,b] DIFF s) + e / &4 /\
         measure(interval[a,b] INTER s) +
         measure(interval[a,b] DIFF s) = measure(interval[a,b]) /\
         measure(interval[a,b] INTER t) +
         measure(interval[a,b] DIFF t) = measure(interval[a,b]) /\
         measure(interval[a,b] INTER t) <= measure t
         ==> measure s < measure(interval[a,b] DIFF t) + e`) THEN
    ASM_SIMP_TAC[MEASURE_SUBSET; INTER_SUBSET; MEASURABLE_INTER;
                 MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST_ALL_TAC o SYM o MATCH_MP MEASURE_UNIQUE) THEN
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REAL_ARITH_TAC;
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_DISJOINT_UNION_EQ THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
      SET_TAC[]]]);;

let OPEN_MEASURABLE_INNER_DIVISION = prove
 (`!s:real^N->bool e.
        open s /\ measurable s /\ &0 < e
        ==> ?D. D division_of UNIONS D /\
                UNIONS D SUBSET s /\
                measure s < measure(UNIONS D) + e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e / &2`] MEASURE_LIMIT) THEN
  ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `B:real` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  ASM_REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s INTER interval(a - vec 1:real^N,b + vec 1)`
        OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL; SUBSET_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`D:(real^N->bool)->bool`; `measure(s:real^N->bool)`;
                 `e / &2`] MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
  ASM_REWRITE_TAC[REAL_HALF] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `measure(UNIONS D :real^N->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MEASURABLE_UNIONS THEN
        ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
        ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL];
        ASM_SIMP_TAC[SUBSET_UNIONS]];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL; INTER_SUBSET]];
    DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `d:(real^N->bool)->bool` ELEMENTARY_UNIONS_INTERVALS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:(real^N->bool)->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS p :real^N->bool = UNIONS d` SUBST1_TAC THENL
     [ASM_MESON_TAC[division_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS D :real^N->bool` THEN
      ASM_SIMP_TAC[SUBSET_UNIONS; INTER_SUBSET];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `ms' - e / &2 < mud ==> ms < ms' + e / &2 ==> ms < mud + e`)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `abs(sc - s) < e / &2
        ==> sc <= so /\ sc <= s ==> s < so + e / &2`)) THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_INTERVAL; INTER_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`) THEN
      REWRITE_TAC[SUBSET_INTERVAL; VECTOR_SUB_COMPONENT; VEC_COMPONENT;
                  VECTOR_ADD_COMPONENT] THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Hence for linear transformation, suffices to check compact intervals.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LINEAR_IMAGE_INTERVAL = prove
 (`!f a b. linear f ==> measurable(IMAGE f (interval[a,b]))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN
    ASM_MESON_TAC[CONVEX_INTERVAL];
    MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN
    ASM_MESON_TAC[BOUNDED_INTERVAL]]);;

let HAS_MEASURE_LINEAR_SUFFICIENT = prove
 (`!f:real^N->real^N m.
        linear f /\
        (!a b. IMAGE f (interval[a,b]) has_measure
               (m * measure(interval[a,b])))
        ==> !s. measurable s ==> (IMAGE f s) has_measure (m * measure s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `m < &0 \/ &0 <= m`) THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`vec 0:real^N`; `vec 1:real^N`]) THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_POS_LE) THEN
    MATCH_MP_TAC(TAUT `~a ==> a ==> b`) THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < --m * x ==> ~(&0 <= m * x)`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_NEG_GT0] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN MATCH_MP_TAC CONTENT_POS_LT THEN
    SIMP_TAC[VEC_COMPONENT; REAL_LT_01];
    ALL_TAC] THEN
  ASM_CASES_TAC `!x y. (f:real^N->real^N) x = f y ==> x = y` THENL
   [ALL_TAC;
    SUBGOAL_THEN `!s. negligible(IMAGE (f:real^N->real^N) s)` ASSUME_TAC THENL
     [ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `m * measure(interval[vec 0:real^N,vec 1]) = &0` MP_TAC THENL
     [MATCH_MP_TAC(ISPEC `IMAGE (f:real^N->real^N) (interval[vec 0,vec 1])`
        HAS_MEASURE_UNIQUE) THEN
      ASM_REWRITE_TAC[HAS_MEASURE_0];
      REWRITE_TAC[REAL_ENTIRE; MEASURE_INTERVAL] THEN
      MATCH_MP_TAC(TAUT `~b /\ (a ==> c) ==> a \/ b ==> c`) THEN CONJ_TAC THENL
       [SIMP_TAC[CONTENT_EQ_0_INTERIOR; INTERIOR_CLOSED_INTERVAL;
                 INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01];
        ASM_SIMP_TAC[REAL_MUL_LZERO; HAS_MEASURE_0]]]] THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_INJECTIVE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `!x y. (f:real^N->real^N) x = f y ==> x = y` (K ALL_TAC) THEN
  SUBGOAL_THEN
   `!s. bounded s /\ measurable s
        ==> (IMAGE (f:real^N->real^N) s) has_measure (m * measure s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!d. COUNTABLE d /\
          (!k. k IN d ==> k SUBSET interval[a,b] /\ ~(k = {}) /\
                          (?c d. k = interval[c,d])) /\
          (!k1 k2. k1 IN d /\ k2 IN d /\ ~(k1 = k2)
                   ==> interior k1 INTER interior k2 = {})
          ==> IMAGE (f:real^N->real^N) (UNIONS d) has_measure
                    (m * measure(UNIONS d))`
    ASSUME_TAC THENL
     [REWRITE_TAC[IMAGE_UNIONS] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `!g:real^N->real^N.
          linear g
          ==> !k l. k IN d /\ l IN d /\ ~(k = l)
                    ==> negligible((IMAGE g k) INTER (IMAGE g l))`
      MP_TAC THENL
       [REPEAT STRIP_TAC THEN
        ASM_CASES_TAC `!x y. (g:real^N->real^N) x = g y ==> x = y` THENL
         [ALL_TAC;
          ASM_MESON_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE;
                        NEGLIGIBLE_INTER]] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `frontier(IMAGE (g:real^N->real^N) k INTER IMAGE g l) UNION
                    interior(IMAGE g k INTER IMAGE g l)` THEN
        CONJ_TAC THENL
         [ALL_TAC;
          REWRITE_TAC[frontier] THEN MATCH_MP_TAC(SET_RULE
           `s SUBSET t ==> s SUBSET (t DIFF u) UNION u`) THEN
          REWRITE_TAC[CLOSURE_SUBSET]] THEN
        MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_CONVEX_FRONTIER THEN
          MATCH_MP_TAC CONVEX_INTER THEN CONJ_TAC THEN
          MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_MESON_TAC[CONVEX_INTERVAL];
          ALL_TAC] THEN
        REWRITE_TAC[INTERIOR_INTER] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `IMAGE (g:real^N->real^N) (interior k) INTER
                    IMAGE g (interior l)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
          EXISTS_TAC
           `IMAGE (g:real^N->real^N) (interior k INTER interior l)` THEN
          CONJ_TAC THENL
           [ASM_SIMP_TAC[IMAGE_CLAUSES; NEGLIGIBLE_EMPTY]; ASM SET_TAC[]];
          MATCH_MP_TAC(SET_RULE
           `s SUBSET u /\ t SUBSET v ==> (s INTER t) SUBSET (u INTER v)`) THEN
          CONJ_TAC THEN MATCH_MP_TAC INTERIOR_IMAGE_SUBSET THEN
          ASM_MESON_TAC[LINEAR_CONTINUOUS_AT]];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `f:real^N->real^N` th) THEN
          MP_TAC(SPEC `\x:real^N. x` th)) THEN
      ASM_REWRITE_TAC[LINEAR_ID; SET_RULE `IMAGE (\x. x) s = s`] THEN
      REPEAT STRIP_TAC THEN ASM_CASES_TAC `FINITE(d:(real^N->bool)->bool)` THENL
       [MP_TAC(ISPECL [`IMAGE (f:real^N->real^N)`; `d:(real^N->bool)->bool`]
                  HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
        MATCH_MP_TAC EQ_TRANS THEN
        EXISTS_TAC `sum d (\k:real^N->bool. m * measure k)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_UNIQUE]; ALL_TAC] THEN
        REWRITE_TAC[SUM_LMUL] THEN AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS THEN
        ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
        ASM_MESON_TAC[MEASURABLE_INTERVAL];
        ALL_TAC] THEN
      MP_TAC(ISPEC `d:(real^N->bool)->bool` COUNTABLE_AS_INJECTIVE_IMAGE) THEN
      ASM_REWRITE_TAC[INFINITE] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:num->real^N->bool`
       (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
      MP_TAC(ISPEC `s:num->real^N->bool`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      MP_TAC(ISPEC `\n:num. IMAGE (f:real^N->real^N) (s n)`
        HAS_MEASURE_COUNTABLE_NEGLIGIBLE_UNIONS_BOUNDED) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_CONJ; RIGHT_FORALL_IMP_THM;
                                  FORALL_IN_IMAGE; IN_UNIV]) THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]) THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE_INTERVAL];
          ASM_MESON_TAC[];
          ONCE_REWRITE_TAC[GSYM o_DEF] THEN
          REWRITE_TAC[GSYM IMAGE_UNIONS; IMAGE_o] THEN
          MATCH_MP_TAC BOUNDED_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_INTERVAL];
          ASM_MESON_TAC[];
          MATCH_MP_TAC BOUNDED_SUBSET THEN REWRITE_TAC[UNIONS_SUBSET] THEN
          EXISTS_TAC `interval[a:real^N,b]` THEN
          REWRITE_TAC[BOUNDED_INTERVAL] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      SUBGOAL_THEN `m * measure (UNIONS (IMAGE s (:num)):real^N->bool) =
             measure(UNIONS (IMAGE (\x. IMAGE f (s x)) (:num)):real^N->bool)`
       (fun th -> ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE; th]) THEN
      ONCE_REWRITE_TAC[GSYM LIFT_EQ] THEN
      MATCH_MP_TAC SERIES_UNIQUE THEN
      EXISTS_TAC `\n:num. lift(measure(IMAGE (f:real^N->real^N) (s n)))` THEN
      EXISTS_TAC `from 0` THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUMS_EQ THEN
      EXISTS_TAC `\n:num. m % lift(measure(s n:real^N->bool))` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN
        ASM_MESON_TAC[MEASURE_UNIQUE];
        REWRITE_TAC[LIFT_CMUL] THEN MATCH_MP_TAC SERIES_CMUL THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_MEASURE_INNER_OUTER_LE] THEN CONJ_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`interval[a,b] DIFF s:real^N->bool`; `a:real^N`;
       `b:real^N`; `e / (&1 + abs m)`] MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < &1 + abs x`; REAL_LT_DIV] THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE f (interval[a,b]) DIFF
                  IMAGE (f:real^N->real^N) (UNIONS d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN DISCH_TAC THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MEASURABLE_DIFF; measurable]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(IMAGE f (interval[a,b])) -
                  measure(IMAGE (f:real^N->real^N) (UNIONS d))` THEN
      CONJ_TAC THENL
       [ALL_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
        MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
        REPEAT(CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC]) THEN
        MATCH_MP_TAC IMAGE_SUBSET THEN ASM_SIMP_TAC[UNIONS_SUBSET]] THEN
      UNDISCH_TAC `!a b. IMAGE (f:real^N->real^N) (interval [a,b])
                         has_measure m * measure (interval [a,b])` THEN
      DISCH_THEN(ASSUME_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
      REPEAT(FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP MEASURE_UNIQUE)) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) - m * e / (&1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_ARITH `a - x <= a - y <=> y <= x`] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[GSYM REAL_SUB_LDISTRIB] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `d <= a + e ==> a = i - s ==> s - e <= i - d`)) THEN
      MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
      ASM_REWRITE_TAC[MEASURABLE_INTERVAL];
      MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `b:real^N`;
                `e / (&1 + abs m)`] MEASURABLE_OUTER_INTERVALS_BOUNDED) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &1 + abs x`] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `IMAGE (f:real^N->real^N) (UNIONS d)` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN
      SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `m * measure(s:real^N->bool) + m * e / (&1 + abs m)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_LE_LMUL];
        REWRITE_TAC[REAL_LE_LADD] THEN
        REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN
        REWRITE_TAC[GSYM real_div] THEN
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
        GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
        ASM_SIMP_TAC[REAL_LE_RMUL_EQ] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[HAS_MEASURE_LIMIT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [HAS_MEASURE_MEASURE]) THEN
  GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_LIMIT] THEN
  DISCH_THEN(MP_TAC o SPEC `e / (&1 + abs m)`) THEN
  ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &1 + abs x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*"))) THEN
  MP_TAC(ISPEC `ball(vec 0:real^N,B)` BOUNDED_SUBSET_CLOSED_INTERVAL) THEN
  REWRITE_TAC[BOUNDED_BALL; LEFT_IMP_EXISTS_THM] THEN
  REMOVE_THEN "*" MP_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `c:real^N` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `d:real^N` THEN
  DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`interval[c:real^N,d]`; `vec 0:real^N`]
    BOUNDED_SUBSET_BALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `f:real^N->real^N` LINEAR_BOUNDED_POS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN

  EXISTS_TAC `D * C:real` THEN ASM_SIMP_TAC[REAL_LT_MUL] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `s INTER (IMAGE (h:real^N->real^N) (interval[a,b]))`) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^N) (s INTER IMAGE h (interval [a,b])) =
    (IMAGE f s) INTER interval[a,b]`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_INTER; BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_LINEAR_IMAGE_INTERVAL];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC
   `m * measure(s INTER (IMAGE (h:real^N->real^N) (interval[a,b])))` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `m * e / (&1 + abs m)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[real_div; REAL_MUL_ASSOC] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &1 + abs x`] THEN
    GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[REAL_LT_RMUL_EQ] THEN REAL_ARITH_TAC] THEN
  REWRITE_TAC[GSYM REAL_SUB_LDISTRIB; REAL_ABS_MUL] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [real_abs] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `abs(z - m) < e ==> z <= w /\ w <= m ==> abs(w - m) <= e`)) THEN
  SUBST1_TAC(SYM(MATCH_MP MEASURE_UNIQUE
   (ASSUME `s INTER interval [c:real^N,d] has_measure z`))) THEN
  CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_INTER; MEASURABLE_LINEAR_IMAGE_INTERVAL;
               MEASURABLE_INTERVAL; INTER_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE
   `!v. t SUBSET v /\ v SUBSET u ==> s INTER t SUBSET s INTER u`) THEN
  EXISTS_TAC `ball(vec 0:real^N,D)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!f. (!x. h(f x) = x) /\ IMAGE f s SUBSET t ==> s SUBSET IMAGE h t`) THEN
  EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(vec 0:real^N,D * C)` THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `C * norm(x:real^N)` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC RAND_CONV [REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[REAL_LT_LMUL_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Some inductions by expressing mapping in terms of elementary matrices.    *)
(* ------------------------------------------------------------------------- *)

let INDUCT_MATRIX_ROW_OPERATIONS = prove
 (`!P:real^N^N->bool.
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!A m n. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. A$i$(swap(m,n) j))) /\
        (!A m n c. P A /\ 1 <= m /\ m <= dimindex(:N) /\
                   1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                   ==> P(lambda i. if i = m then row m A + c % row n A
                                   else row i A))
        ==> !A. P A`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "zero_row") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "diagonal") MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "swap_cols") (LABEL_TAC "row_op")) THEN
  SUBGOAL_THEN
   `!k A:real^N^N.
        (!i j. 1 <= i /\ i <= dimindex(:N) /\
               k <= j /\ j <= dimindex(:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A`
   (fun th -> GEN_TAC THEN MATCH_MP_TAC th THEN
              EXISTS_TAC `dimindex(:N) + 1` THEN ARITH_TAC) THEN
  MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "diagonal" MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[LE_0];
    ALL_TAC] THEN
  X_GEN_TAC `k:num` THEN DISCH_THEN(LABEL_TAC "ind_hyp") THEN
  DISJ_CASES_THEN2 SUBST1_TAC ASSUME_TAC (ARITH_RULE `k = 0 \/ 1 <= k`) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `k <= dimindex(:N)` THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    ASM_ARITH_TAC] THEN
  SUBGOAL_THEN
   `!A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0)
        ==> P A`
  (LABEL_TAC "nonzero_hyp") THENL
   [ALL_TAC;
    X_GEN_TAC `A:real^N^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `row k (A:real^N^N) = vec 0` THENL
     [REMOVE_THEN "zero_row" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
    SIMP_TAC[VEC_COMPONENT; row; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `l:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `l:num = k` THENL
     [REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "swap_cols" (MP_TAC o SPECL
     [`(lambda i j. (A:real^N^N)$i$swap(k,l) j):real^N^N`;
      `k:num`; `l:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN ANTS_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
      REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
      REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA])] THEN
    REMOVE_THEN "nonzero_hyp" MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k <= i <=> 1 <= i /\ SUC k <= i`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA] THEN
    ASM_REWRITE_TAC[swap] THEN MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
    STRIP_TAC THEN SUBGOAL_THEN `l:num <= k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC;
      ALL_TAC] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
   SUBGOAL_THEN
   `!l A:real^N^N.
        ~(A$k$k = &0) /\
        (!i j. 1 <= i /\ i <= dimindex (:N) /\
               SUC k <= j /\ j <= dimindex (:N) /\ ~(i = j)
               ==> A$i$j = &0) /\
        (!i. l <= i /\ i <= dimindex(:N) /\ ~(i = k) ==> A$i$k = &0)
        ==> P A`
   MP_TAC THENL
    [ALL_TAC;
     DISCH_THEN(MP_TAC o SPEC `dimindex(:N) + 1`) THEN
     REWRITE_TAC[CONJ_ASSOC; ARITH_RULE `~(n + 1 <= i /\ i <= n)`]] THEN
   MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC THENL
    [GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
     DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
     USE_THEN "ind_hyp" MATCH_MP_TAC THEN
     MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
     ASM_CASES_TAC `j:num = k` THENL
      [ASM_REWRITE_TAC[] THEN USE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
       REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  X_GEN_TAC `l:num` THEN DISCH_THEN(LABEL_TAC "inner_hyp") THEN
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "main") (LABEL_TAC "aux")) THEN
  ASM_CASES_TAC `l:num = k` THENL
   [REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `l = 0 \/ 1 <= l`) THENL
   [REMOVE_THEN "ind_hyp" MATCH_MP_TAC THEN
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `j:num = k` THENL
     [ASM_REWRITE_TAC[] THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REMOVE_THEN "main" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `l <= dimindex(:N)` THENL
   [ALL_TAC;
    REMOVE_THEN "inner_hyp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_ARITH_TAC] THEN
  REMOVE_THEN "inner_hyp" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l (A:real^N^N) + --(A$l$k/A$k$k) % row k A
                else row i A):real^N^N`]) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `!i. l <= i ==> 1 <= i` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[ARITH_RULE `SUC k <= j <=> 1 <= j /\ SUC k <= j`] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; row; COND_COMPONENT;
                 VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> x + --(x / y) * y = &0`] THEN
    REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num` THEN
    ASM_CASES_TAC `i:num = l` THEN ASM_REWRITE_TAC[] THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_RING `x = &0 /\ y = &0 ==> x + z * y = &0`) THEN
      CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN REMOVE_THEN "aux" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN REMOVE_THEN "row_op" (MP_TAC o SPECL
   [`(lambda i. if i = l then row l A + --(A$l$k / A$k$k) % row k A
                else row i (A:real^N^N)):real^N^N`;
    `l:num`; `k:num`; `(A:real^N^N)$l$k / A$k$k`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT; row; COND_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let INDUCT_MATRIX_ELEMENTARY = prove
 (`!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n c. 1 <= m /\ m <= dimindex(:N) /\
                 1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
                 ==> P(lambda i j. if i = m /\ j = n then c
                                   else if i = j then &1 else &0))
        ==> !A. P A`,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(fun th ->
    MATCH_MP_TAC INDUCT_MATRIX_ROW_OPERATIONS THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `A:real^N^N` THEN MP_TAC th) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(P:real^N^N->bool) A` THENL
   [REWRITE_TAC[GSYM IMP_CONJ]; REWRITE_TAC[GSYM IMP_CONJ_ALT]] THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN MATCH_MP_TAC EQ_IMP THEN
  AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA; matrix_mul; row] THENL
   [ASM_SIMP_TAC[mat; IN_DIMINDEX_SWAP; LAMBDA_BETA] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_RZERO; REAL_MUL_RID] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[swap; IN_NUMSEG]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    REWRITE_TAC[REAL_MUL_LZERO] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; LAMBDA_BETA; IN_NUMSEG; REAL_MUL_LID]] THEN
  ASM_SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `sum {m,n} (\k. (if k = n then c else if m = k then &1 else &0) *
                    (A:real^N^N)$k$j)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_SUPERSET THEN
    ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                 IN_NUMSEG; REAL_MUL_LZERO] THEN
    ASM_ARITH_TAC;
    ASM_SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
    REAL_ARITH_TAC]);;

let INDUCT_MATRIX_ELEMENTARY_ALT = prove
 (`!P:real^N^N->bool.
        (!A B. P A /\ P B ==> P(A ** B)) /\
        (!A i. 1 <= i /\ i <= dimindex(:N) /\ row i A = vec 0 ==> P A) /\
        (!A. (!i j. 1 <= i /\ i <= dimindex(:N) /\
                    1 <= j /\ j <= dimindex(:N) /\ ~(i = j)
                    ==> A$i$j = &0) ==> P A) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. (mat 1:real^N^N)$i$(swap(m,n) j))) /\
        (!m n. 1 <= m /\ m <= dimindex(:N) /\
               1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
               ==> P(lambda i j. if i = m /\ j = n \/ i = j then &1 else &0))
        ==> !A. P A`,
  GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC INDUCT_MATRIX_ELEMENTARY THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c = &0` THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA; COND_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lambda i j. if i = m /\ j = n then c else if i = j then &1 else &0) =
  ((lambda i j. if i = j then if j = n then inv c else &1 else &0):real^N^N) **
    ((lambda i j. if i = m /\ j = n \/ i = j then &1 else &0):real^N^N) **
    ((lambda i j. if i = j then if j = n then c else &1 else &0):real^N^N)`
  SUBST1_TAC THENL
   [ALL_TAC;
    REPEAT(MATCH_MP_TAC(ASSUME `!A B:real^N^N. P A /\ P B ==> P(A ** B)`) THEN
           CONJ_TAC) THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`]) THEN
    ASM_SIMP_TAC[LAMBDA_BETA]] THEN
  SIMP_TAC[CART_EQ; matrix_mul; LAMBDA_BETA] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  X_GEN_TAC `j:num` THEN STRIP_TAC THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG; REAL_ARITH
       `(if p then &1 else &0) * (if q then c else &0) =
        if q then if p then c else &0 else &0`] THEN
  REWRITE_TAC[REAL_ARITH
   `(if p then x else &0) * y = (if p then x * y else &0)`] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG] THEN
  ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `j:num = n` THEN ASM_REWRITE_TAC[REAL_MUL_LID; EQ_SYM_EQ] THEN
  ASM_CASES_TAC `i:num = n` THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_LID; REAL_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* The same thing in mapping form (might have been easier all along).        *)
(* ------------------------------------------------------------------------- *)

let INDUCT_LINEAR_ELEMENTARY = prove
 (`!P. (!f g. linear f /\ linear g /\ P f /\ P g ==> P(f o g)) /\
       (!f i. linear f /\ 1 <= i /\ i <= dimindex(:N) /\ (!x. (f x)$i = &0)
              ==> P f) /\
       (!c. P(\x. lambda i. c i * x$i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. x$swap(m,n) i)) /\
       (!m n. 1 <= m /\ m <= dimindex(:N) /\
              1 <= n /\ n <= dimindex(:N) /\ ~(m = n)
              ==> P(\x. lambda i. if i = m then x$m + x$n else x$i))
       ==> !f:real^N->real^N. linear f ==> P f`,
  GEN_TAC THEN
  MP_TAC(ISPEC `\A:real^N^N. P(\x:real^N. A ** x):bool`
    INDUCT_MATRIX_ELEMENTARY_ALT) THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MONO_IMP THEN CONJ_TAC THENL
   [ALL_TAC;
    DISCH_TAC THEN X_GEN_TAC `f:real^N->real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `matrix(f:real^N->real^N)`) THEN
    ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX]] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `B:real^N^N`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `\x:real^N. (B:real^N^N) ** x`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`A:real^N^N`; `m:num`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`\x:real^N. (A:real^N^N) ** x`; `m:num`]) THEN
    ASM_REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `row m (A:real^N^N) = vec 0` THEN
    ASM_SIMP_TAC[CART_EQ; row; LAMBDA_BETA; VEC_COMPONENT; matrix_vector_mul;
                 REAL_MUL_LZERO; SUM_0];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `A:real^N^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\i. (A:real^N^N)$i$i`) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum(1..dimindex(:N)) (\j. if j = i then (A:real^N^N)$i$j * (x:real^N)$j
                                else &0)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]; ALL_TAC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[] THEN COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `m:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; matrix_vector_mul; FUN_EQ_THM; LAMBDA_BETA;
               mat; IN_DIMINDEX_SWAP]
  THENL
   [ONCE_REWRITE_TAC[SWAP_GALOIS] THEN ONCE_REWRITE_TAC[COND_RAND] THEN
    ONCE_REWRITE_TAC[COND_RATOR] THEN
    SIMP_TAC[SUM_DELTA; REAL_MUL_LID; REAL_MUL_LZERO; IN_NUMSEG] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
    ASM_SIMP_TAC[SUM_DELTA; REAL_MUL_LZERO; REAL_MUL_LID; IN_NUMSEG] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `sum {m,n} (\j. if n = j \/ j = m then (x:real^N)$j else &0)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[SUM_CLAUSES; FINITE_RULES; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[REAL_ADD_RID];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
      ASM_SIMP_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM;
                   IN_NUMSEG; REAL_MUL_LZERO] THEN
      ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Hence the effect of an arbitrary linear map on a measurable set.          *)
(* ------------------------------------------------------------------------- *)

let LAMBDA_SWAP_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N)
        ==> (x = (lambda i. y$swap(m,n) i) <=>
             (lambda i. x$swap(m,n) i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
  ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
  ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT]);;

let LAMBDA_ADD_GALOIS = prove
 (`!x:real^N y:real^N.
        1 <= m /\ m <= dimindex(:N) /\ 1 <= n /\ n <= dimindex(:N) /\
        ~(m = n)
        ==> (x = (lambda i. if i = m then y$m + y$n else y$i) <=>
             (lambda i. if i = m then x$m - x$n else x$i) = y)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN
  DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
  ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let HAS_MEASURE_SHEAR_INTERVAL = prove
 (`!a b:real^N m n.
        1 <= m /\ m <= dimindex(:N) /\
        1 <= n /\ n <= dimindex(:N) /\
        ~(m = n) /\ ~(interval[a,b] = {}) /\
        &0 <= a$n
        ==> (IMAGE (\x. (lambda i. if i = m then x$m + x$n else x$i))
                   (interval[a,b]):real^N->bool)
            has_measure measure (interval [a,b])`,
  let lemma = prove
   (`!s t u v:real^N->bool.
          measurable s /\ measurable t /\ measurable u /\
          negligible(s INTER t) /\ negligible(s INTER u) /\
          negligible(t INTER u) /\
          s UNION t UNION u = v
          ==> v has_measure (measure s) + (measure t) + (measure u)`,
    REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_UNION] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_UNION; MEASURABLE_UNION] THEN
    ASM_SIMP_TAC[MEASURE_EQ_0; UNION_OVER_INTER; MEASURE_UNION;
                 MEASURABLE_UNION; NEGLIGIBLE_INTER; MEASURABLE_INTER] THEN
    REAL_ARITH_TAC)
  and lemma' = prove
   (`!s t u a:real^N.
          measurable s /\ measurable t /\
          s UNION (IMAGE (\x. a + x) t) = u /\
          negligible(s INTER (IMAGE (\x. a + x) t))
          ==> measure s + measure t = measure u`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    ASM_SIMP_TAC[MEASURE_NEGLIGIBLE_UNION; MEASURABLE_TRANSLATION_EQ;
                 MEASURE_TRANSLATION]) in
  REWRITE_TAC[INTERVAL_NE_EMPTY] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `linear((\x. lambda i. if i = m then x$m + x$n else x$i):real^N->real^N)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i)
            (interval[a:real^N,b]):real^N->bool`;
    `interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (b:real^N)$m + b$n else b$i)]`]
     lemma) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ASM_SIMP_TAC[LAMBDA_ADD_GALOIS; UNWIND_THM1] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[] THEN
    REWRITE_TAC[TAUT `(p /\ x) /\ (q /\ x) /\ r <=> x /\ p /\ q /\ r`;
                TAUT `(p /\ x) /\ q /\ (r /\ x) <=> x /\ p /\ q /\ r`;
                TAUT `((p /\ x) /\ q) /\ (r /\ x) /\ s <=>
                            x /\ p /\ q /\ r /\ s`;
            TAUT `(a /\ x \/ (b /\ x) /\ c \/ (d /\ x) /\ e <=> f /\ x) <=>
                  x ==> (a \/ b /\ c \/ d /\ e <=> f)`] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
    REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
     [ALL_TAC;
      GEN_TAC THEN DISCH_THEN(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THENL
     [EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`;
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (b:real^N)$m}`]
    THEN (CONJ_TAC THENL
      [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
       REWRITE_TAC[VECTOR_SUB_EQ] THEN
       ASM_MESON_TAC[BASIS_INJ];
       ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                    NOT_IN_EMPTY] THEN
       FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN ASM_REWRITE_TAC[] THEN
       ASM_REAL_ARITH_TAC]);
    ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE;
               MEASURABLE_LINEAR_IMAGE_INTERVAL;
               MEASURABLE_INTERVAL] THEN
  MP_TAC(ISPECL
   [`interval[a,(lambda i. if i = m then (b:real^N)$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x <= a$m}`;
    `interval[a,(lambda i. if i = m then b$m + b$n else b$i)] INTER
       {x:real^N | (basis m - basis n) dot x >= (b:real^N)$m}`;
    `interval[a:real^N,
              (lambda i. if i = m then (a:real^N)$m + b$n
                         else (b:real^N)$i)]`;
    `(lambda i. if i = m then (a:real^N)$m - (b:real^N)$m
                else &0):real^N`]
     lemma') THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_INTERVAL;
                 CONVEX_HALFSPACE_LE; CONVEX_HALFSPACE_GE;
                 CONVEX_INTER; MEASURABLE_CONVEX; BOUNDED_INTER;
                 BOUNDED_LINEAR_IMAGE; BOUNDED_INTERVAL] THEN
    REWRITE_TAC[INTER] THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = (lambda i. p i) + y <=>
                                   x - (lambda i. p i) = y`] THEN
    ASM_SIMP_TAC[IN_INTERVAL; IN_ELIM_THM; LAMBDA_BETA;
                 DOT_BASIS; DOT_LSUB; UNWIND_THM1;
                 VECTOR_SUB_COMPONENT] THEN
    ONCE_REWRITE_TAC[MESON[]
       `(!i:num. P i) <=> P m /\ (!i. ~(i = m) ==> P i)`] THEN
    ASM_SIMP_TAC[REAL_SUB_RZERO] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN
      FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC
       `!i. ~(i = m)
            ==> 1 <= i /\ i <= dimindex (:N)
                ==> (a:real^N)$i <= (x:real^N)$i /\
                    x$i <= (b:real^N)$i` THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ONCE_REWRITE_TAC[TAUT `((a /\ b) /\ c) /\ (d /\ e) /\ f <=>
                             (b /\ e) /\ a /\ c /\ d /\ f`] THEN
      ONCE_REWRITE_TAC[SET_RULE
       `{x | P x /\ Q x} = {x | P x} INTER {x | Q x}`] THEN
      MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{x:real^N | (basis m - basis n) dot x = (a:real^N)$m}`
      THEN CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
        REWRITE_TAC[VECTOR_SUB_EQ] THEN
        ASM_MESON_TAC[BASIS_INJ];
        ASM_SIMP_TAC[DOT_LSUB; DOT_BASIS; SUBSET; IN_ELIM_THM;
                     NOT_IN_EMPTY] THEN
        FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(REAL_ARITH
   `a:real = b + c ==> a = x + b ==> x = c`) THEN
  ASM_SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES;
               LAMBDA_BETA] THEN
  REPEAT(COND_CASES_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `n:num`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]) THEN
  SUBGOAL_THEN `1..dimindex(:N) = m INSERT ((1..dimindex(:N)) DELETE m)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_DELETE; IN_NUMSEG] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[PRODUCT_CLAUSES; FINITE_DELETE; FINITE_NUMSEG] THEN
  ASM_SIMP_TAC[IN_DELETE] THEN
  MATCH_MP_TAC(REAL_RING
   `s1:real = s3 /\ s2 = s3
    ==> ((bm + bn) - am) * s1 =
        ((am + bn) - am) * s2 + (bm - am) * s3`) THEN
  CONJ_TAC THEN MATCH_MP_TAC PRODUCT_EQ THEN
  SIMP_TAC[IN_DELETE] THEN REAL_ARITH_TAC);;

let HAS_MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * measure s)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC INDUCT_LINEAR_ELEMENTARY THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (MP_TAC o SPEC `IMAGE (g:real^N->real^N) s`)
     (MP_TAC o SPEC `s:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [HAS_MEASURE_MEASURABLE_MEASURE] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MATRIX_COMPOSE; DET_MUL; REAL_ABS_MUL] THEN
    REWRITE_TAC[IMAGE_o; GSYM REAL_MUL_ASSOC];

    MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `m:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(!x y. (f:real^N->real^N) x = f y ==> x = y)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_SINGULAR_INTO_HYPERPLANE] THEN
      EXISTS_TAC `basis m:real^N` THEN
      ASM_SIMP_TAC[BASIS_NONZERO; DOT_BASIS];
      ALL_TAC] THEN
    MP_TAC(ISPEC `matrix f:real^N^N` INVERTIBLE_DET_NZ) THEN
    ASM_SIMP_TAC[INVERTIBLE_LEFT_INVERSE; MATRIX_LEFT_INVERTIBLE_INJECTIVE;
                 MATRIX_WORKS; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[HAS_MEASURE_0] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_LINEAR_SINGULAR_IMAGE];

    MAP_EVERY X_GEN_TAC [`c:num->real`; `s:real^N->bool`] THEN
    DISCH_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o REWRITE_RULE[HAS_MEASURE_MEASURE]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `c:num->real` o
     MATCH_MP HAS_MEASURE_STRETCH) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix; LAMBDA_BETA] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_DIAGONAL o rand o snd) THEN
    REWRITE_TAC[diagonal_matrix] THEN
    SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; REAL_MUL_RZERO] THEN
    DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
    REWRITE_TAC[REAL_MUL_RID];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    ASM_SIMP_TAC[linear; LAMBDA_BETA; IN_DIMINDEX_SWAP; VECTOR_ADD_COMPONENT;
                 VECTOR_MUL_COMPONENT; CART_EQ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN `matrix (\x:real^N. lambda i. x$swap (m,n) i):real^N^N =
                  transp(lambda i j. (mat 1:real^N^N)$i$swap (m,n) j)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[MATRIX_EQ; LAMBDA_BETA; IN_DIMINDEX_SWAP;
                    matrix_vector_mul; CART_EQ; matrix; mat; basis;
                    COND_COMPONENT; transp] THEN
      REWRITE_TAC[EQ_SYM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[DET_TRANSP] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) DET_PERMUTE_COLUMNS o
        rand o lhand o rand o snd) THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG; ETA_AX] THEN
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[DET_I; REAL_ABS_SIGN; REAL_MUL_RID; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x:real^N. lambda i. x$swap (m,n) i)
              (interval[a,b]):real^N->bool =
      interval[(lambda i. a$swap (m,n) i),
               (lambda i. b$swap (m,n) i)]`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_INTERVAL; IN_IMAGE] THEN
      ASM_SIMP_TAC[LAMBDA_SWAP_GALOIS; UNWIND_THM1] THEN
      SIMP_TAC[LAMBDA_BETA] THEN GEN_TAC THEN EQ_TAC THEN
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `swap(m,n) (i:num)`) THEN
      ASM_SIMP_TAC[IN_DIMINDEX_SWAP] THEN
      ASM_MESON_TAC[REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] SWAP_IDEMPOTENT];
      ALL_TAC] THEN
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_INTERVAL] THEN
    REWRITE_TAC[MEASURE_INTERVAL] THEN
    ASM_SIMP_TAC[CONTENT_CLOSED_INTERVAL; GSYM INTERVAL_NE_EMPTY] THEN
    DISCH_THEN(K ALL_TAC) THEN SIMP_TAC[LAMBDA_BETA] THEN
    ASM_SIMP_TAC[GSYM VECTOR_SUB_COMPONENT; IN_DIMINDEX_SWAP] THEN
    MP_TAC(ISPECL [`\i. (b - a:real^N)$i`; `swap(m:num,n)`; `1..dimindex(:N)`]
                (GSYM PRODUCT_PERMUTE)) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[PERMUTES_SWAP; IN_NUMSEG];

    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_MEASURE_LINEAR_SUFFICIENT THEN
    MATCH_MP_TAC(TAUT `a /\ (a ==> b) ==> a /\ b`) THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[linear; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
                   VECTOR_MUL_COMPONENT; CART_EQ] THEN REAL_ARITH_TAC;
      DISCH_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
    SUBGOAL_THEN
      `det(matrix(\x. lambda i. if i = m then (x:real^N)$m + x$n
                                else x$i):real^N^N) = &1`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[matrix; basis; COND_COMPONENT; LAMBDA_BETA] THEN
      FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
       `~(m:num = n) ==> m < n \/ n < m`))
      THENL
       [W(MP_TAC o PART_MATCH (lhs o rand) DET_UPPERTRIANGULAR o lhs o snd);
        W(MP_TAC o PART_MATCH (lhs o rand) DET_LOWERTRIANGULAR o lhs o snd)]
      THEN ASM_SIMP_TAC[LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                        matrix; REAL_ADD_RID; COND_ID;
                        PRODUCT_CONST_NUMSEG; REAL_POW_ONE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REPEAT GEN_TAC THEN REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ABS_NUM; REAL_MUL_LID] THEN
    ASM_CASES_TAC `interval[a:real^N,b] = {}` THENL
     [ASM_SIMP_TAC[IMAGE_CLAUSES; HAS_MEASURE_EMPTY; MEASURE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (\x. lambda i. if i = m then x$m + x$n else x$i) (interval [a,b]) =
      IMAGE (\x:real^N. (lambda i. if i = m \/ i = n then a$n else &0) +
                        x)
            (IMAGE (\x:real^N. lambda i. if i = m then x$m + x$n else x$i)
                   (IMAGE (\x. (lambda i. if i = n then --(a$n) else &0) + x)
                          (interval[a,b])))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[FUN_EQ_THM; o_THM; VECTOR_ADD_COMPONENT; LAMBDA_BETA;
                   CART_EQ] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `i:num`] THEN
      STRIP_TAC THEN ASM_CASES_TAC `i:num = m` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:num = n` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC HAS_MEASURE_TRANSLATION THEN
    SUBGOAL_THEN
     `measure(interval[a,b]) =
      measure(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool)`
    SUBST1_TAC THENL [REWRITE_TAC[MEASURE_TRANSLATION]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(IMAGE (\x:real^N. (lambda i. if i = n then --(a$n) else &0) + x)
                    (interval[a,b]):real^N->bool = {})`
    MP_TAC THENL [ASM_SIMP_TAC[IMAGE_EQ_EMPTY]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `c + x:real^N = &1 % x + c`] THEN
    ASM_REWRITE_TAC[IMAGE_AFFINITY_INTERVAL; REAL_POS] THEN
    DISCH_TAC THEN MATCH_MP_TAC HAS_MEASURE_SHEAR_INTERVAL THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MEASURABLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s ==> measurable(IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s
        ==> measure(IMAGE f s) = abs(det(matrix f)) * measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let HAS_MEASURE_LINEAR_IMAGE_ALT = prove
 (`!f:real^N->real^N s m.
        linear f /\ s has_measure m
        ==> (IMAGE f s) has_measure (abs(det(matrix f)) * m)`,
  MESON_TAC[MEASURE_UNIQUE; measurable; HAS_MEASURE_LINEAR_IMAGE]);;

let HAS_MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f s. linear f /\ measurable s /\ abs(det(matrix f)) = &1
         ==> (IMAGE f s) has_measure (measure s)`,
  MESON_TAC[HAS_MEASURE_LINEAR_IMAGE; REAL_MUL_LID]);;

let MEASURE_LINEAR_IMAGE_SAME = prove
 (`!f:real^N->real^N s.
        linear f /\ measurable s /\ abs(det(matrix f)) = &1
        ==> measure(IMAGE f s) = measure s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_SAME) THEN
  SIMP_TAC[HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURABLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable (IMAGE f s) <=> measurable s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE MEASURABLE_LINEAR_IMAGE));;

add_linear_invariants [MEASURABLE_LINEAR_IMAGE_EQ];;

let NEGLIGIBLE_LINEAR_IMAGE = prove
 (`!f:real^N->real^N s. linear f /\ negligible s ==> negligible(IMAGE f s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM HAS_MEASURE_0] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  REWRITE_TAC[REAL_MUL_RZERO]);;

let NEGLIGIBLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> (negligible (IMAGE f s) <=> negligible s)`,
  MATCH_ACCEPT_TAC(LINEAR_INVARIANT_RULE NEGLIGIBLE_LINEAR_IMAGE));;

add_linear_invariants [NEGLIGIBLE_LINEAR_IMAGE_EQ];;

let HAS_MEASURE_ORTHOGONAL_IMAGE = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f /\ s has_measure m
        ==> (IMAGE f s) has_measure m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_LINEAR) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_LINEAR_IMAGE_ALT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(REAL_RING `x = &1 ==> x * m = m`) THEN
  REWRITE_TAC[REAL_ARITH `abs x = &1 <=> x = &1 \/ x = -- &1`] THEN
  MATCH_MP_TAC DET_ORTHOGONAL_MATRIX THEN
  ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION_MATRIX]);;

let HAS_MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s m.
        orthogonal_transformation f
        ==> ((IMAGE f s) has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[HAS_MEASURE_ORTHOGONAL_IMAGE] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE_o) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
   REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HAS_MEASURE_ORTHOGONAL_IMAGE) THEN
  ASM_SIMP_TAC[GSYM IMAGE_o; IMAGE_I]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] HAS_MEASURE_ORTHOGONAL_IMAGE_EQ];;

let MEASURE_ORTHOGONAL_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        orthogonal_transformation f
        ==> measure(IMAGE f s) = measure s`,
  SIMP_TAC[measure; HAS_MEASURE_ORTHOGONAL_IMAGE_EQ]);;

add_linear_invariants
 [REWRITE_RULE[ORTHOGONAL_TRANSFORMATION] MEASURE_ORTHOGONAL_IMAGE_EQ];;

let HAS_MEASURE_ISOMETRY = prove
 (`!f:real^M->real^N s m.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> (IMAGE f s has_measure m <=> s has_measure m)`,
  REPEAT STRIP_TAC THEN
  TRANS_TAC EQ_TRANS
   `IMAGE ((\x. lambda i. x$i):real^N->real^M) (IMAGE (f:real^M->real^N) s)
    has_measure m` THEN
  CONJ_TAC THENL
   [SPEC_TAC(`IMAGE (f:real^M->real^N) s`,`s:real^N->bool`) THEN GEN_TAC THEN
    CONV_TAC SYM_CONV THEN REWRITE_TAC[has_measure] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
        HAS_INTEGRAL_TWIZZLE_EQ o lhand o snd) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM I_DEF; PERMUTES_I];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC HAS_MEASURE_ORTHOGONAL_IMAGE_EQ THEN
    ASM_REWRITE_TAC[ORTHOGONAL_TRANSFORMATION; o_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      X_GEN_TAC `x:real^M` THEN
      TRANS_TAC EQ_TRANS `norm((f:real^M->real^N) x)` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      SIMP_TAC[NORM_EQ; dot; LAMBDA_BETA] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC SUM_EQ_NUMSEG THEN SIMP_TAC[LAMBDA_BETA]]]);;

let MEASURABLE_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (measurable(IMAGE f s) <=> measurable s)`,
  REPEAT STRIP_TAC THEN TRANS_TAC EQ_TRANS
   `measurable(IMAGE ((\x. lambda i. x$i):real^N->real^M)
                     (IMAGE (f:real^M->real^N) s))` THEN
  CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN REWRITE_TAC[measurable] THEN
    AP_TERM_TAC THEN ABS_TAC THEN MATCH_MP_TAC HAS_MEASURE_ISOMETRY THEN
    ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      SIMP_TAC[NORM_EQ; dot; LAMBDA_BETA] THEN
      ASM_MESON_TAC[]];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC MEASURABLE_LINEAR_IMAGE_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[linear; CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT;
               VECTOR_MUL_COMPONENT];
      SIMP_TAC[CART_EQ; LAMBDA_BETA; o_DEF] THEN
      ASM_MESON_TAC[CART_EQ]]]);;

let MEASURE_ISOMETRY = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x. norm(f x) = norm x)
        ==> measure (IMAGE f s) = measure s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measure] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP HAS_MEASURE_ISOMETRY th]));;

(* ------------------------------------------------------------------------- *)
(* Measure of a standard simplex.                                            *)
(* ------------------------------------------------------------------------- *)

let CONGRUENT_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))} =
           IMAGE (\x:real^N. lambda i. sum(1..inverse p(i)) (\j. x$j))
                 {x | (!i. 1 <= i /\ i <= dimindex (:N) ==> &0 <= x$i) /\
                      sum (1..dimindex (:N)) (\i. x$i) <= &1}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
                 ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
                 ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1] THEN
    STRIP_TAC THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    ASM_SIMP_TAC[SUM_SING_NUMSEG; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[GSYM ADD1; SUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
    ASM_SIMP_TAC[REAL_LE_ADDR] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  STRIP_TAC THEN
  EXISTS_TAC `(lambda i. if i = 1 then x$(p 1)
                         else (x:real^N)$p(i) - x$p(i - 1)):real^N` THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LAMBDA_BETA; LAMBDA_BETA_PERM; LE_REFL;
               ARITH_RULE `i < n ==> i <= n /\ i + 1 <= n`;
               ARITH_RULE `1 <= n + 1`; DIMINDEX_GE_1; CART_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= inverse (p:num->num) i /\
                  !x. x <= inverse p i ==> x <= dimindex(:N)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_INVERSE; IN_NUMSEG; LE_TRANS; PERMUTES_IN_IMAGE];
      ASM_SIMP_TAC[LAMBDA_BETA] THEN ASM_SIMP_TAC[SUM_CLAUSES_LEFT; ARITH]] THEN
    SIMP_TAC[ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    FIRST_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
     `1 <= p ==> p = 1 \/ 2 <= p`) o CONJUNCT1) THEN
    ASM_SIMP_TAC[ARITH] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP PERMUTES_INVERSES th]) THEN
    REWRITE_TAC[REAL_ADD_RID] THEN TRY REAL_ARITH_TAC THEN
    ASM_MESON_TAC[PERMUTES_INVERSE_EQ; PERMUTES_INVERSE];

    X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[REAL_SUB_LE] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i - 1`) THEN
    ASM_SIMP_TAC[SUB_ADD] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;

    SIMP_TAC[SUM_CLAUSES_LEFT; DIMINDEX_GE_1; ARITH;
             ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV o BINDER_CONV)
                [GSYM REAL_MUL_LID] THEN
    ONCE_REWRITE_TAC[SUM_PARTIAL_PRE] THEN
    REWRITE_TAC[REAL_SUB_REFL; REAL_MUL_RZERO; SUM_0; COND_ID] THEN
    REWRITE_TAC[REAL_MUL_LID; ARITH; REAL_SUB_RZERO] THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_ADD_RID] THEN
    ASM_REWRITE_TAC[REAL_ARITH `x + y - x:real = y`] THEN
    ASM_MESON_TAC[DIMINDEX_GE_1;
                  ARITH_RULE `1 <= n /\ ~(2 <= n) ==> n = 1`]]);;

let HAS_MEASURE_IMAGE_STD_SIMPLEX = prove
 (`!p. p permutes 1..dimindex(:N)
       ==> {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                       (!i. 1 <= i /\ i < dimindex(:N)
                            ==> x$(p i) <= x$(p(i + 1)))}
           has_measure
           (measure (convex hull
             (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CONGRUENT_IMAGE_STD_SIMPLEX] THEN
  ASM_SIMP_TAC[GSYM STD_SIMPLEX] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE_SAME THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                 GSYM SUM_ADD_NUMSEG; GSYM SUM_LMUL] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ_NUMSEG THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC
     `abs(det
       ((lambda i. ((lambda i j. if j <= i then &1 else &0):real^N^N)
                   $inverse p i)
        :real^N^N))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[CART_EQ] THEN
      ASM_SIMP_TAC[matrix; LAMBDA_BETA; BASIS_COMPONENT; COND_COMPONENT;
                   LAMBDA_BETA_PERM; PERMUTES_INVERSE] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `sum (1..inverse (p:num->num) i)
                      (\k. if k = j then &1 else &0)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN
        ASM_SIMP_TAC[IN_NUMSEG; PERMUTES_IN_IMAGE; basis] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC LAMBDA_BETA THEN
        ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; LE_TRANS;
                      PERMUTES_INVERSE];
        ASM_SIMP_TAC[SUM_DELTA; IN_NUMSEG]];
      ALL_TAC] THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE; DET_PERMUTE_ROWS; ETA_AX] THEN
    REWRITE_TAC[REAL_ABS_MUL; REAL_ABS_SIGN; REAL_MUL_LID] THEN
    MATCH_MP_TAC(REAL_ARITH `x = &1 ==> abs x = &1`) THEN
    ASM_SIMP_TAC[DET_LOWERTRIANGULAR; GSYM NOT_LT; LAMBDA_BETA] THEN
    REWRITE_TAC[LT_REFL; PRODUCT_CONST_NUMSEG; REAL_POW_ONE]]);;

let HAS_MEASURE_STD_SIMPLEX = prove
 (`(convex hull (vec 0:real^N INSERT {basis i | 1 <= i /\ i <= dimindex(:N)}))
   has_measure inv(&(FACT(dimindex(:N))))`,
  let lemma = prove
   (`!f:num->real. (!i. 1 <= i /\ i < n ==> f i <= f(i + 1)) <=>
                   (!i j. 1 <= i /\ i <= j /\ j <= n ==> f i <= f j)`,
    GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
     [GEN_TAC THEN INDUCT_TAC THEN
      SIMP_TAC[LE; REAL_LE_REFL] THEN
      STRIP_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(f:num->real) j` THEN
      ASM_SIMP_TAC[ARITH_RULE `SUC x <= y ==> x <= y`] THEN
      REWRITE_TAC[ADD1] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  MP_TAC(ISPECL
   [`\p. {x:real^N | &0 <= x$(p 1) /\ x$(p(dimindex(:N))) <= &1 /\
                     (!i. 1 <= i /\ i < dimindex(:N)
                          ==> x$(p i) <= x$(p(i + 1)))}`;
    `{p | p permutes 1..dimindex(:N)}`]
    HAS_MEASURE_NEGLIGIBLE_UNIONS_IMAGE) THEN
  ASM_SIMP_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                            HAS_MEASURE_IMAGE_STD_SIMPLEX; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_PERMUTATIONS; FINITE_NUMSEG;
               CARD_PERMUTATIONS; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`p:num->num`; `q:num->num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?i. i IN 1..dimindex(:N) /\ ~(p i:num = q i)` MP_TAC THENL
     [ASM_MESON_TAC[permutes; FUN_EQ_THM]; ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
    REWRITE_TAC[TAUT `a ==> ~(b /\ ~c) <=> a /\ b ==> c`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^N | (basis(p(k:num)) - basis(q k)) dot x = &0}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN REWRITE_TAC[VECTOR_SUB_EQ] THEN
      MATCH_MP_TAC BASIS_NE THEN ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; DOT_LSUB; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[DOT_BASIS; GSYM IN_NUMSEG; PERMUTES_IN_IMAGE] THEN
    SUBGOAL_THEN `?l. (q:num->num) l = p(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= l /\ l <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < l` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    SUBGOAL_THEN `?m. (p:num->num) m = q(k:num)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[permutes]; ALL_TAC] THEN
    SUBGOAL_THEN `1 <= m /\ m <= dimindex(:N)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG]; ALL_TAC] THEN
    SUBGOAL_THEN `k:num < m` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN REWRITE_TAC[LE_LT] THEN
      ASM_MESON_TAC[PERMUTES_INJECTIVE; IN_NUMSEG];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[lemma] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `l:num`]) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`k:num`; `m:num`]) THEN
    ASM_SIMP_TAC[LT_IMP_LE; IMP_IMP; REAL_LE_ANTISYM; REAL_SUB_0] THEN
    MATCH_MP_TAC EQ_IMP THEN BINOP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE; IN_NUMSEG; DOT_BASIS];
    ALL_TAC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
    REWRITE_TAC[GSYM numseg; FINITE_NUMSEG];
    ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD `~(y = &0) ==> (x = inv y <=> y * x = &1)`;
               REAL_OF_NUM_EQ; FACT_NZ] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `measure(interval[vec 0:real^N,vec 1])` THEN CONJ_TAC THENL
   [AP_TERM_TAC; REWRITE_TAC[MEASURE_INTERVAL; CONTENT_UNIT]] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
                RIGHT_FORALL_IMP_THM; IN_ELIM_THM] THEN
    SIMP_TAC[IMP_IMP; IN_INTERVAL; LAMBDA_BETA; VEC_COMPONENT] THEN
    X_GEN_TAC `p:num->num` THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THENL
     [EXISTS_TAC `(x:real^N)$(p 1)`;
      EXISTS_TAC `(x:real^N)$(p(dimindex(:N)))`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o MATCH_MP PERMUTES_SURJECTIVE) THEN
    ASM_MESON_TAC[LE_REFL; PERMUTES_IN_IMAGE; IN_NUMSEG];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `s SUBSET UNIONS(IMAGE f t) <=>
                        !x. x IN s ==> ?y. y IN t /\ x IN f y`] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERVAL; IN_ELIM_THM] THEN
  SIMP_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `\i j. ~((x:real^N)$j <= x$i)` TOPOLOGICAL_SORT) THEN
  REWRITE_TAC[REAL_NOT_LE; REAL_NOT_LT] THEN
  ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`dimindex(:N)`; `1..dimindex(:N)`]) THEN
  REWRITE_TAC[HAS_SIZE_NUMSEG_1; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` (CONJUNCTS_THEN2
   (ASSUME_TAC o GSYM) ASSUME_TAC)) THEN
  EXISTS_TAC `\i. if i IN 1..dimindex(:N) then f(i) else i` THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE
    `1 <= i /\ i <= j /\ j <= n <=>
     1 <= i /\ 1 <= j /\ i <= n /\ j <= n /\ i <= j`] THEN
  ASM_SIMP_TAC[IN_NUMSEG; LE_REFL; DIMINDEX_GE_1] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LE_REFL; DIMINDEX_GE_1; LE_LT; REAL_LE_LT]] THEN
  SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG] THEN
  SIMP_TAC[IN_NUMSEG] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence the measure of a general simplex.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_SIMPLEX_0 = prove
 (`!l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (vec 0 INSERT set_of_list l)) has_measure
            abs(det(vector l)) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vec 0 INSERT (set_of_list l) =
        IMAGE (\x:real^N. transp(vector l:real^N^N) ** x)
              (vec 0 INSERT {basis i:real^N | 1 <= i /\ i <= dimindex(:N)})`
  SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    REWRITE_TAC[IMAGE_CLAUSES; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[MATRIX_VECTOR_MUL_RZERO] THEN AP_TERM_TAC THEN
    SIMP_TAC[matrix_vector_mul; vector; transp; LAMBDA_BETA; basis] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    SIMP_TAC[REAL_MUL_RZERO; SUM_DELTA] THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
    ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> ~(b /\ c ==> ~a)`] THEN
    X_GEN_TAC `y:real^N` THEN SIMP_TAC[LAMBDA_BETA; REAL_MUL_RID] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
    REWRITE_TAC[NOT_IMP; REAL_MUL_RID; GSYM CART_EQ] THEN
    ASM_REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL] THEN
    EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `SUC i`; EXISTS_TAC `i - 1`] THEN
    ASM_REWRITE_TAC[SUC_SUB1] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE; MATRIX_VECTOR_MUL_LINEAR] THEN
  SUBGOAL_THEN
   `det(vector l:real^N^N) = det(matrix(\x:real^N. transp(vector l) ** x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[MATRIX_OF_MATRIX_VECTOR_MUL; DET_TRANSP]; ALL_TAC] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[GSYM(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
                 HAS_MEASURE_STD_SIMPLEX)] THEN
  MATCH_MP_TAC HAS_MEASURE_LINEAR_IMAGE THEN
  REWRITE_TAC[MATRIX_VECTOR_MUL_LINEAR] THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN REWRITE_TAC[BOUNDED_INSERT] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN MATCH_MP_TAC FINITE_IMAGE THEN
  REWRITE_TAC[GSYM numseg; FINITE_NUMSEG]);;

let HAS_MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> (convex hull (set_of_list(CONS a l))) has_measure
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `MAP (\x:real^N. x - a) l` HAS_MEASURE_SIMPLEX_0) THEN
  ASM_REWRITE_TAC[LENGTH_MAP; set_of_list] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o MATCH_MP HAS_MEASURE_TRANSLATION) THEN
  REWRITE_TAC[GSYM CONVEX_HULL_TRANSLATION] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[IMAGE_CLAUSES; VECTOR_ADD_RID; SET_OF_LIST_MAP] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; VECTOR_ARITH `a + x - a:real^N = x`;
              SET_RULE `IMAGE (\x. x) s = s`]);;

let MEASURABLE_CONVEX_HULL = prove
 (`!s. bounded s ==> measurable(convex hull s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; BOUNDED_CONVEX_HULL]);;

let MEASURABLE_SIMPLEX = prove
 (`!l. measurable(convex hull (set_of_list l))`,
  GEN_TAC THEN MATCH_MP_TAC MEASURABLE_CONVEX_HULL THEN
  MATCH_MP_TAC FINITE_IMP_BOUNDED THEN REWRITE_TAC[FINITE_SET_OF_LIST]);;

let MEASURE_SIMPLEX = prove
 (`!a l:(real^N)list.
        LENGTH l = dimindex(:N)
        ==> measure(convex hull (set_of_list(CONS a l))) =
            abs(det(vector(MAP (\x. x - a) l))) / &(FACT(dimindex(:N)))`,
  MESON_TAC[HAS_MEASURE_SIMPLEX; HAS_MEASURE_MEASURABLE_MEASURE]);;

(* ------------------------------------------------------------------------- *)
(* Area of a triangle.                                                       *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        convex hull {a,b,c} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^2`; `[b;c]:(real^2)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_2; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_2; VECTOR_2] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_2; ARITH]);;

let MEASURABLE_TRIANGLE = prove
 (`!a b c:real^N. measurable(convex hull {a,b,c})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TRIANGLE = prove
 (`!a b c:real^2.
        measure(convex hull {a,b,c}) =
        abs((b$1 - a$1) * (c$2 - a$2) - (b$2 - a$2) * (c$1 - a$1)) / &2`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* Volume of a tetrahedron.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        convex hull {a,b,c,d} has_measure
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) /
           &6`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `[b;c;d]:(real^3)list`] HAS_MEASURE_SIMPLEX) THEN
  REWRITE_TAC[LENGTH; DIMINDEX_3; ARITH; set_of_list; MAP] THEN
  CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[DET_3; VECTOR_3] THEN
  SIMP_TAC[VECTOR_SUB_COMPONENT; DIMINDEX_3; ARITH]);;

let MEASURABLE_TETRAHEDRON = prove
 (`!a b c d:real^N. measurable(convex hull {a,b,c,d})`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC MEASURABLE_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  MATCH_MP_TAC BOUNDED_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_BOUNDED THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

let MEASURE_TETRAHEDRON = prove
 (`!a b c d:real^3.
        measure(convex hull {a,b,c,d}) =
        abs((b$1 - a$1) * (c$2 - a$2) * (d$3 - a$3) +
            (b$2 - a$2) * (c$3 - a$3) * (d$1 - a$1) +
            (b$3 - a$3) * (c$1 - a$1) * (d$2 - a$2) -
            (b$1 - a$1) * (c$3 - a$3) * (d$2 - a$2) -
            (b$2 - a$2) * (c$1 - a$1) * (d$3 - a$3) -
            (b$3 - a$3) * (c$2 - a$2) * (d$1 - a$1)) / &6`,
  REWRITE_TAC[REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]
               HAS_MEASURE_TETRAHEDRON]);;

(* ------------------------------------------------------------------------- *)
(* Measure is continuous with Hausdorff distance: several formulations.      *)
(* ------------------------------------------------------------------------- *)

let MEASURE_CONTINUOUS_WITH_HAUSDIST = prove
 (`!s:real^N->bool e.
        bounded s /\ convex s /\ ~(s = {}) /\ &0 < e
        ==> ?d. &0 < d /\
                !t. bounded t /\ convex t /\ ~(t = {}) /\ hausdist(s,t) < d
                    ==> abs(measure(t) - measure(s)) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier s:real^N->bool`; `e:real`]
    MEASURABLE_OUTER_OPEN) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP NEGLIGIBLE_CONVEX_FRONTIER) THEN
  REWRITE_TAC[NEGLIGIBLE_EQ_MEASURE_0] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_ADD_LID] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `setdist(frontier s,(:real^N) DIFF u)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_FRONTIER_BOUNDED;
                 GSYM OPEN_CLOSED; SETDIST_POS_LE; FRONTIER_EQ_EMPTY] THEN
    REWRITE_TAC[SET_RULE `UNIV DIFF s = {} <=> s = UNIV`; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_BOUNDED_UNIV]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_MEASURABLE_UNIV]; ASM SET_TAC[]];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `u < e ==> a <= u ==> a < e`)) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_SUB_LE_MEASURE_SYMDIFF o
      lhand o snd) THEN
    ASM_SIMP_TAC[MEASURABLE_CONVEX] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNION; MEASURABLE_DIFF; MEASURABLE_CONVEX] THEN
    ONCE_REWRITE_TAC[UNION_COMM] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`;
                   `setdist(frontier s,(:real^N) DIFF u)`]
        CONVEX_SYMDIFF_CLOSE_TO_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_BALL_0] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
    REWRITE_TAC[NORM_ARITH `~(norm(y:real^N) < e) = e <= dist(x,x + y)`] THEN
    MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC[]]);;

let MEASURE_CONTINUOUS_WITH_HAUSDIST_EXPLICIT = prove
 (`!s:real^N->bool e.
        bounded s /\ convex s /\ &0 < e
        ==> ?d. &0 < d /\
                !t. convex t /\
                    (!y. y IN s ==> ?x. x IN t /\ dist(x,y) < d) /\
                    (!y. y IN t ==> ?x. x IN s /\ dist(x,y) < d)
                    ==> abs(measure(t) - measure(s)) < e`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `&1` THEN SIMP_TAC[MEASURE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `e:real`]
    MEASURE_CONTINUOUS_WITH_HAUSDIST) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  EXISTS_TAC `d / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `&1` THEN SIMP_TAC[MEASURE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `{a + b:real^N | a IN s /\ b IN ball(vec 0,d / &2)}` THEN
    ASM_SIMP_TAC[BOUNDED_SUMS; BOUNDED_BALL] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_BALL_0; VECTOR_ARITH
     `x:real^N = a + b <=> b = x - a`] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[UNWIND_THM2] THEN
    ASM_MESON_TAC[dist; DIST_SYM];
    DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < d /\ x <= d / &2 ==> x < d`) THEN
    ASM_SIMP_TAC[REAL_HAUSDIST_LE_EQ] THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS; SETDIST_LE_DIST; IN_SING;
                  DIST_SYM; SETDIST_SYM]]);;

let MEASURE_SEMICONTINUOUS_WITH_HAUSDIST_EXPLICIT = prove
 (`!s:real^N->bool e.
        bounded s /\ negligible(frontier s) /\ &0 < e
        ==> ?d. &0 < d /\
                !s'. measurable s' /\
                     (!y. y IN s' ==> ?x. x IN s /\ dist(x,y) < d)
                     ==> measure(s') < measure(s) + e`,
  REWRITE_TAC[NEGLIGIBLE_EQ_MEASURE_0] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[NOT_IN_EMPTY; GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `&1` THEN SIMP_TAC[MEASURE_EMPTY] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier s:real^N->bool`; `e:real`]
    MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_ADD_LID] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `setdist(frontier s,(:real^N) DIFF u)` THEN CONJ_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN
    ASM_SIMP_TAC[SETDIST_EQ_0_COMPACT_CLOSED; COMPACT_FRONTIER_BOUNDED;
                 GSYM OPEN_CLOSED; SETDIST_POS_LE; FRONTIER_EQ_EMPTY] THEN
    REWRITE_TAC[SET_RULE `UNIV DIFF s = {} <=> s = UNIV`; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_BOUNDED_UNIV]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[NOT_MEASURABLE_UNIV]; ASM SET_TAC[]];

    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `u < e ==> t - s <= u ==> t < s + e`)) THEN
    TRANS_TAC REAL_LE_TRANS `measure(t DIFF s:real^N->bool)` THEN
    ASM_SIMP_TAC[MEASURE_SUB_LE_MEASURE_DIFF; MEASURABLE_JORDAN;
                 NEGLIGIBLE_EQ_MEASURE_0] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_JORDAN; MEASURABLE_DIFF;
                 NEGLIGIBLE_EQ_MEASURE_0] THEN
    REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`segment[x:real^N,y]`; `s:real^N->bool`]
        CONNECTED_INTER_FRONTIER) THEN REWRITE_TAC[CONNECTED_SEGMENT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN ANTS_TAC THENL
     [CONJ_TAC THENL [EXISTS_TAC `y:real^N`; EXISTS_TAC `x:real^N`] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `dist(x:real^N,z) < setdist(frontier s,(:real^N) DIFF u)`
    MP_TAC THENL
     [ASM_MESON_TAC[REAL_LET_TRANS; DIST_IN_CLOSED_SEGMENT; DIST_SYM];
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[REAL_NOT_LT] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      MATCH_MP_TAC SETDIST_LE_DIST THEN ASM SET_TAC[]]]);;

let MEASURE_SEMICONTINUOUS_WITH_HAUSDIST_BOUND = prove
 (`!s s' r e a:real^N.
        bounded s /\ convex s /\ ball(a,r) SUBSET s /\ &0 < r /\
        bounded s' /\ measurable s' /\ hausdist(s,s') <= e * r /\ &0 < e
        ==> measure(s') <= measure(s) * (&1 + e) pow dimindex(:N)`,
  REPEAT GEN_TAC THEN GEOM_ORIGIN_TAC `a:real^N` THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s':real^N->bool`; `closure s:real^N->bool`]
        HAUSDIST_COMPACT_SUMS) THEN
  ASM_REWRITE_TAC[HAUSDIST_CLOSURE; COMPACT_CLOSURE; CLOSURE_EQ_EMPTY] THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[REAL_NOT_LE; BALL_EQ_EMPTY; SUBSET_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
   (REWRITE_RULE[CONJ_ASSOC] MEASURE_SUBSET))) THEN
  ASM_SIMP_TAC[MEASURABLE_COMPACT; COMPACT_SUMS; COMPACT_CLOSURE;
               COMPACT_CBALL] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  TRANS_TAC REAL_LE_TRANS
   `measure {&1 % y + e % z:real^N | y IN closure s /\ z IN closure s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_COMPACT; COMPACT_SUMS; COMPACT_CLOSURE;
               COMPACT_CBALL] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE
       `{a % x + b % y:real^N | x IN s /\ y IN t} =
        {x + y | x IN IMAGE (\x. a % x) s /\ y IN IMAGE (\x. b % x) t}`] THEN
      ASM_SIMP_TAC[MEASURABLE_COMPACT; COMPACT_SUMS; COMPACT_CLOSURE;
                   COMPACT_CBALL; COMPACT_SCALING];
      REWRITE_TAC[VECTOR_MUL_LID] THEN MATCH_MP_TAC(SET_RULE
       `t SUBSET IMAGE (\x. e % x) u
        ==> {y + z:real^N | y IN s /\ z IN t} SUBSET
            {y + e % z | y IN s /\ z IN u}`) THEN
      TRANS_TAC SUBSET_TRANS `IMAGE (\x:real^N. e % x) (cball(vec 0,r))` THEN
      CONJ_TAC THENL
       [ASM_SIMP_TAC[GSYM CBALL_SCALING; VECTOR_MUL_RZERO] THEN
        MATCH_MP_TAC SUBSET_CBALL THEN ASM_MESON_TAC[HAUSDIST_SYM];
        MATCH_MP_TAC IMAGE_SUBSET THEN
        ASM_SIMP_TAC[GSYM CLOSURE_BALL; SUBSET_CLOSURE]]];
    ASM_SIMP_TAC[CONVEX_SUMS_MULTIPLES; REAL_POS; REAL_LT_IMP_LE;
                 CONVEX_CLOSURE] THEN
    ASM_SIMP_TAC[MEASURE_SCALING; COMPACT_CLOSURE; MEASURABLE_COMPACT] THEN
    ASM_SIMP_TAC[MEASURE_CLOSURE; NEGLIGIBLE_CONVEX_FRONTIER] THEN
    MATCH_MP_TAC(REAL_ARITH `y * x = a ==> x * y <= a`) THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Steinhaus's theorem. (Stromberg's proof as given on Wikipedia.)           *)
(* ------------------------------------------------------------------------- *)

let STEINHAUS = prove
 (`!s:real^N->bool.
        measurable s /\ &0 < measure s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_INNER_COMPACT) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `measure(s:real^N->bool) / &3`]
    MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < x / &3 <=> &0 < x`] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^N) DIFF u`]
    SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_BALL_0; IN_ELIM_THM] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((IMAGE (\x:real^N. v + x) k) INTER k = {})` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (\x:real^N. v + x) k`; `k:real^N->bool`]
        MEASURE_UNION) THEN
    ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ; MEASURE_EMPTY] THEN
    REWRITE_TAC[MEASURE_TRANSLATION; REAL_SUB_RZERO] THEN
    MATCH_MP_TAC(REAL_ARITH
     `!s:real^N->bool u:real^N->bool.
        measure u < measure s + measure s / &3 /\
        measure s < measure k + measure s / &3 /\
        measure x <= measure u
        ==> ~(measure x = measure k + measure k)`) THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_UNION] THEN
    ASM_REWRITE_TAC[UNION_SUBSET] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `v + x:real^N`]) THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; NORM_ARITH
     `d <= dist(x:real^N,v + x) <=> ~(norm v < d)`];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    REWRITE_TAC[VECTOR_ARITH `v:real^N = x - y <=> x = v + y`] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A measurable set with cardinality less than c is negligible.              *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_NONNEGLIGIBLE_IMP_LARGE = prove
 (`!s:real^N->bool. measurable s /\ &0 < measure s ==> s =_c (:real)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `FINITE(s:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_FINITE; MEASURABLE_MEASURE_POS_LT];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP STEINHAUS) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[GSYM CARD_LE_ANTISYM] THEN CONJ_TAC THENL
   [TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN
    REWRITE_TAC[CARD_LE_UNIV] THEN MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    REWRITE_TAC[CARD_EQ_EUCLIDEAN];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `(:real^N)` THEN CONJ_TAC THENL
   [MESON_TAC[CARD_EQ_EUCLIDEAN; CARD_EQ_SYM; CARD_EQ_IMP_LE]; ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `interval(vec 0:real^N,vec 1)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN ONCE_REWRITE_TAC[CARD_EQ_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CARD_EQ THEN
    MATCH_MP_TAC HOMEOMORPHIC_OPEN_INTERVAL_UNIV THEN
    REWRITE_TAC[UNIT_INTERVAL_NONEMPTY];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `interval[vec 0:real^N,vec 1]` THEN
  SIMP_TAC[INTERVAL_OPEN_SUBSET_CLOSED; CARD_LE_SUBSET] THEN
  TRANS_TAC CARD_LE_TRANS `cball(vec 0:real^N,d / &2)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_EQ_IMP_LE THEN
    MATCH_MP_TAC HOMEOMORPHIC_IMP_CARD_EQ THEN
    MATCH_MP_TAC HOMEOMORPHIC_CONVEX_COMPACT THEN
    REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; INTERIOR_CLOSED_INTERVAL;
                CONVEX_CBALL; COMPACT_CBALL; UNIT_INTERVAL_NONEMPTY;
                INTERIOR_CBALL; BALL_EQ_EMPTY] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `ball(vec 0:real^N,d)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_LE_SUBSET THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_CBALL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `IMAGE (\(x:real^N,y). x - y) (s *_c s)` THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[mul_c; CARD_LE_SUBSET; SET_RULE
     `IMAGE f {g x y | P x /\ Q y} = {f(g x y) | P x /\ Q y}`];
    ALL_TAC] THEN
  TRANS_TAC CARD_LE_TRANS `((s:real^N->bool) *_c s)` THEN
  REWRITE_TAC[CARD_LE_IMAGE] THEN
  MATCH_MP_TAC CARD_EQ_IMP_LE THEN MATCH_MP_TAC CARD_SQUARE_INFINITE THEN
  ASM_REWRITE_TAC[INFINITE]);;

let MEASURABLE_SMALL_IMP_NEGLIGIBLE = prove
 (`!s:real^N->bool. measurable s /\ s <_c (:real) ==> negligible s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `a /\ b ==> c <=> a ==> ~c ==> ~b`] THEN
  SIMP_TAC[GSYM MEASURABLE_MEASURE_POS_LT] THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_NONNEGLIGIBLE_IMP_LARGE) THEN
  REWRITE_TAC[lt_c] THEN MESON_TAC[CARD_EQ_IMP_LE; CARD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Austin's Lemma.                                                           *)
(* ------------------------------------------------------------------------- *)

let AUSTIN_LEMMA = prove
 (`!D. FINITE D /\
       (!d. d IN D
            ==> ?k a b. d = interval[a:real^N,b] /\
                        (!i. 1 <= i /\ i <= dimindex(:N) ==> b$i - a$i = k))
       ==> ?D'. D' SUBSET D /\ pairwise DISJOINT D' /\
                measure(UNIONS D') >=
                measure(UNIONS D) / &3 pow (dimindex(:N))`,
  GEN_TAC THEN WF_INDUCT_TAC `CARD(D:(real^N->bool)->bool)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "*")) THEN
  ASM_CASES_TAC `D:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[SUBSET_EMPTY; UNWIND_THM2; PAIRWISE_EMPTY] THEN
    REWRITE_TAC[UNIONS_0; real_ge; MEASURE_EMPTY; NOT_IN_EMPTY] THEN
    REWRITE_TAC[REAL_ARITH `&0 / x = &0`; REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d:real^N->bool. d IN D /\ !d'. d' IN D ==> measure d' <= measure d`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE measure (D:(real^N->bool)->bool)` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
    `{c:real^N->bool | c IN (D DELETE d) /\ c INTER d = {}}`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC CARD_PSUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_DELETE; FINITE_RESTRICT; IN_ELIM_THM; real_ge] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[IN_DELETE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `D':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(d:real^N->bool) INSERT D'` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
    REWRITE_TAC[pairwise; IN_INSERT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a3 b3:real^N.
        measure(interval[a3,b3]) = &3 pow dimindex(:N) * measure d /\
        !c. c IN D /\ ~(c INTER d = {}) ==> c SUBSET interval[a3,b3]`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "*" (MP_TAC o SPEC `d:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:real`; `a:real^N`; `b:real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
    EXISTS_TAC `inv(&2) % (a + b) - &3 / &2 % (b - a):real^N` THEN
    EXISTS_TAC `inv(&2) % (a + b) + &3 / &2 % (b - a):real^N` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH `(x + &3 / &2 * a) - (x - &3 / &2 * a) = &3 * a`;
                  REAL_ARITH `x - a <= x + a <=> &0 <= a`] THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 <= &3 / &2 * x - &0 <=> &0 <= x`] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN
      SIMP_TAC[PRODUCT_CONST; FINITE_NUMSEG; CARD_NUMSEG_1; REAL_POW_MUL];
      X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
      REMOVE_THEN "*" (MP_TAC o SPEC `c:real^N->bool`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`k':real`; `a':real^N`; `b':real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE RAND_CONV [DISJOINT_INTERVAL]) THEN
      REWRITE_TAC[NOT_EXISTS_THM; SUBSET_INTERVAL] THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `1 <= i` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `interval[a':real^N,b']`) THEN
      ASM_REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_ARITH `a$k <= b$k <=> &0 <= b$k - a$k`] THEN
      ASM_SIMP_TAC[IN_NUMSEG] THEN
      ASM_CASES_TAC `&0 <= k` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `&0 <= k'` THEN ASM_REWRITE_TAC[] THEN
      REPEAT(FIRST_X_ASSUM(fun th ->
        SIMP_TAC[th] THEN MP_TAC(ISPEC `i:num` th))) THEN
      ASM_SIMP_TAC[PRODUCT_CONST; CARD_NUMSEG_1; FINITE_NUMSEG] THEN
      DISCH_TAC THEN DISCH_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP
       (REWRITE_RULE[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`]
        REAL_POW_LE2_REV)) THEN
      ASM_SIMP_TAC[DIMINDEX_GE_1; LE_1] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT] THEN
  SUBGOAL_THEN `!d:real^N->bool. d IN D ==> measurable d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_DISJOINT_UNION o
    rand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
      FINITE_SUBSET)) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_DELETE];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(interval[a3:real^N,b3]) +
              measure(UNIONS D DIFF interval[a3,b3])` THEN
  CONJ_TAC THENL
   [W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNION o
      rand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MEASURABLE_UNIONS; MEASURABLE_DIFF;
                   MEASURABLE_INTERVAL] THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_UNIONS];
        ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_DIFF;
                     MEASURABLE_INTERVAL; MEASURABLE_UNION];
        SET_TAC[]]];
    ASM_REWRITE_TAC[REAL_ARITH `a * x + y <= (x + z) * a <=> y <= z * a`] THEN
    ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `y <= a ==> x <= y ==> x <= a`)) THEN
    SIMP_TAC[REAL_LE_DIV2_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNIONS; MEASURABLE_INTERVAL;
                 IN_ELIM_THM; IN_DELETE; FINITE_DELETE; FINITE_RESTRICT] THEN
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some differentiability-like properties of the indefinite integral.        *)
(* The first two proofs are minor variants of each other, but it was more    *)
(* work to derive one from the other.                                        *)
(* ------------------------------------------------------------------------- *)

let INTEGRABLE_CCONTINUOUS_EXPLICIT = prove
 (`!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                           ==> norm(inv(content(interval[x,x + h % vec 1])) %
                                    integral (interval[x,x + h % vec 1]) f -
                                    f(x)) < e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_UNIV] THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x:real^M,x + h % vec 1]`;
    `box2 = \h x. interval[x:real^M - h % vec 1,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  SUBGOAL_THEN
   `?k. negligible k /\
        !x e. ~(x IN k) /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e`
  MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[]] THEN
  EXISTS_TAC
   `{x | ~(!e. &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e)}` THEN
  SIMP_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x | !d. &0 < d
                     ==> ?h. &0 < h /\ h < d /\
                             inv(&k + &1) <= dist(i h x,(f:real^M->real^N) x)}
            |  k IN (:num)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^M`; `e:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&k)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `jj:num` THEN
  SUBGOAL_THEN `&0 < inv(&jj + &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    SPEC_TAC(`inv(&jj + &1)`,`mu:real`) THEN GEN_TAC THEN DISCH_TAC] THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  ASM_CASES_TAC `negligible(interval[a:real^M,b])` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a - vec 1:real^M`; `b + vec 1:real^M`]
    HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(e * mu) / &2 / &6 pow (dimindex(:M))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL;
               REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE `{x | P x} INTER s = {x | x IN s /\ P x}`] THEN
  ABBREV_TAC
    `E = {x | x IN interval[a,b] /\
              !d. &0 < d
                   ==> ?h. &0 < h /\ h < d /\
                           mu <= dist(i h x,(f:real^M->real^N) x)}` THEN
  SUBGOAL_THEN
   `!x. x IN E
        ==> ?h. &0 < h /\
                (box h x:real^M->bool) SUBSET (g x) /\
                (box h x:real^M->bool) SUBSET interval[a - vec 1,b + vec 1] /\
                mu <= dist(i h x,(f:real^M->real^N) x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `min (&1) (d / &(dimindex(:M)))`)) THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; DIMINDEX_GE_1; LE_1; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "box" THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL] THEN
      X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs((x - y:real^M)$i))` THEN
      REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; IN_NUMSEG] THEN
      SIMP_TAC[NOT_LT; DIMINDEX_GE_1; CARD_NUMSEG_1; VECTOR_SUB_COMPONENT] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(x:real^M) IN interval[a,b]` THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `y:real^M` THEN MP_TAC th) THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uv:real^M->real` THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`; `E:real^M->bool`;
                 `\x:real^M. if x IN E then ball(x,uv x) else g(x)`]
   COVERING_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[gauge] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `D:(real^M->bool)->bool`) THEN
  EXISTS_TAC `UNIONS D:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `measurable(UNIONS D:real^M->bool) /\
    measure(UNIONS D) <= measure(interval[a:real^M,b])`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?d. d SUBSET D /\ FINITE d /\
        measure(UNIONS D:real^M->bool) <= &2 * measure(UNIONS d)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `measure(UNIONS D:real^M->bool) = &0` THENL
     [EXISTS_TAC `{}:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; MEASURE_EMPTY; UNIONS_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(ISPECL [`D:(real^M->bool)->bool`; `measure(interval[a:real^M,b])`;
                     `measure(UNIONS D:real^M->bool) / &2`]
                MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_MEASURE_POS_LT; REAL_HALF] THEN
        ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
          [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_UNIONS];
           ALL_TAC]) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[IN_INTER] THEN REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_TAC `tag:(real^M->bool)->real^M`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `D <= &2 * d ==> d <= e / &2 ==> D <= e`)) THEN
  MP_TAC(ISPEC
   `IMAGE (\k:real^M->bool. (box2:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) d`
   AUSTIN_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN EXPAND_TAC "box2" THEN
    EXISTS_TAC `&2 * uv((tag:(real^M->bool)->real^M) k):real` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k - uv(tag k) % vec 1:real^M` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k + uv(tag k) % vec 1:real^M` THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE; real_ge] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= d' /\ p <= e ==> d' <= p ==> d <= e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      EXPAND_TAC "box2" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `z:real^M` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^M) IN k` THEN SPEC_TAC(`z:real^M`,`z:real^M`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(tag k:real^M,uv(tag(k:real^M->bool)))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "box2" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL] THEN
      X_GEN_TAC `z:real^M` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN

      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `measure(UNIONS (IMAGE (\k:real^M->bool.
                            (box:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) p)) *
              &6 pow dimindex (:M)` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `!box. IMAGE (\k:real^M->bool. (box:real->real^M->real^M->bool)
                                    (uv(tag k):real) ((tag k:real^M))) p =
             IMAGE (\t. box (uv t) t) (IMAGE tag p)`
     (fun th -> REWRITE_TAC[th])
    THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o rand o snd) THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_NEGLIGIBLE_UNIONS_IMAGE o
        lhand o lhand o rand o snd) THEN
    MATCH_MP_TAC(TAUT
     `fp /\ (mb /\ mb') /\ (db /\ db') /\ (m1 /\ m2 ==> p)
      ==> (fp /\ mb /\ db ==> m1) ==> (fp /\ mb' /\ db' ==> m2) ==> p`) THEN
    SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ASM_SIMP_TAC[FINITE_IMAGE]] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
      REWRITE_TAC[MEASURABLE_INTERVAL];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      REWRITE_TAC[IMP_IMP; RIGHT_IMP_FORALL_THM; AND_FORALL_THM] THEN
      MAP_EVERY X_GEN_TAC [`k1:real^M->bool`; `k2:real^M->bool`] THEN
      MATCH_MP_TAC(TAUT
        `(q ==> r) /\ (p ==> q) ==> (p ==> q) /\ (p ==> r)`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
        MATCH_MP_TAC(SET_RULE
        `s SUBSET s' /\ t SUBSET t' ==> (s INTER t) SUBSET (s' INTER t')`) THEN
        CONJ_TAC THEN MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `s = {} ==> negligible s`) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `k1:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k2:real^M->bool`) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box2" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
    REWRITE_TAC[GSYM SUM_RMUL] THEN
    MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
    X_GEN_TAC `t:real^M` THEN DISCH_THEN(K ALL_TAC) THEN
    SUBST1_TAC(REAL_ARITH `&6 = &2 * &3`) THEN
    REWRITE_TAC[REAL_POW_MUL; REAL_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    REWRITE_TAC[REAL_ARITH `a <= a + x <=> &0 <= x`;
                REAL_ARITH `a - x <= a + x <=> &0 <= x`] THEN
    COND_CASES_TAC THEN REWRITE_TAC[REAL_MUL_LZERO] THEN
    REWRITE_TAC[REAL_ARITH `(t + h) - (t - h):real = &2 * h`;
                REAL_ARITH `(t + h) - t:real = h`] THEN
    REWRITE_TAC[PRODUCT_MUL_NUMSEG; PRODUCT_CONST_NUMSEG] THEN
    REWRITE_TAC[ADD_SUB; REAL_MUL_AC];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\k. (tag:(real^M->bool)->real^M) k,
                (box(uv(tag k):real) (tag k):real^M->bool)) p`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[tagged_partial_division_of; fine] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    REWRITE_TAC[MESON[]
     `(!x j. (?k. (x = tag k /\ j = g k) /\ k IN d) ==> P x j) <=>
      (!k. k IN d ==> P (tag k) (g k))`] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[IN_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < u ==> x <= x /\ x <= x + u`) THEN ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[SUBSET];
        EXPAND_TAC "box" THEN MESON_TAC[]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k1:real^M->bool` THEN
      ASM_CASES_TAC `(k1:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k2:real^M->bool` THEN
      ASM_CASES_TAC `(k2:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(tag:(real^M->bool)->real^M) k1 = tag k2` THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box2" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE
         `i1 SUBSET s1 /\ i2 SUBSET s2
          ==> DISJOINT s1 s2 ==> i1 INTER i2 = {}`) THEN
        CONJ_TAC THEN MATCH_MP_TAC(MESON[INTERIOR_SUBSET; SUBSET_TRANS]
         `s SUBSET t ==> interior s SUBSET t`) THEN
        MAP_EVERY EXPAND_TAC ["box"; "box2"] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `e = e' /\ y <= x ==> x < e ==> y <= e'`) THEN
  CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a' <= e ==> a <= a' ==> a <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; RIGHT_EXISTS_AND_THM; FINITE_IMAGE] THEN
  REWRITE_TAC[NORM_POS_LE; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `SND:real^M#(real^M->bool)->real^M->bool` THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 < uv(tag(k:real^M->bool):real^M):real` ASSUME_TAC
  THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real) (tag k):real^M->bool)`
  MP_TAC THENL
   [EXPAND_TAC "box" THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> a <= a + x`] THEN
    MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
    REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  DISCH_THEN(fun th ->
   GEN_REWRITE_TAC (funpow 2 RAND_CONV)
    [MATCH_MP(REAL_ARITH `&0 < x ==> x = abs x`) th] THEN
   ASSUME_TAC th) THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM NORM_MUL] THEN
  SUBGOAL_THEN
   `mu <= dist(i (uv(tag(k:real^M->bool):real^M):real) (tag k):real^N,
               f(tag k))`
  MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> m <= x ==> m <= y`) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN EXPAND_TAC "i" THEN
  REWRITE_TAC[dist; VECTOR_SUB_LDISTRIB] THEN
  UNDISCH_TAC
    `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real)
                (tag k):real^M->bool)` THEN
  EXPAND_TAC "box" THEN REWRITE_TAC[MEASURE_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

let INTEGRABLE_CCONTINUOUS_EXPLICIT_SYMMETRIC = prove
 (`!f:real^M->real^N.
    (!a b. f integrable_on interval[a,b])
    ==> ?k. negligible k /\
         !x e. ~(x IN k) /\ &0 < e
               ==> ?d. &0 < d /\
                       !h. &0 < h /\ h < d
                ==> norm(inv(content(interval[x - h % vec 1,x + h % vec 1])) %
                    integral (interval[x - h % vec 1,x + h % vec 1]) f -
                    f(x)) < e`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x - h % vec 1:real^M,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  SUBGOAL_THEN
   `?k. negligible k /\
        !x e. ~(x IN k) /\ &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e`
  MP_TAC THENL
   [ALL_TAC; MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[]] THEN
  EXISTS_TAC
   `{x | ~(!e. &0 < e
              ==> ?d. &0 < d /\
                      !h. &0 < h /\ h < d
                          ==> norm(i h x - (f:real^M->real^N) x) < e)}` THEN
  SIMP_TAC[IN_ELIM_THM] THEN
  REWRITE_TAC[LIM_SEQUENTIALLY] THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC
   `UNIONS {{x | !d. &0 < d
                     ==> ?h. &0 < h /\ h < d /\
                             inv(&k + &1) <= dist(i h x,(f:real^M->real^N) x)}
            |  k IN (:num)}` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`y:real^M`; `e:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[SIMPLE_IMAGE; UNIONS_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    X_GEN_TAC `d:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `d:real`) THEN
    ASM_REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[dist] THEN
    MATCH_MP_TAC (REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `inv(&k)` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `jj:num` THEN
  SUBGOAL_THEN `&0 < inv(&jj + &1)` MP_TAC THENL
   [REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    SPEC_TAC(`inv(&jj + &1)`,`mu:real`) THEN GEN_TAC THEN DISCH_TAC] THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  ASM_CASES_TAC `negligible(interval[a:real^M,b])` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_INTERVAL]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `a - vec 1:real^M`; `b + vec 1:real^M`]
    HENSTOCK_LEMMA) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[INTEGRABLE_ON_SUBINTERVAL; SUBSET_UNIV]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(e * mu) / &2 / &3 pow (dimindex(:M))`) THEN
  ASM_SIMP_TAC[REAL_HALF; REAL_LT_DIV; REAL_LT_MUL;
               REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^M->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE `{x | P x} INTER s = {x | x IN s /\ P x}`] THEN
  ABBREV_TAC
    `E = {x | x IN interval[a,b] /\
              !d. &0 < d
                   ==> ?h. &0 < h /\ h < d /\
                           mu <= dist(i h x,(f:real^M->real^N) x)}` THEN
  SUBGOAL_THEN
   `!x. x IN E
        ==> ?h. &0 < h /\
                (box h x:real^M->bool) SUBSET (g x) /\
                (box h x:real^M->bool) SUBSET interval[a - vec 1,b + vec 1] /\
                mu <= dist(i h x,(f:real^M->real^N) x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [gauge]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC o SPEC `x:real^M`) THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC `min (&1) (d / &(dimindex(:M)))`)) THEN
    REWRITE_TAC[REAL_LT_MIN; REAL_LT_01; GSYM CONJ_ASSOC] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; DIMINDEX_GE_1; LE_1; REAL_OF_NUM_LT] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(x:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "box" THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL] THEN
      X_GEN_TAC `y:real^M` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `sum(1..dimindex(:M)) (\i. abs((x - y:real^M)$i))` THEN
      REWRITE_TAC[NORM_LE_L1] THEN MATCH_MP_TAC SUM_BOUND_LT_GEN THEN
      REWRITE_TAC[FINITE_NUMSEG; NUMSEG_EMPTY; IN_NUMSEG] THEN
      SIMP_TAC[NOT_LT; DIMINDEX_GE_1; CARD_NUMSEG_1; VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[REAL_LET_TRANS];
      UNDISCH_TAC `(x:real^M) IN interval[a,b]` THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_INTERVAL] THEN
      DISCH_THEN(fun th -> X_GEN_TAC `y:real^M` THEN MP_TAC th) THEN
      REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `i:num` THEN
      DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `uv:real^M->real` THEN
  REWRITE_TAC[TAUT `(a ==> b /\ c) <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M`; `b:real^M`; `E:real^M->bool`;
                 `\x:real^M. if x IN E then ball(x,uv x) else g(x)`]
   COVERING_LEMMA) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTERVAL_NE_EMPTY] THEN CONJ_TAC THENL
     [EXPAND_TAC "E" THEN SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[gauge] THEN GEN_TAC THEN
    COND_CASES_TAC THEN ASM_SIMP_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[gauge]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `D:(real^M->bool)->bool`) THEN
  EXISTS_TAC `UNIONS D:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `measurable(UNIONS D:real^M->bool) /\
    measure(UNIONS D) <= measure(interval[a:real^M,b])`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC MEASURABLE_UNIONS THEN
    ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `?d. d SUBSET D /\ FINITE d /\
        measure(UNIONS D:real^M->bool) <= &2 * measure(UNIONS d)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `measure(UNIONS D:real^M->bool) = &0` THENL
     [EXISTS_TAC `{}:(real^M->bool)->bool` THEN
      ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; MEASURE_EMPTY; UNIONS_0] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      MP_TAC(ISPECL [`D:(real^M->bool)->bool`; `measure(interval[a:real^M,b])`;
                     `measure(UNIONS D:real^M->bool) / &2`]
                MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [ASM_SIMP_TAC[MEASURABLE_MEASURE_POS_LT; REAL_HALF] THEN
        ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURABLE_INTERVAL]; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
          [ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL; MEASURABLE_UNIONS];
           ALL_TAC]) THEN
        ASM SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[] THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o el 3 o CONJUNCTS) THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b <=> ~(a ==> ~b)`] THEN
  SIMP_TAC[IN_INTER] THEN REWRITE_TAC[NOT_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_THEN(X_CHOOSE_TAC `tag:(real^M->bool)->real^M`) THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `D <= &2 * d ==> d <= e / &2 ==> D <= e`)) THEN
  MP_TAC(ISPEC
   `IMAGE (\k:real^M->bool. (box:real->real^M->real^M->bool)
                            (uv(tag k):real) ((tag k:real^M))) d`
   AUSTIN_LEMMA) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN EXPAND_TAC "box" THEN
    EXISTS_TAC `&2 * uv((tag:(real^M->bool)->real^M) k):real` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k - uv(tag k) % vec 1:real^M` THEN
    EXISTS_TAC `(tag:(real^M->bool)->real^M) k + uv(tag k) % vec 1:real^M` THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_SUBSET_IMAGE; real_ge] THEN
  SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^M->bool)->bool` MP_TAC) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MATCH_MP_TAC(REAL_ARITH
   `d <= d' /\ p <= e ==> d' <= p ==> d <= e`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      X_GEN_TAC `z:real^M` THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^M) IN k` THEN SPEC_TAC(`z:real^M`,`z:real^M`) THEN
      REWRITE_TAC[GSYM SUBSET] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `ball(tag k:real^M,uv(tag(k:real^M->bool)))` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      EXPAND_TAC "box" THEN REWRITE_TAC[SUBSET; IN_BALL; IN_INTERVAL] THEN
      X_GEN_TAC `z:real^M` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      SIMP_TAC[REAL_ARITH `x - h <= y /\ y <= x + h <=> abs(x - y) <= h`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; REAL_LE_TRANS]];
    ALL_TAC] THEN
  SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH] THEN
  SUBGOAL_THEN `FINITE(p:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
  EXISTS_TAC `mu:real` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `IMAGE (\k. (tag:(real^M->bool)->real^M) k,
                (box(uv(tag k):real) (tag k):real^M->bool)) p`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[tagged_partial_division_of; fine] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[IN_IMAGE; PAIR_EQ] THEN
    REWRITE_TAC[MESON[]
     `(!x j. (?k. (x = tag k /\ j = g k) /\ k IN d) ==> P x j) <=>
      (!k. k IN d ==> P (tag k) (g k))`] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[IN_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 < u ==> x - u <= x /\ x <= x + u`) THEN ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[SUBSET];
        EXPAND_TAC "box" THEN MESON_TAC[]];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pairwise]) THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k1:real^M->bool` THEN
      ASM_CASES_TAC `(k1:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k2:real^M->bool` THEN
      ASM_CASES_TAC `(k2:real^M->bool) IN p` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(tag:(real^M->bool)->real^M) k1 = tag k2` THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "box" THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
        REWRITE_TAC[SUBSET_INTERVAL] THEN
        REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
        REWRITE_TAC[REAL_ARITH `x - e <= x + e <=> &0 <= e`] THEN
        SUBGOAL_THEN `&0 <= uv((tag:(real^M->bool)->real^M) k1) /\
                      &0 <= uv((tag:(real^M->bool)->real^M) k2)`
        STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[SUBSET; REAL_LT_IMP_LE]; ASM_REWRITE_TAC[]] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [CART_EQ]) THEN
        MATCH_MP_TAC MONO_NOT THEN REWRITE_TAC[AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE
         `i1 SUBSET s1 /\ i2 SUBSET s2
          ==> DISJOINT s1 s2 ==> i1 INTER i2 = {}`) THEN
        REWRITE_TAC[INTERIOR_SUBSET]];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `e = e' /\ y <= x ==> x < e ==> y <= e'`) THEN
  CONJ_TAC THENL [REWRITE_TAC[real_div; REAL_MUL_AC]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "box" THEN REWRITE_TAC[MEASURABLE_INTERVAL];
    ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `a' <= e ==> a <= a' ==> a <= e`) THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
  MATCH_MP_TAC SUM_LE_INCLUDED THEN
  ASM_SIMP_TAC[FORALL_IN_IMAGE; RIGHT_EXISTS_AND_THM; FINITE_IMAGE] THEN
  REWRITE_TAC[NORM_POS_LE; EXISTS_IN_IMAGE] THEN
  EXISTS_TAC `SND:real^M#(real^M->bool)->real^M->bool` THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&0 < uv(tag(k:real^M->bool):real^M):real` ASSUME_TAC
  THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real) (tag
k):real^M->bool)`
  MP_TAC THENL
   [EXPAND_TAC "box" THEN
    REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                   VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> a - x <= a + x`] THEN
    MATCH_MP_TAC PRODUCT_POS_LT_NUMSEG THEN
    REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
  DISCH_THEN(fun th ->
   GEN_REWRITE_TAC (funpow 2 RAND_CONV)
    [MATCH_MP(REAL_ARITH `&0 < x ==> x = abs x`) th] THEN
   ASSUME_TAC th) THEN
  REWRITE_TAC[real_div; GSYM REAL_ABS_INV] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM NORM_MUL] THEN
  SUBGOAL_THEN
   `mu <= dist(i (uv(tag(k:real^M->bool):real^M):real) (tag k):real^N,
               f(tag k))`
  MP_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(REAL_ARITH `x = y ==> m <= x ==> m <= y`) THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN EXPAND_TAC "i" THEN
  REWRITE_TAC[dist; VECTOR_SUB_LDISTRIB] THEN
  UNDISCH_TAC
    `&0 < measure(box(uv(tag(k:real^M->bool):real^M):real)
                (tag k):real^M->bool)` THEN
  EXPAND_TAC "box" THEN REWRITE_TAC[MEASURE_INTERVAL] THEN
  SIMP_TAC[VECTOR_MUL_ASSOC; REAL_LT_IMP_NZ; REAL_MUL_LINV] THEN
  REWRITE_TAC[VECTOR_MUL_LID]);;

let HAS_VECTOR_DERIVATIVE_INDEFINITE_INTEGRAL = prove
 (`!f:real^1->real^N a b.
        f integrable_on interval[a,b]
        ==> ?k. negligible k /\
                !x. x IN interval[a,b] DIFF k
                    ==> ((\x. integral(interval[a,x]) f) has_vector_derivative
                         f(x)) (at x within interval[a,b])`,
  SUBGOAL_THEN
   `!f:real^1->real^N a b.
        f integrable_on interval[a,b]
        ==> ?k. negligible k /\
                !x e. x IN interval[a,b] DIFF k /\ & 0 < e
                      ==> ?d. &0 < d /\
                              !x'. x' IN interval[a,b] /\
                                   drop x < drop x' /\ drop x' < drop x + d
                                   ==> norm(integral(interval[x,x']) f -
                                            drop(x' - x) % f x) /
                                       norm(x' - x) < e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MP_TAC(ISPEC
     `(\x. if x IN interval[a,b] then f x else vec 0):real^1->real^N`
     INTEGRABLE_CCONTINUOUS_EXPLICIT) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `(:real^1)` THEN
      ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; SUBSET_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^1->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `e:real`] THEN
    REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^1`; `e:real`]) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `drop y - drop x`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `x + (drop y - drop x) % vec 1 = y` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_VEC] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[CONTENT_1; REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ; NORM_POS_LT; VECTOR_SUB_EQ;
                 GSYM DROP_EQ; REAL_LT_IMP_NE] THEN
    SUBGOAL_THEN `norm(y - x) = abs(drop y - drop x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB]; ALL_TAC] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM NORM_MUL)] THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_FIELD `x < y ==> (y - x) * inv(y - x) = &1`] THEN
    AP_TERM_TAC THEN REWRITE_TAC[DROP_SUB; VECTOR_MUL_LID] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_EQ THEN
    X_GEN_TAC `z:real^1` THEN REWRITE_TAC[DIFF_EMPTY] THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPECL [`f:real^1->real^N`; `a:real^1`; `b:real^1`] th) THEN
    MP_TAC(ISPECL [`\x. (f:real^1->real^N) (--x)`; `--b:real^1`;
                   `--a:real^1`] th)) THEN
  ASM_REWRITE_TAC[INTEGRABLE_REFLECT] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^1->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  EXISTS_TAC `k1 UNION IMAGE (--) k2:real^1->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[linear] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN
  REWRITE_TAC[IN_IMAGE; VECTOR_ARITH `x:real^1 = --x' <=> --x = x'`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN STRIP_TAC THEN
  REWRITE_TAC[has_vector_derivative; HAS_DERIVATIVE_WITHIN] THEN CONJ_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  REMOVE_THEN "2" (MP_TAC o SPECL [`--x:real^1`; `e:real`]) THEN
  REMOVE_THEN "1" (MP_TAC o SPECL [`x:real^1`; `e:real`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_REFLECT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "1"))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real`
   (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "2"))) THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_INTERVAL_1] THEN
  REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `drop x < drop y \/ drop y < drop x` DISJ_CASES_TAC THENL
   [ASM_REAL_ARITH_TAC;
    REMOVE_THEN "1" (MP_TAC o SPEC `y:real^1`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `c + a:real^N = b ==> a = b - c`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    REMOVE_THEN "2" (MP_TAC o SPEC `--y:real^1`) THEN
    ANTS_TAC THENL [SIMP_TAC[DROP_NEG] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm(--y - --x) = abs(drop y - drop x)` SUBST1_TAC THENL
     [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB; DROP_NEG] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x < e ==> y < e`) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[INTEGRAL_REFLECT] THEN
    REWRITE_TAC[VECTOR_NEG_NEG; DROP_SUB; DROP_NEG] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH
      `x - (--a - --b) % y:real^N = --(--x - (a - b) % y)`] THEN
    REWRITE_TAC[NORM_NEG] THEN AP_TERM_TAC THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(VECTOR_ARITH `b + a = c ==> --a:real^N = b - c`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN
    REPEAT(CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]);;

let ABSOLUTELY_INTEGRABLE_LEBESGUE_POINTS = prove
 (`!f:real^M->real^N.
    (!a b. f absolutely_integrable_on interval[a,b])
    ==> ?k. negligible k /\
            !x e. ~(x IN k) /\ &0 < e
                  ==> ?d. &0 < d /\
                          !h. &0 < h /\ h < d
                             ==> norm(inv(content(interval[x - h % vec 1,
                                                           x + h % vec 1])) %
                                      integral (interval[x - h % vec 1,
                                                         x + h % vec 1])
                                               (\t. lift(norm(f t - f x))))
                                 < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(GEN `r:real^N` (ISPEC `\t. lift(norm((f:real^M->real^N) t - r))`
        INTEGRABLE_CCONTINUOUS_EXPLICIT_SYMMETRIC)) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MONO_FORALL) THEN ANTS_TAC THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
    ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `k:real^N->real^M->bool` THEN STRIP_TAC THEN
  EXISTS_TAC
   `UNIONS (IMAGE (k:real^N->real^M->bool)
           {x | !i. 1 <= i /\ i <= dimindex(:N) ==> rational(x$i)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RATIONAL_COORDINATES] THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `e:real`] THEN
  REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN STRIP_TAC THEN
  MP_TAC(SET_RULE `(f:real^M->real^N) x IN (:real^N)`) THEN
  REWRITE_TAC[GSYM CLOSURE_RATIONAL_COORDINATES] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &3`) THEN
  ASM_REWRITE_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N`; `x:real^M`; `e / &3`]) THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `h:real` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(y1:real^N) < e / &3 /\ norm(i1 - i2) <= e / &3
    ==> norm(i1 - y1) < e / &3 ==> norm(i2) < e`) THEN
  REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[dist; DIST_SYM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC
   `abs(inv(content(interval[x - h % vec 1,x + h % vec 1]))) *
    drop(integral (interval[x - h % vec 1,x + h % vec 1])
                  (\x:real^M. lift(e / &3)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_ABS_POS] THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_SUB o rand o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
      ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      REWRITE_TAC[INTEGRABLE_CONST] THEN CONJ_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN CONJ_TAC THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_CONST];
        X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
        REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM; LIFT_DROP; GSYM LIFT_SUB] THEN
        ASM_MESON_TAC[NORM_ARITH
         `dist(r,x) < e / &3
          ==> abs(norm(y - r:real^N) - norm(y - x)) <= e / &3`]]];
    ASM_CASES_TAC
     `content(interval[x - h % vec 1:real^M,x + h % vec 1]) = &0`
    THENL
     [ASM_REWRITE_TAC[REAL_INV_0; REAL_ABS_NUM; REAL_MUL_LZERO] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[REAL_ABS_INV] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ;
                   GSYM REAL_ABS_NZ] THEN
      REWRITE_TAC[INTEGRAL_CONST; DROP_CMUL; LIFT_DROP] THEN
      SIMP_TAC[real_abs; CONTENT_POS_LE; REAL_MUL_SYM; REAL_LE_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of a function on a set (not necessarily itself measurable). *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("measurable_on",(12,"right"));;

let measurable_on = new_definition
 `(f:real^M->real^N) measurable_on s <=>
        ?k g. negligible k /\
              (!n. (g n) continuous_on (:real^M)) /\
              (!x. ~(x IN k)
                   ==> ((\n. g n x) --> if x IN s then f(x) else vec 0)
                       sequentially)`;;

let MEASURABLE_ON_UNIV = prove
 (`(\x.  if x IN s then f(x) else vec 0) measurable_on (:real^M) <=>
   f measurable_on s`,
  REWRITE_TAC[measurable_on; IN_UNIV; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Lebesgue measurability (like "measurable" but allowing infinite measure)  *)
(* ------------------------------------------------------------------------- *)

let lebesgue_measurable = new_definition
 `lebesgue_measurable s <=> (indicator s) measurable_on (:real^N)`;;

(* ------------------------------------------------------------------------- *)
(* Relation between measurability and integrability.                         *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`,
  let lemma = prove
   (`!f:real^M->real^N g a b.
          f measurable_on (:real^M) /\
          g integrable_on interval[a,b] /\
          (!x. x IN interval[a,b] ==> norm(f x) <= drop(g x))
          ==> f integrable_on interval[a,b]`,
    REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
    REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `h:num->real^M->real^N`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `interval[a:real^M,b] DIFF k` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`h:num->real^M->real^N`; `g:real^M->real^1`] THEN
    ASM_SIMP_TAC[IN_DIFF] THEN REWRITE_TAC[LEFT_AND_FORALL_THM] THEN
    X_GEN_TAC `n:num` THEN
    UNDISCH_TAC `(g:real^M->real^1) integrable_on interval [a,b]` THEN
    SUBGOAL_THEN
     `(h:num->real^M->real^N) n absolutely_integrable_on interval[a,b]`
    MP_TAC THENL
     [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_CONTINUOUS THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[IMP_IMP; absolutely_integrable_on; GSYM CONJ_ASSOC] THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
      MATCH_MP_TAC INTEGRABLE_SPIKE_SET THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN SET_TAC[]]) in
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_ON_ALL_INTERVALS_INTEGRABLE_BOUND THEN
  EXISTS_TAC `g:real^M->real^1` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
  MATCH_MP_TAC lemma THEN
  EXISTS_TAC `(\x. if x IN s then g x else vec 0):real^M->real^1` THEN
  RULE_ASSUM_TAC(ONCE_REWRITE_RULE[INTEGRABLE_ALT]) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; DROP_VEC; REAL_POS]);;

let MEASURABLE_BOUNDED_AE_BY_INTEGRABLE_IMP_INTEGRABLE = prove
 (`!f:real^M->real^N g s k.
        f measurable_on s /\ g integrable_on s /\ negligible k /\
        (!x. x IN s DIFF k ==> norm(f x) <= drop(g x))
        ==> f integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN EXISTS_TAC
   `\x. if x IN k then lift(norm((f:real^M->real^N) x)) else g x` THEN
  ASM_SIMP_TAC[COND_RAND; IN_DIFF; LIFT_DROP; REAL_LE_REFL; COND_ID] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^1`; `k:real^M->bool`] THEN
  ASM_SIMP_TAC[IN_DIFF]);;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^M->real^N g s.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `g:real^M->real^1`]
    ABSOLUTELY_INTEGRABLE_ABSOLUTELY_INTEGRABLE_BOUND) THEN
  DISCH_THEN MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    ASM_MESON_TAC[REAL_ABS_LE; REAL_LE_TRANS];
    ASM_MESON_TAC[MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE];
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    ASM_REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; GSYM drop] THEN
    ASM_MESON_TAC[NORM_ARITH `norm(x) <= a ==> &0 <= a`]]);;

let INTEGRAL_DROP_LE_MEASURABLE = prove
 (`!f g s:real^N->bool.
        f measurable_on s /\
        g integrable_on s /\
        (!x. x IN s ==> &0 <= drop(f x) /\ drop(f x) <= drop(g x))
        ==> drop(integral s f) <= drop(integral s g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_LE THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `g:real^N->real^1` THEN
  ASM_SIMP_TAC[NORM_REAL; GSYM drop; real_abs]);;

let INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE = prove
 (`!f:real^M->real^N.
        (!a b. f integrable_on interval[a,b]) ==> f measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MAP_EVERY ABBREV_TAC
   [`box = \h x. interval[x:real^M,x + h % vec 1]`;
    `i = \h:real x:real^M. inv(content(box h x)) %
                      integral (box h x) (f:real^M->real^N)`] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  EXISTS_TAC `(\n x. i (inv(&n + &1)) x):num->real^M->real^N` THEN
  REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[continuous_on; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`; `e:real`] THEN
    DISCH_TAC THEN EXPAND_TAC "i" THEN EXPAND_TAC "box" THEN
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `x - &2 % vec 1:real^M`;
      `x + &2 % vec 1:real^M`;
      `x:real^M`;
      `x + inv(&n + &1) % vec 1:real^M`;
      `e * (&1 / (&n + &1)) pow dimindex(:M)`]
     INDEFINITE_INTEGRAL_CONTINUOUS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTERVAL; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
        REAL_MUL_RID; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `&0 <= inv(&n + &1) /\ inv(&n + &1) <= &1` MP_TAC THENL
         [ALL_TAC; REAL_ARITH_TAC] THEN
        ASM_REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH `&0 <= &n + &1`] THEN
        MATCH_MP_TAC REAL_INV_LE_1 THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_POW_LT THEN MATCH_MP_TAC REAL_LT_DIV THEN
        REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min k (&1)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01] THEN
      ASM_REWRITE_TAC[dist] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      REWRITE_TAC[REAL_ARITH `a <= a + x <=> &0 <= x`] THEN
      REWRITE_TAC[REAL_LE_INV_EQ; REAL_ARITH `&0 <= &n + &1`] THEN
      REWRITE_TAC[REAL_ARITH `(x + inv y) - x = &1 / y`] THEN
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; ADD_SUB] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; NORM_MUL] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_POW; REAL_ABS_DIV] THEN
      REWRITE_TAC[REAL_ABS_NUM; REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_DIV; REAL_POW_LT;
                   REAL_ARITH `&0 < &1 /\ &0 < &n + &1`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `(y + i) - (x + i):real^N = y - x`;
                  VECTOR_ARITH `(y - i) - (x - i):real^N = y - x`] THEN
      ASM_SIMP_TAC[IN_INTERVAL; REAL_LT_IMP_LE] THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; dist;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `1 <= i /\ i <= dimindex(:M)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH
       `&0 <= i /\ i <= &1 /\ abs(x - y) <= &1
        ==> (x - &2 <= y /\ y <= x + &2) /\
            (x - &2 <= y + i /\ y + i <= x + &2)`) THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_INV_LE_1;
                   REAL_ARITH `&0 <= &n + &1 /\ &1 <= &n + &1`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
      ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LT_IMP_LE; NORM_SUB;
                    REAL_LE_TRANS]];
    FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_CCONTINUOUS_EXPLICIT) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    ASM_CASES_TAC `negligible(k:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^M` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["i"; "box"] THEN REWRITE_TAC[dist] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let INTEGRABLE_IMP_MEASURABLE = prove
 (`!f:real^M->real^N s.
        f integrable_on s ==> f measurable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_UNIV; GSYM MEASURABLE_ON_UNIV] THEN
  SPEC_TAC(`\x. if x IN s then (f:real^M->real^N) x else vec 0`,
           `f:real^M->real^N`) THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
  REPEAT GEN_TAC THEN MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `(:real^M)` THEN ASM_REWRITE_TAC[SUBSET_UNIV]);;

let ABSOLUTELY_INTEGRABLE_MEASURABLE = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s <=>
        f measurable_on s /\ (\x. lift(norm(f x))) integrable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[absolutely_integrable_on] THEN
  MATCH_MP_TAC(TAUT `(a ==> b) /\ (b /\ c ==> a) ==> (a /\ c <=> b /\ c)`) THEN
  REWRITE_TAC[INTEGRABLE_IMP_MEASURABLE] THEN STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `\x. lift(norm((f:real^M->real^N) x))` THEN
  ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Composing continuous and measurable functions; a few variants.            *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_CONTINUOUS = prove
 (`!f:real^M->real^N g:real^N->real^P.
        f measurable_on (:real^M) /\ g continuous_on (:real^N)
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\n x. (g:real^N->real^P) ((h:num->real^M->real^N) n x)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [CONTINUOUS_ON_SEQUENTIALLY]) THEN
    ASM_SIMP_TAC[o_DEF; IN_UNIV]]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_0 = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        f measurable_on s /\ g continuous_on (:real^N) /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> c ==> a /\ b ==> d`] THEN
  DISCH_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; o_DEF] THEN ASM_MESON_TAC[]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL = prove
 (`!f:real^M->real^N g:real^N->real^P a b.
        f measurable_on (:real^M) /\
        (!x. f(x) IN interval(a,b)) /\
        g continuous_on interval(a,b)
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `(\n x. (g:real^N->real^P)
           (lambda i. max ((a:real^N)$i + (b$i - a$i) / (&n + &2))
                          (min ((h n x:real^N)$i)
                               ((b:real^N)$i - (b$i - a$i) / (&n + &2)))))
    :num->real^M->real^P` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MP_TAC(ISPECL
       [`(:real^M)`;
        `(lambda i. (b:real^N)$i - (b$i - (a:real^N)$i) / (&n + &2)):real^N`]
         CONTINUOUS_ON_CONST) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
      MP_TAC(ISPECL
       [`(:real^M)`;
        `(lambda i. (a:real^N)$i + ((b:real^N)$i - a$i) / (&n + &2)):real^N`]
         CONTINUOUS_ON_CONST) THEN
      REWRITE_TAC[IMP_IMP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `interval(a:real^N,b)` THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o CONJUNCT1) THEN
      SIMP_TAC[IN_INTERVAL; LAMBDA_BETA] THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN
        `&0 < ((b:real^N)$i - (a:real^N)$i) / (&n + &2) /\
         ((b:real^N)$i - (a:real^N)$i) / (&n + &2) <= (b$i - a$i) / &2` MP_TAC
      THENL [ALL_TAC; REAL_ARITH_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_LT_LDIV_EQ;
                   REAL_ARITH `&0 < &n + &2`] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[real_div]] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC]];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[o_DEF] THEN MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\n. (lambda i. ((a:real^N)$i + ((b:real^N)$i - a$i) / (&n + &2))))
       --> a) sequentially /\
      ((\n. (lambda i. ((b:real^N)$i - ((b:real^N)$i - a$i) / (&n + &2))))
       --> b) sequentially`
    MP_TAC THENL
     [ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
      SIMP_TAC[LAMBDA_BETA] THEN
      CONJ_TAC THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      REWRITE_TAC[real_sub] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
      REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC LIM_ADD THEN
      REWRITE_TAC[LIM_CONST; LIFT_NEG; real_div; LIFT_CMUL] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_NEG_0] THEN
      TRY(MATCH_MP_TAC LIM_NEG) THEN REWRITE_TAC[VECTOR_NEG_0] THEN
      SUBST1_TAC(VECTOR_ARITH
       `vec 0:real^1 = ((b:real^N)$j + --((a:real^N)$j)) % vec 0`) THEN
      MATCH_MP_TAC LIM_CMUL THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; DIST_0; NORM_LIFT] THEN
      X_GEN_TAC `e:real` THEN
      GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[REAL_ABS_INV] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&N)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
      ASM_SIMP_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; LE_1;
                   REAL_OF_NUM_LE; REAL_ABS_NUM] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[TAUT `a ==> b /\ c ==> d <=> a /\ c ==> b ==> d`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_MIN) THEN
    REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LIM_MAX) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA; FUN_EQ_THM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL]) THEN
    ASM_MESON_TAC[REAL_ARITH `a < x /\ x < b ==> max a (min x b) = x`]]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET = prove
 (`!f:real^M->real^N g:real^N->real^P s.
        closed s /\
        f measurable_on (:real^M) /\
        (!x. f(x) IN s) /\
        g continuous_on s
        ==> (g o f) measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^N->real^P`; `(:real^N)`; `s:real^N->bool`]
    TIETZE_UNBOUNDED) THEN
  ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `h:real^N->real^P` THEN
  DISCH_TAC THEN SUBGOAL_THEN
   `(g:real^N->real^P) o (f:real^M->real^N) = h o f` SUBST1_TAC
  THENL [ASM_SIMP_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN ASM_REWRITE_TAC[]);;

let MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET_0 = prove
 (`!f:real^M->real^N g:real^N->real^P s t.
        closed s /\
        f measurable_on t /\
        (!x. f(x) IN s) /\
        g continuous_on s /\
        vec 0 IN s /\ g(vec 0) = vec 0
        ==> (g o f) measurable_on t`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  MP_TAC(ISPECL [`(\x. if x IN t then f x else vec 0):real^M->real^N`;
                 `g:real^N->real^P`; `s:real^N->bool`]
        MEASURABLE_ON_COMPOSE_CONTINUOUS_CLOSED_SET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MEASURABLE_ON_UNIV] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic closure properties of measurable functions.                         *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON = prove
 (`!f:real^M->real^N. f continuous_on (:real^M) ==> f measurable_on (:real^M)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[measurable_on; IN_UNIV] THEN
  EXISTS_TAC `{}:real^M->bool` THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  EXISTS_TAC `\n:num. (f:real^M->real^N)` THEN
  ASM_REWRITE_TAC[LIM_CONST]);;

let MEASURABLE_ON_CONST = prove
 (`!k:real^N. (\x. k) measurable_on (:real^M)`,
  SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; CONTINUOUS_ON_CONST]);;

let MEASURABLE_ON_0 = prove
 (`!s. (\x. vec 0) measurable_on s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_CONST; COND_ID]);;

let MEASURABLE_ON_CMUL = prove
 (`!c f:real^M->real^N s.
        f measurable_on s ==> (\x. c % f x) measurable_on s`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
  SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID]);;

let MEASURABLE_ON_NEG = prove
 (`!f:real^M->real^N s.
     f measurable_on s ==> (\x. --(f x)) measurable_on s`,
  REWRITE_TAC[VECTOR_ARITH `--x:real^N = --(&1) % x`;
              MEASURABLE_ON_CMUL]);;

let MEASURABLE_ON_NEG_EQ = prove
 (`!f:real^M->real^N s. (\x. --(f x)) measurable_on s <=> f measurable_on s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
  REWRITE_TAC[VECTOR_NEG_NEG; ETA_AX]);;

let MEASURABLE_ON_NORM = prove
 (`!f:real^M->real^N s.
        f measurable_on s ==> (\x. lift(norm(f x))) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o ISPEC `\x:real^N. lift(norm x)` o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS_0)) THEN
  REWRITE_TAC[o_DEF; NORM_0; LIFT_NUM] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[continuous_on; IN_UNIV; DIST_LIFT] THEN
  GEN_TAC THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN NORM_ARITH_TAC);;

let MEASURABLE_ON_PASTECART = prove
 (`!f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. pastecart (f x) (g x)) measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^M->bool` MP_TAC)
   (X_CHOOSE_THEN `k2:real^M->bool` MP_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:num->real^M->real^P` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `g1:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k1 UNION k2:real^M->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION] THEN
  EXISTS_TAC `(\n x. pastecart (g1 n x) (g2 n x))
              :num->real^M->real^(N,P)finite_sum` THEN
  ASM_SIMP_TAC[CONTINUOUS_ON_PASTECART; ETA_AX; IN_UNION; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
  ASM_CASES_TAC `(x:real^M) IN s` THEN
  REWRITE_TAC[GSYM PASTECART_VEC] THEN ASM_SIMP_TAC[LIM_PASTECART]);;

let MEASURABLE_ON_COMBINE = prove
 (`!h:real^N->real^P->real^Q f:real^M->real^N g:real^M->real^P s.
        f measurable_on s /\ g measurable_on s /\
        (\x. h (fstcart x) (sndcart x)) continuous_on UNIV /\
        h (vec 0) (vec 0) = vec 0
        ==> (\x. h (f x) (g x)) measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\x:real^M. (h:real^N->real^P->real^Q) (f x) (g x)) =
    (\x. h (fstcart x) (sndcart x)) o (\x. pastecart (f x) (g x))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; FSTCART_PASTECART; SNDCART_PASTECART; o_THM];
    MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_0 THEN
    ASM_SIMP_TAC[MEASURABLE_ON_PASTECART; FSTCART_VEC; SNDCART_VEC]]);;

let MEASURABLE_ON_ADD = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x + g x) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMBINE THEN
  ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_SUB = prove
 (`!f:real^M->real^N g:real^M->real^N s.
        f measurable_on s /\ g measurable_on s
        ==> (\x. f x - g x) measurable_on s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_COMBINE THEN
  ASM_REWRITE_TAC[VECTOR_SUB_RZERO] THEN MATCH_MP_TAC CONTINUOUS_ON_SUB THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_MAX = prove
 (`!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. max ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`,
  let lemma = REWRITE_RULE[]
   (ISPEC `(\x y. lambda i. max (x$i) (y$i)):real^N->real^N->real^N`
          MEASURABLE_ON_COMBINE) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
  REWRITE_TAC[REAL_ARITH `max x x = x`; LAMBDA_ETA] THEN
  SIMP_TAC[continuous_on; LAMBDA_BETA; IN_UNIV; DIST_LIFT] THEN
  GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^(N,N)finite_sum`; `e:real`] THEN
  DISCH_TAC THEN EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[dist] THEN
  X_GEN_TAC `y:real^(N,N)finite_sum` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `abs(x - y) < e /\ abs(x' - y') < e
    ==> abs(max x x' - max y y') < e`) THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN CONJ_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `norm(x) < e /\ abs(x$i) <= norm x ==> abs(x$i) < e`) THEN
  ASM_SIMP_TAC[COMPONENT_LE_NORM; GSYM FSTCART_SUB; GSYM SNDCART_SUB] THEN
  ASM_MESON_TAC[REAL_LET_TRANS; NORM_FSTCART; NORM_SNDCART]);;

let MEASURABLE_ON_MIN = prove
 (`!f:real^M->real^N g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. (lambda i. min ((f x)$i) ((g x)$i)):real^N)
          measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG)) THEN
  REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_MAX) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN
  SIMP_TAC[CART_EQ; VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN REAL_ARITH_TAC);;

let MEASURABLE_ON_DROP_MUL = prove
 (`!f g:real^M->real^N s.
      f measurable_on s /\ g measurable_on s
      ==> (\x. drop(f x) % g x) measurable_on s`,
  let lemma = REWRITE_RULE[]
   (ISPEC `\x y. drop x % y :real^N` MEASURABLE_ON_COMBINE) in
  REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  REWRITE_TAC[o_DEF; ETA_AX; LIFT_DROP] THEN
  CONJ_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
  REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART]);;

let MEASURABLE_ON_LIFT_MUL = prove
 (`!f g s. (\x. lift(f x)) measurable_on s /\
           (\x. lift(g x)) measurable_on s
           ==> (\x. lift(f x * g x)) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_DROP_MUL) THEN
  REWRITE_TAC[LIFT_CMUL; LIFT_DROP]);;

let MEASURABLE_ON_VSUM = prove
 (`!f:A->real^M->real^N t.
        FINITE t /\ (!i. i IN t ==> (f i) measurable_on s)
        ==> (\x. vsum t (\i. f i x)) measurable_on s`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[VSUM_CLAUSES; MEASURABLE_ON_0; MEASURABLE_ON_ADD; IN_INSERT;
           ETA_AX]);;

let MEASURABLE_ON_COMPONENTWISE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        (!i. 1 <= i /\ i <= dimindex(:N)
             ==> (\x. lift(f x$i)) measurable_on (:real^M))`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
     ISPEC `\x:real^N. lift(x$i)` o MATCH_MP
     (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS)) THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_LIFT_COMPONENT; o_DEF];
    ALL_TAC] THEN
  REWRITE_TAC[measurable_on; IN_UNIV] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`k:num->real^M->bool`; `g:num->num->real^M->real^1`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `UNIONS(IMAGE k (1..dimindex(:N))):real^M->bool` THEN
  EXISTS_TAC `(\n x. lambda i. drop(g i n x)):num->real^M->real^N` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[FINITE_NUMSEG; IN_NUMSEG; FORALL_IN_IMAGE; FINITE_IMAGE];
    GEN_TAC THEN ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX]]);;

let MEASURABLE_ON_SPIKE = prove
 (`!f:real^M->real^N g s t.
        negligible s /\ (!x. x IN t DIFF s ==> g x = f x)
        ==> f measurable_on t ==> g measurable_on t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[measurable_on] THEN ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s UNION k:real^M->bool` THEN
  ASM_SIMP_TAC[DE_MORGAN_THM; IN_UNION; NEGLIGIBLE_UNION]);;

let MEASURABLE_ON_SPIKE_SET = prove
 (`!f:real^M->real^N s t.
        negligible (s DIFF t UNION t DIFF s)
        ==> f measurable_on s
            ==> f measurable_on t`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[measurable_on] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `g:num->real^M->real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k UNION (s DIFF t UNION t DIFF s):real^M->bool` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION; IN_UNION; DE_MORGAN_THM] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MEASURABLE_ON_RESTRICT = prove
 (`!f:real^M->real^N s.
        f measurable_on (:real^M) /\ lebesgue_measurable s
        ==> (\x. if x IN s then f(x) else vec 0) measurable_on (:real^M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lebesgue_measurable; indicator] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_DROP_MUL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f measurable_on t /\
           lebesgue_measurable s
           ==> f measurable_on s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[IN_UNIV] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_RESTRICT) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN ASM SET_TAC[]);;

let MEASURABLE_ON_LIMIT = prove
 (`!f:num->real^M->real^N g s k.
        (!n. (f n) measurable_on s) /\
        negligible k /\
        (!x. x IN s DIFF k ==> ((\n. f n x) --> g x) sequentially)
        ==> g measurable_on s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^N`; `vec 1:real^N`]
    HOMEOMORPHIC_OPEN_INTERVAL_UNIV) THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY; VEC_COMPONENT; REAL_LT_01] THEN
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h':real^N->real^N`; `h:real^N->real^N`] THEN
  REWRITE_TAC[IN_UNIV] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((h':real^N->real^N) o (h:real^N->real^N) o
     (\x. if x IN s then g x else vec 0)) measurable_on (:real^M)`
  MP_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[o_DEF; MEASURABLE_ON_UNIV]] THEN
  SUBGOAL_THEN `!y:real^N. norm(h y:real^N) <= &(dimindex(:N))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `IMAGE h UNIV = s ==> (!z. z IN s ==> P z) ==> !y. P(h y)`)) THEN
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_INTERVAL] THEN
    REWRITE_TAC[VEC_COMPONENT] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(1..dimindex(:N)) (\i. abs((y:real^N)$i))` THEN
    REWRITE_TAC[NORM_LE_L1] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC SUM_BOUND THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x /\ x < &1 ==> abs(x) <= &1`];
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS_OPEN_INTERVAL THEN
  MAP_EVERY EXISTS_TAC [`vec 0:real^N`; `vec 1:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^M`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `interval[a:real^M,b] DIFF k` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC DOMINATED_CONVERGENCE_INTEGRABLE THEN
    MAP_EVERY EXISTS_TAC
     [`(\n x. h(if x IN s then f n x else vec 0:real^N)):num->real^M->real^N`;
      `(\x. vec(dimindex(:N))):real^M->real^1`] THEN
    REWRITE_TAC[o_DEF; INTEGRABLE_CONST] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC
        MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `(\x. vec(dimindex(:N))):real^M->real^1` THEN
      ASM_REWRITE_TAC[ETA_AX; INTEGRABLE_CONST] THEN
      ASM_SIMP_TAC[DROP_VEC] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
        EXISTS_TAC `interval[a:real^M,b:real^M]` THEN CONJ_TAC THENL
         [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          ALL_TAC] THEN
        ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
        MATCH_MP_TAC(REWRITE_RULE[indicator; lebesgue_measurable]
              MEASURABLE_ON_RESTRICT) THEN
        REWRITE_TAC[MEASURABLE_ON_UNIV] THEN CONJ_TAC THENL
         [MP_TAC(ISPECL
           [`(\x. if x IN s then f (n:num) x else vec 0):real^M->real^N`;
            `h:real^N->real^N`] MEASURABLE_ON_COMPOSE_CONTINUOUS) THEN
          ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[MEASURABLE_ON_UNIV; ETA_AX];
          MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
          REWRITE_TAC[INTEGRABLE_CONST]];
        MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
        EXISTS_TAC `interval[a:real^M,b:real^M]` THEN
        REWRITE_TAC[INTEGRABLE_CONST] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
        EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
      EXISTS_TAC `interval[a:real^M,b:real^M]` THEN
      REWRITE_TAC[INTEGRABLE_CONST] THEN MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_SIMP_TAC[DROP_VEC];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[LIM_CONST] THEN
      MATCH_MP_TAC LIM_CONTINUOUS_FUNCTION THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

let MEASURABLE_ON_BILINEAR = prove
 (`!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\ f measurable_on s /\ g measurable_on s
        ==> (\x. op (f x) (g x)) measurable_on s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `ff:num->real^M->real^N`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`k':real^M->bool`; `gg:num->real^M->real^P`] THEN
  REPLICATE_TAC 3 DISCH_TAC THEN EXISTS_TAC `k UNION k':real^M->bool` THEN
  EXISTS_TAC
   `\n:num x:real^M. (op:real^N->real^P->real^Q) (ff n x) (gg n x)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
        BILINEAR_CONTINUOUS_ON_COMPOSE)) THEN
    ASM_REWRITE_TAC[ETA_AX];
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `(if x IN s then (op:real^N->real^P->real^Q) (f x) (g x) else vec 0) =
      op (if x IN s then f(x:real^M) else vec 0)
         (if x IN s then g(x:real^M) else vec 0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (MP_TAC o GEN `y:real^N` o MATCH_MP LINEAR_0 o SPEC `y:real^N`)
       (MP_TAC o GEN `z:real^P` o MATCH_MP LINEAR_0 o SPEC `z:real^P`)) THEN
      MESON_TAC[];
      REPEAT STRIP_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
       (REWRITE_RULE[TAUT `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`]
                LIM_BILINEAR)) THEN
      ASM_SIMP_TAC[]]]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT = prove
 (`!op:real^N->real^P->real^Q f g s:real^M->bool.
        bilinear op /\
        f measurable_on s /\ bounded (IMAGE f s) /\
        g absolutely_integrable_on s
        ==> (\x. op (f x) (g x)) absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP BILINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x:real^M. lift(B * C * norm((g:real^M->real^P) x))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        MEASURABLE_ON_BILINEAR)) THEN
    ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE];
    REWRITE_TAC[LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC INTEGRABLE_CMUL) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
    TRANS_TAC REAL_LE_TRANS
     `B * norm((f:real^M->real^N) x) * norm(g x:real^P)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE]]);;

let MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE_AE = prove
 (`!f:real^M->real^N g s t.
        f measurable_on s /\  g integrable_on s /\ negligible t /\
        (!x. x IN s DIFF t ==> norm(f x) <= drop(g x))
        ==> f absolutely_integrable_on s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] ABSOLUTELY_INTEGRABLE_SPIKE) THEN
  MAP_EVERY EXISTS_TAC
   [`\x. if x IN s DIFF t then (f:real^M->real^N) x else vec 0`;
    `t:real^M->bool`] THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC `\x. if x IN s DIFF t then (g:real^M->real^1) x else vec 0` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[TAUT `p ==> q ==> r <=> q ==> p ==> r`]
        MEASURABLE_ON_SPIKE));
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (ONCE_REWRITE_RULE[TAUT `p ==> q ==> r <=> q ==> p ==> r`]
        INTEGRABLE_SPIKE));
    ASM_MESON_TAC[REAL_LE_REFL; NORM_0; DROP_VEC]] THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Natural closure properties of measurable functions; the intersection      *)
(* one is actually quite tedious since we end up reinventing cube roots      *)
(* before they actually get introduced in transcendentals.ml                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_EMPTY = prove
 (`!f:real^M->real^N. f measurable_on {}`,
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[NOT_IN_EMPTY; MEASURABLE_ON_CONST]);;

let MEASURABLE_ON_INTER = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ f measurable_on t
        ==> f measurable_on (s INTER t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ONCE_REWRITE_TAC[MEASURABLE_ON_COMPONENTWISE] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q ==> r <=> p /\ p ==> q ==> r`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_LIFT_MUL) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_LIFT_MUL) THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
  REWRITE_TAC[VEC_COMPONENT; REAL_ARITH
   `(if p then x else &0) * (if q then y else &0) =
    if p /\ q then x * y else &0`] THEN
  SUBGOAL_THEN `!s. (\x. lift (drop x pow 3)) continuous_on s` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[REAL_ARITH `(x:real) pow 3 = x * x * x`] THEN
    REWRITE_TAC[LIFT_CMUL] THEN
    REPEAT(MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
           ASM_REWRITE_TAC[o_DEF; LIFT_DROP; CONTINUOUS_ON_ID]);
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. !x. lift(drop(r x) pow 3) = x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; FORALL_LIFT; GSYM EXISTS_DROP; LIFT_EQ] THEN
    X_GEN_TAC `x:real` THEN  MP_TAC(ISPECL
     [`\x. lift (drop x pow 3)`; `lift(--(abs x + &1))`;
      `lift(abs x + &1)`;`x:real`; `1`] IVT_INCREASING_COMPONENT_1) THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; EXISTS_DROP] THEN
    ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    REWRITE_TAC[DIMINDEX_1; LE_REFL] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `(:real^1)`) THEN
      ASM_SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV];
      REWRITE_TAC[REAL_BOUNDS_LE; REAL_POW_NEG; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH
      `&0 <= x /\ &0 <= x pow 2 /\ &0 <= x pow 3 ==> x <= (x + &1) pow 3`) THEN
      SIMP_TAC[REAL_POW_LE; REAL_ABS_POS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x.  r(lift(x pow 3)) = lift x` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN GEN_TAC THEN
    MATCH_MP_TAC REAL_POW_EQ_ODD THEN EXISTS_TAC `3` THEN
    ASM_REWRITE_TAC[ARITH; GSYM LIFT_EQ; LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^1->real^1) continuous_on (:real^1)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_INVERSE_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`\x. lift(drop x pow 3)`; `(:real^1)`] THEN
    ASM_REWRITE_TAC[LIFT_DROP] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(fun th -> REPEAT STRIP_TAC THEN SUBST1_TAC(SYM th)) THEN
    MATCH_MP_TAC INJECTIVE_INTO_1D_IMP_OPEN_MAP THEN
    ASM_REWRITE_TAC[PATH_CONNECTED_UNIV; LIFT_EQ] THEN
    SIMP_TAC[REAL_POW_EQ_ODD_EQ; ARITH; DROP_EQ];
    ONCE_REWRITE_TAC[REAL_ARITH `&0 = &0 pow 3`] THEN
    REWRITE_TAC[REAL_ARITH `(x * x) * x:real = x pow 3`; IN_INTER] THEN
    REWRITE_TAC[MESON[] `(if p then x pow 3 else y pow 3) =
                         (if p then x else y:real) pow 3`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o ISPEC `r:real^1->real^1` o
      MATCH_MP (REWRITE_RULE[IMP_CONJ] MEASURABLE_ON_COMPOSE_CONTINUOUS)) THEN
    ASM_REWRITE_TAC[o_DEF]]);;

let MEASURABLE_ON_DIFF = prove
 (`!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s DIFF t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_INTER) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[IMP_IMP] THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; IN_DIFF; IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_UNION = prove
 (`!f:real^M->real^N s t.
    f measurable_on s /\ f measurable_on t ==> f measurable_on (s UNION t)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_INTER) THEN
  POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_ADD) THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MEASURABLE_ON_SUB) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM; IN_UNION; IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN
  MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(x:real^M) IN t`] THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MEASURABLE_ON_UNIONS = prove
 (`!f:real^M->real^N k.
        FINITE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; MEASURABLE_ON_EMPTY; UNIONS_INSERT] THEN
  SIMP_TAC[FORALL_IN_INSERT; MEASURABLE_ON_UNION]);;

let MEASURABLE_ON_COUNTABLE_UNIONS = prove
 (`!f:real^M->real^N k.
        COUNTABLE k /\ (!s. s IN k ==> f measurable_on s)
        ==> f measurable_on (UNIONS k)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k:(real^M->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[UNIONS_0; MEASURABLE_ON_EMPTY] THEN
  MP_TAC(ISPEC `k:(real^M->bool)->bool` COUNTABLE_AS_IMAGE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:num->real^M->bool` THEN DISCH_THEN SUBST_ALL_TAC THEN
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
  EXISTS_TAC `(\n x. if x IN UNIONS (IMAGE d (0..n)) then f x else vec 0):
              num->real^M->real^N` THEN
  EXISTS_TAC `{}:real^M->bool` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY; MEASURABLE_ON_UNIV] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_UNIONS THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FORALL_IN_IMAGE]) THEN
    SIMP_TAC[FORALL_IN_IMAGE; IN_UNIV; FINITE_IMAGE; FINITE_NUMSEG];
    X_GEN_TAC `x:real^M` THEN DISCH_THEN(K ALL_TAC) THEN
    ASM_CASES_TAC `(x:real^M) IN UNIONS (IMAGE d (:num))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LIM_EVENTUALLY THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_UNIV; EVENTUALLY_SEQUENTIALLY] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN DISCH_TAC THEN
      X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNIONS]) THEN
      ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
      REWRITE_TAC[EXISTS_IN_IMAGE; IN_NUMSEG; LE_0] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC ALWAYS_EVENTUALLY THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Negligibility of a Lipschitz image of a negligible set.                   *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> negligible(IMAGE f s)`,
  let lemma = prove
   (`!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ bounded s /\ negligible s /\ &0 < B /\
        (!x. x IN s
             ==> ?t. open t /\ x IN t /\
                     !y. y IN s INTER t
                         ==> norm(f y - f x) <= B * norm(y - x))
        ==> negligible(IMAGE f s)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^M->bool`;
                   `e / &2 / (&2 * B * &(dimindex(:M))) pow (dimindex(:N))`]
      MEASURABLE_OUTER_OPEN) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE] THEN
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      MATCH_MP_TAC REAL_POW_LT THEN
      REPEAT(MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC) THEN
      ASM_SIMP_TAC[DIMINDEX_GE_1; REAL_OF_NUM_LT; ARITH; LE_1];
      ALL_TAC] THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_HALF; MEASURE_EQ_0] THEN
    REWRITE_TAC[REAL_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!x. ?r. &0 < r /\ r <= &1 / &2 /\
              (x IN s
               ==> !y. norm(y - x:real^M) < r
                       ==> y IN t /\
                           (y IN s
                            ==> norm(f y - f x:real^N) <= B * norm(y - x)))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC; EXISTS_TAC `&1 / &4` THEN REAL_ARITH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `t INTER u :real^M->bool` open_def) THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTER; dist]] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min (&1 / &2) r` THEN
      ASM_REWRITE_TAC[REAL_MIN_LE; REAL_LT_MIN] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      REWRITE_TAC[RIGHT_IMP_FORALL_THM; IMP_IMP] THEN
      X_GEN_TAC `r:real^M->real` THEN STRIP_TAC] THEN
    SUBGOAL_THEN
     `?c. s SUBSET interval[--(vec c):real^M,vec c] /\
          ~(interval(--(vec c):real^M,vec c) = {})`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `abs c + &1` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      DISCH_TAC THEN REWRITE_TAC[SUBSET; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_BOUNDS_LE] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`--(vec c):real^M`; `(vec c):real^M`; `s:real^M->bool`;
                   `\x:real^M. ball(x,r x)`] COVERING_LEMMA) THEN
    ASM_REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN

    REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!k. k IN D
          ==> ?u v z. k = interval[u,v] /\ ~(interval(u,v) = {}) /\
                      z IN s /\ z IN interval[u,v] /\
                      interval[u:real^M,v] SUBSET ball(z,r z)`
    MP_TAC THENL
     [X_GEN_TAC `d:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. d = interval[u,v]` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^M` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^M` THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_CLOSED_INTERVAL; IN_INTER];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`u:(real^M->bool)->real^M`; `v:(real^M->bool)->real^M`;
      `z:(real^M->bool)->real^M`] THEN
    DISCH_THEN(LABEL_TAC "*") THEN EXISTS_TAC
     `UNIONS(IMAGE (\d:real^M->bool.
         interval[(f:real^M->real^N)(z d) -
      (B * &(dimindex(:M)) *
      ((v(d):real^M)$1 - (u(d):real^M)$1)) % vec 1:real^N,
                  f(z d) +
                  (B * &(dimindex(:M)) * (v(d)$1 - u(d)$1)) % vec 1]) D)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^M) IN UNIONS D` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; REWRITE_TAC[UNIONS_IMAGE]] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `d:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^M) IN ball(z(d:real^M->bool),r(z d))` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; REWRITE_TAC[IN_BALL; dist]] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `y IN t /\
        norm((f:real^M->real^N) y - f(z d)) <= B * norm(y - z(d:real^M->bool))`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTERVAL] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
      REWRITE_TAC[REAL_ARITH
       `z - b <= y /\ y <= z + b <=> abs(y - z) <= b`] THEN
      REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          REAL_LE_TRANS)) THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
      W(MP_TAC o PART_MATCH lhand NORM_LE_L1 o lhand o snd) THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV)
       [GSYM CARD_NUMSEG_1] THEN
      SIMP_TAC[GSYM SUM_CONST; FINITE_NUMSEG] THEN
      MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `j:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((v:(real^M->bool)->real^M) d - u d)$j` THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN CONJ_TAC THENL
       [SUBGOAL_THEN `y IN interval[(u:(real^M->bool)->real^M) d,v d] /\
                      (z d) IN interval[u d,v d]`
        MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
        DISCH_THEN(CONJUNCTS_THEN (MP_TAC o SPEC `j:num`)) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN FIRST_X_ASSUM(MP_TAC o SPECL
         [`(u:(real^M->bool)->real^M) d`; `(v:(real^M->bool)->real^M) d`]) THEN
        ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL]];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(x <= e / &2 ==> x < e) /\ P /\ x <= e / &2 ==> P /\ x < e`) THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D':(real^M->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
    ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_INTERVAL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `(&2 * B * &(dimindex(:M))) pow (dimindex(:N)) *
                sum D' (\d:real^M->bool. measure d)` THEN
    SUBGOAL_THEN `FINITE(D':(real^M->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_LE THEN
      ASM_REWRITE_TAC[MEASURE_INTERVAL] THEN X_GEN_TAC `d:real^M->bool` THEN
      DISCH_TAC THEN REWRITE_TAC[CONTENT_CLOSED_INTERVAL_CASES] THEN
      REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; REAL_ARITH
       `(a - x <= a + x <=> &0 <= x) /\ (a + x) - (a - x) = &2 * x`] THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
      ASM_SIMP_TAC[REAL_LE_MUL_EQ; REAL_OF_NUM_LT; LE_1; DIMINDEX_GE_1] THEN
      SUBGOAL_THEN `d = interval[u d:real^M,v d]`
       (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
      THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      SUBGOAL_THEN
       `!i. 1 <= i /\ i <= dimindex(:M)
            ==> ((u:(real^M->bool)->real^M) d)$i <= (v d:real^M)$i`
      MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; INTERVAL_NE_EMPTY; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SIMP_TAC[REAL_SUB_LE; DIMINDEX_GE_1; LE_REFL] THEN DISCH_TAC THEN
      REWRITE_TAC[PRODUCT_CONST_NUMSEG; REAL_POW_MUL] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_POW_LT; REAL_OF_NUM_LT; ARITH;
                   GSYM REAL_MUL_ASSOC; ADD_SUB; DIMINDEX_GE_1; LE_1] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `((v d:real^M)$1 - ((u:(real^M->bool)->real^M) d)$1)
                  pow (dimindex(:M))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_POW_MONO_INV THEN
        ASM_SIMP_TAC[REAL_SUB_LE; DIMINDEX_GE_1; LE_REFL] THEN
        REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN W(MP_TAC o
          PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
        REWRITE_TAC[DIMINDEX_GE_1; LE_REFL] THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        MATCH_MP_TAC(NORM_ARITH
         `!z r. norm(z - u) < r /\ norm(z - v) < r /\ r <= &1 / &2
                ==> norm(v - u:real^M) <= &1`) THEN
        MAP_EVERY EXISTS_TAC
         [`(z:(real^M->bool)->real^M) d`;
          `r((z:(real^M->bool)->real^M) d):real`] THEN
        ASM_REWRITE_TAC[GSYM dist; GSYM IN_BALL] THEN
        SUBGOAL_THEN
         `(u:(real^M->bool)->real^M) d IN interval[u d,v d] /\
          (v:(real^M->bool)->real^M) d IN interval[u d,v d]`
        MP_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
        ASM_REWRITE_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY];
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CARD_NUMSEG_1] THEN
        SIMP_TAC[GSYM PRODUCT_CONST; FINITE_NUMSEG] THEN
        MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC PRODUCT_EQ_NUMSEG THEN
        FIRST_X_ASSUM(MP_TAC o SPECL
         [`(u:(real^M->bool)->real^M) d`; `(v:(real^M->bool)->real^M) d`]) THEN
        ASM_MESON_TAC[DIMINDEX_GE_1; LE_REFL; SUBSET]];
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `(&2 * B * &(dimindex(:M))) pow dimindex(:N) *
                  measure(t:real^M->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN
        CONJ_TAC THENL [MATCH_MP_TAC REAL_LT_IMP_LE; ALL_TAC];
        MATCH_MP_TAC REAL_LT_IMP_LE THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        W(MP_TAC o PART_MATCH (rand o rand) REAL_LT_RDIV_EQ o snd)] THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LT_MUL; LE_1; DIMINDEX_GE_1;
                   REAL_ARITH `&0 < &2 * B <=> &0 < B`; REAL_OF_NUM_LT] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(UNIONS D':real^M->bool)` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`D':(real^M->bool)->bool`; `UNIONS D':real^M->bool`]
          MEASURE_ELEMENTARY) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[division_of] THEN
          CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
          GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
           [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; INTERIOR_EMPTY]];
          DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
          MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET]];
        MATCH_MP_TAC MEASURE_SUBSET THEN CONJ_TAC THENL
         [MATCH_MP_TAC MEASURABLE_UNIONS THEN
          ASM_MESON_TAC[MEASURABLE_INTERVAL; SUBSET];
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `UNIONS D:real^M->bool` THEN
          ASM_SIMP_TAC[SUBSET_UNIONS] THEN
          REWRITE_TAC[SUBSET; FORALL_IN_UNIONS] THEN
          X_GEN_TAC `d:real^M->bool` THEN
          REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN
          DISCH_TAC THEN REWRITE_TAC[GSYM SUBSET] THEN
          SUBGOAL_THEN `d SUBSET ball(z d:real^M,r(z d))` MP_TAC THENL
           [ASM_MESON_TAC[];
            REWRITE_TAC[SUBSET; IN_BALL; dist] THEN
            ASM_MESON_TAC[NORM_SUB]]]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s = UNIONS
    {{x | x IN s /\ norm(x:real^M) <= &n /\
          ?t. open t /\ x IN t /\
              !y. y IN s INTER t
                  ==> norm(f y - f x:real^N) <= (&n + &1) * norm(y - x)} |
     n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
    REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(SPEC `max (norm(x:real^M)) b` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[REAL_MAX_LE] THEN
    X_GEN_TAC `n:num` THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `b * norm(y - x:real^M)` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[GSYM IMAGE_o; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC lemma THEN EXISTS_TAC `&n + &1` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^M,&n)` THEN
      SIMP_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; IN_ELIM_THM];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REAL_ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]]]);;

let NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE_LOWDIM = prove
 (`!f:real^M->real^N s.
        dimindex(:M) < dimindex(:N) /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`(f:real^M->real^N) o (sndcart:real^(1,M)finite_sum->real^M)`;
     `IMAGE (pastecart (vec 0:real^1)) (s:real^M->bool)`]
    NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; SNDCART_PASTECART; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + m <= n <=> m < n`] THEN CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `{x:real^(1,M)finite_sum | x$1 = &0}` THEN
    SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; DIMINDEX_GE_1; LE_REFL] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[pastecart; LAMBDA_BETA; DIMINDEX_1; LE_REFL; VEC_COMPONENT;
             DIMINDEX_FINITE_SUM; ARITH_RULE `1 <= 1 + n`];
    REWRITE_TAC[IN_INTER; IMP_CONJ; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[GSYM dist; DIST_PASTECART_CANCEL; SNDCART_PASTECART] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; IN_INTER] THEN
    MAP_EVERY X_GEN_TAC [`u:real^M->bool`; `b:real`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`(:real^1) PCROSS (u:real^M->bool)`; `b:real`] THEN
    ASM_SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV] THEN
    ASM_SIMP_TAC[dist]]);;

let NEGLIGIBLE_LIPSCHITZ_IMAGE_UNIV = prove
 (`!f:real^N->real^N s B.
        negligible s /\ (!x y. norm(f x - f y) <= B * norm(x - y))
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[LE_REFL] THEN X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`interval(a - vec 1:real^N,a + vec 1)`; `B:real`] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL; IN_INTERVAL] THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ negligible s /\ f differentiable_on s
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [differentiable_on]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  ASM_REWRITE_TAC[differentiable; HAS_DERIVATIVE_WITHIN_ALT] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1`) THEN
  REWRITE_TAC[REAL_LT_01; REAL_MUL_RID] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP LINEAR_BOUNDED_POS) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `ball(x:real^M,d)` THEN EXISTS_TAC `B + &1` THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REWRITE_TAC[IN_BALL; dist; REAL_ADD_RDISTRIB] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(NORM_ARITH
   `!d. norm(y - x - d:real^N) <= z /\ norm(d) <= b
        ==> norm(y - x) <= b + z`) THEN
  EXISTS_TAC `(f':real^M->real^N)(y - x)` THEN
  ASM_MESON_TAC[NORM_SUB]);;

let NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM = prove
 (`!f:real^M->real^N s.
        dimindex(:M) < dimindex(:N) /\ f differentiable_on s
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(ASSUME_TAC o MATCH_MP
   (ARITH_RULE `m < n ==> !x:num. x <= m ==> x <= n`)) THEN
  SUBGOAL_THEN
   `(f:real^M->real^N) =
    (f o ((\x. lambda i. x$i):real^N->real^M)) o
    ((\x. lambda i. if i <= dimindex(:M) then x$i else &0):real^M->real^N)`
  SUBST1_TAC THENL
   [SIMP_TAC[FUN_EQ_THM; o_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA];
    ONCE_REWRITE_TAC[IMAGE_o] THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
    REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `{y:real^N | y$(dimindex(:N)) = &0}` THEN
      SIMP_TAC[NEGLIGIBLE_STANDARD_HYPERPLANE; LE_REFL; DIMINDEX_GE_1] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[LAMBDA_BETA; LE_REFL; DIMINDEX_GE_1] THEN
      ASM_REWRITE_TAC[GSYM NOT_LT];
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [differentiable_on]) THEN
      REWRITE_TAC[differentiable_on; FORALL_IN_IMAGE] THEN STRIP_TAC THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC DIFFERENTIABLE_CHAIN_WITHIN THEN CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_LINEAR THEN
        SIMP_TAC[linear; LAMBDA_BETA; CART_EQ;
                 VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN BINOP_TAC THENL
         [AP_TERM_TAC;
          MATCH_MP_TAC(SET_RULE
           `(!x. f(g x) = x) ==> s = IMAGE f (IMAGE g s)`)] THEN
        ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA]]]]);;

(* ------------------------------------------------------------------------- *)
(* Simplest case of Sard's theorem (we don't need continuity of derivative). *)
(* ------------------------------------------------------------------------- *)

let BABY_SARD = prove
 (`!f:real^M->real^N f' s.
        dimindex(:M) <= dimindex(:N) /\
        (!x. x IN s
             ==> (f has_derivative f' x) (at x within s) /\
                 rank(matrix(f' x)) < dimindex(:N))
        ==> negligible(IMAGE f s)`,
  let lemma = prove
   (`!p w e m.
      dim p < dimindex(:N) /\ &0 <= m /\ &0 <= e
      ==> ?s. measurable s /\
              {z:real^N | norm(z - w) <= m /\
                          ?t. t IN p /\ norm(z - w - t) <= e}
              SUBSET s /\
              measure s <= (&2 * e) * (&2 * m) pow (dimindex(:N) - 1)`,
    REPEAT GEN_TAC THEN GEN_GEOM_ORIGIN_TAC `w:real^N` ["t"; "p"] THEN
    REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
    DISCH_THEN(MP_TAC o MATCH_MP LOWDIM_SUBSET_HYPERPLANE) THEN
    REWRITE_TAC[VECTOR_SUB_RZERO; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `a:real^N` THEN GEOM_BASIS_MULTIPLE_TAC 1 `a:real^N` THEN
    X_GEN_TAC `a:real` THEN GEN_REWRITE_TAC LAND_CONV [REAL_LE_LT] THEN
    ASM_CASES_TAC `a = &0` THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
     `interval[--(lambda i. if i = 1 then e else m):real^N,
               (lambda i. if i = 1 then e else m)]` THEN
    REWRITE_TAC[MEASURABLE_INTERVAL] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTERVAL] THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      REWRITE_TAC[REAL_BOUNDS_LE] THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [ALL_TAC; ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
      ASM_SIMP_TAC[SPAN_SUPERSET; IN_ELIM_THM; DOT_BASIS; DOT_LMUL;
                   DIMINDEX_GE_1; LE_REFL; REAL_ENTIRE; REAL_LT_IMP_NZ] THEN
      MP_TAC(ISPECL [`x - y:real^N`; `1`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; ARITH; DIMINDEX_GE_1] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
      SIMP_TAC[VECTOR_NEG_COMPONENT; LAMBDA_BETA] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POW_LE; REAL_POS] THEN
      REWRITE_TAC[REAL_ARITH `x - --x = &2 * x`] THEN
      SIMP_TAC[PRODUCT_CLAUSES_LEFT; DIMINDEX_GE_1] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS] THEN
      SIMP_TAC[ARITH; ARITH_RULE `2 <= n ==> ~(n = 1)`] THEN
      SIMP_TAC[PRODUCT_CONST_NUMSEG; DIMINDEX_GE_1; REAL_LE_REFL; ARITH_RULE
       `1 <= n ==> (n + 1) - 2 = n - 1`]]) in
  let semma = prove
   (`!f:real^M->real^N f' s B.
          dimindex(:M) <= dimindex(:N) /\ &0 < B /\ bounded s /\
          (!x. x IN s ==> (f has_derivative f' x) (at x within s) /\
                         rank(matrix(f' x)) < dimindex(:N) /\ onorm(f' x) <= B)
          ==> negligible(IMAGE f s)`,
    REWRITE_TAC[TAUT `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `!x. x IN s ==> linear((f':real^M->real^M->real^N) x)`
    ASSUME_TAC THENL [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?c. s SUBSET interval(--(vec c):real^M,vec c) /\
            ~(interval(--(vec c):real^M,vec c) = {})`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bounded]) THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `abs c + &1` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      DISCH_TAC THEN REWRITE_TAC[SUBSET; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[IN_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
      STRIP_TAC THEN REWRITE_TAC[REAL_BOUNDS_LT] THEN W(MP_TAC o
        PART_MATCH lhand COMPONENT_LE_NORM o lhand o snd) THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_NE_EMPTY]) THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[VEC_COMPONENT; DIMINDEX_GE_1;
                LE_REFL; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `--x < x <=> &0 < &2 * x`; REAL_OF_NUM_MUL] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `?d. &0 < d /\ d <= B /\
          (d * &2) * (&4 * B) pow (dimindex(:N) - 1) <=
          e / &(2 * c) pow dimindex(:M) / &(dimindex(:M)) pow dimindex(:M)`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC
       `min B (e / &(2 * c) pow dimindex(:M) /
               &(dimindex(:M)) pow dimindex(:M) /
               (&4 * B) pow (dimindex(:N) - 1) / &2)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_ARITH `min x y <= x`] THEN
      CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC) THEN
        ASM_SIMP_TAC[REAL_POW_LT; REAL_OF_NUM_LT; DIMINDEX_GE_1; LE_1;
                     REAL_ARITH `&0 < &4 * B <=> &0 < B`; ARITH];
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_POW_LT;
                     REAL_ARITH `&0 < &4 * B <=> &0 < B`; ARITH] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x. ?r. &0 < r /\ r <= &1 / &2 /\
              (x IN s
               ==> !y. y IN s /\ norm(y - x) < r
                       ==> norm((f:real^M->real^N) y - f x - f' x (y - x)) <=
                           d * norm(y - x))`
    MP_TAC THENL
     [X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN s` THEN
      ASM_REWRITE_TAC[] THENL
       [ALL_TAC; EXISTS_TAC `&1 / &4` THEN REAL_ARITH_TAC] THEN
      UNDISCH_THEN
       `!x. x IN s ==> ((f:real^M->real^N) has_derivative f' x) (at x within s)`
       (MP_TAC o REWRITE_RULE[HAS_DERIVATIVE_WITHIN_ALT]) THEN
      ASM_SIMP_TAC[RIGHT_IMP_FORALL_THM] THEN
      DISCH_THEN(MP_TAC o SPECL [`x:real^M`; `d:real`]) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min r (&1 / &2)` THEN
      ASM_REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_MESON_TAC[];
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
      X_GEN_TAC `r:real^M->real` THEN REWRITE_TAC[RIGHT_IMP_FORALL_THM] THEN
      REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(LABEL_TAC "*")] THEN
    MP_TAC(ISPECL [`--(vec c):real^M`; `(vec c):real^M`; `s:real^M->bool`;
                   `\x:real^M. ball(x,r x)`] COVERING_LEMMA) THEN
    ASM_REWRITE_TAC[gauge; OPEN_BALL; CENTRE_IN_BALL] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS; INTERVAL_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!k:real^M->bool.
          k IN D
          ==> ?t. measurable(t) /\
                  IMAGE (f:real^M->real^N) (k INTER s) SUBSET t /\
                  measure t <= e / &(2 * c) pow (dimindex(:M)) * measure(k)`
    MP_TAC THENL
     [X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]`
       (REPEAT_TCL CHOOSE_THEN SUBST_ALL_TAC)
      THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?x:real^M. x IN (s INTER interval[u,v]) /\
                               interval[u,v] SUBSET ball(x,r x)`
      MP_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[IN_INTER]] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`IMAGE ((f':real^M->real^M->real^N) x) (:real^M)`;
               `(f:real^M->real^N) x`;
                 `d * norm(v - u:real^M)`;
                 `(&2 * B) * norm(v - u:real^M)`]
          lemma) THEN
      ANTS_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_POS; NORM_POS_LE; REAL_LT_IMP_LE] THEN
        MP_TAC(ISPEC `matrix ((f':real^M->real^M->real^N) x)`
          RANK_DIM_IM) THEN
        ASM_SIMP_TAC[MATRIX_WORKS] THEN REWRITE_TAC[ETA_AX] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `t:real^N->bool` THEN
      REPEAT(MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[]) THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] SUBSET_TRANS) THEN
        REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_ELIM_THM] THEN
        X_GEN_TAC `y:real^M` THEN
        REWRITE_TAC[IN_INTER; EXISTS_IN_IMAGE; IN_UNIV] THEN
        STRIP_TAC THEN REMOVE_THEN "*"
         (MP_TAC o SPECL [`x:real^M`; `y:real^M`]) THEN
        ANTS_TAC THENL
         [ASM_MESON_TAC[IN_BALL; SUBSET; NORM_SUB; dist]; ALL_TAC] THEN
        DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
         [REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC(NORM_ARITH
           `norm(z) <= B /\ d <= B
            ==> norm(y - x - z:real^N) <= d
                ==> norm(y - x) <= &2 * B`) THEN
          CONJ_TAC THENL
           [MP_TAC(ISPEC `(f':real^M->real^M->real^N) x` ONORM) THEN
            ASM_SIMP_TAC[] THEN
            DISCH_THEN(MP_TAC o SPEC `y - x:real^M` o CONJUNCT1) THEN
            MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            ASM_SIMP_TAC[ONORM_POS_LE; NORM_POS_LE];
            MATCH_MP_TAC REAL_LE_MUL2 THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; NORM_POS_LE]];
          DISCH_THEN(fun th -> EXISTS_TAC `y - x:real^M` THEN MP_TAC th) THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
          ASM_SIMP_TAC[REAL_LE_LMUL_EQ]] THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL])) THEN
        REWRITE_TAC[IMP_IMP; AND_FORALL_THM] THEN
        MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
        DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
        ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
        REWRITE_TAC[REAL_ARITH `&2 * (&2 * B) * n = (&4 * B) * n`] THEN
        GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [REAL_POW_MUL] THEN
        SIMP_TAC[REAL_ARITH `(&2 * d * n) * a * b = d * &2 * a * (n * b)`] THEN
        REWRITE_TAC[GSYM(CONJUNCT2 real_pow)] THEN
        SIMP_TAC[DIMINDEX_GE_1; ARITH_RULE `1 <= n ==> SUC(n - 1) = n`] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `e / &(2 * c) pow (dimindex(:M)) /
                    (&(dimindex(:M)) pow dimindex(:M)) *
                    norm(v - u:real^M) pow dimindex(:N)` THEN
        CONJ_TAC THENL
         [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
          ASM_SIMP_TAC[NORM_POS_LE; REAL_POW_LE];
          ALL_TAC] THEN
        GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [real_div] THEN
        REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_OF_NUM_LT;
                 LE_1; DIMINDEX_GE_1] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `norm(v - u:real^M) pow dimindex(:M)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_POW_MONO_INV THEN ASM_REWRITE_TAC[NORM_POS_LE] THEN
          SUBGOAL_THEN `u IN ball(x:real^M,r x) /\ v IN ball(x,r x)` MP_TAC
          THENL
           [ASM_MESON_TAC[SUBSET; ENDS_IN_INTERVAL; INTERIOR_EMPTY];
            REWRITE_TAC[IN_BALL] THEN
            SUBGOAL_THEN `(r:real^M->real) x <= &1 / &2` MP_TAC THENL
              [ASM_REWRITE_TAC[]; CONV_TAC NORM_ARITH]];
          REMOVE_THEN "*" (K ALL_TAC) THEN
          FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^M`; `v:real^M`]) THEN
          ASM_REWRITE_TAC[REAL_ARITH `x - --x = &2 * x`] THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM; REAL_OF_NUM_MUL] THEN
          X_GEN_TAC `p:num` THEN DISCH_TAC THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `(sum(1..dimindex(:M)) (\i. abs((v - u:real^M)$i)))
                      pow (dimindex(:M))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC REAL_POW_LE2 THEN SIMP_TAC[NORM_POS_LE; NORM_LE_L1];
            REWRITE_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
            GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
             [GSYM REAL_SUB_LE] THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_POW2] THEN
            ASM_SIMP_TAC[SUM_CONST_NUMSEG; PRODUCT_CONST_NUMSEG;
                         VECTOR_SUB_COMPONENT; ADD_SUB] THEN
            REWRITE_TAC[REAL_POW_MUL; REAL_MUL_SYM] THEN
            MATCH_MP_TAC REAL_EQ_IMP_LE THEN BINOP_TAC THEN REWRITE_TAC[] THEN
            AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[REAL_ABS_REFL] THEN
            ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_LT_DIV; REAL_LT_POW2]]]];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `g:(real^M->bool)->(real^N->bool)` THEN DISCH_TAC THEN
      EXISTS_TAC `UNIONS (IMAGE (g:(real^M->bool)->(real^N->bool)) D)` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
      ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
      X_GEN_TAC `D':(real^M->bool)->bool` THEN STRIP_TAC THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
        lhand o snd) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC
       `sum D' (\k:real^M->bool.
                  e / &(2 * c) pow (dimindex(:M)) * measure k)` THEN CONJ_TAC
      THENL [MATCH_MP_TAC SUM_LE THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[SUM_LMUL] THEN
      REWRITE_TAC[REAL_ARITH `e / b * x:real = (e * x) / b`] THEN
      ASM_SIMP_TAC[REAL_POW_LT; REAL_LE_LDIV_EQ; REAL_LE_LMUL_EQ] THEN
      MP_TAC(ISPECL [`D':(real^M->bool)->bool`; `UNIONS D':real^M->bool`]
              MEASURE_ELEMENTARY) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[division_of] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET]] THEN
        GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; INTERIOR_EMPTY]];
        ALL_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH `y = z /\ x <= e ==> x = y ==> z <= e`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
        ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(interval[--(vec c):real^M,vec c])` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_INTERVAL] THEN
        CONJ_TAC THENL [MATCH_MP_TAC MEASURABLE_UNIONS; ASM SET_TAC[]] THEN
        ASM_MESON_TAC[SUBSET; MEASURABLE_INTERVAL];
        SIMP_TAC[MEASURE_INTERVAL; CONTENT_CLOSED_INTERVAL_CASES] THEN
        REWRITE_TAC[VEC_COMPONENT; VECTOR_NEG_COMPONENT; REAL_ARITH
         `x - --x = &2 * x /\ (--x <= x <=> &0 <= &2 * x)`] THEN
        ASM_SIMP_TAC[REAL_OF_NUM_MUL; REAL_LT_IMP_LE] THEN
        REWRITE_TAC[PRODUCT_CONST_NUMSEG; ADD_SUB; REAL_LE_REFL]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `s = UNIONS
    {{x | x IN s /\ norm(x:real^M) <= &n /\
          onorm((f':real^M->real^M->real^N) x) <= &n} |
     n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_MAX_LE; REAL_ARCH_SIMPLE];
    REWRITE_TAC[IMAGE_UNIONS] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[GSYM IMAGE_o; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[IN_UNIV] THEN
    MATCH_MP_TAC semma THEN
    MAP_EVERY EXISTS_TAC [`f':real^M->real^M->real^N`; `&n + &1:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `cball(vec 0:real^M,&n)` THEN
      SIMP_TAC[BOUNDED_CBALL; SUBSET; IN_CBALL_0; IN_ELIM_THM];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[REAL_ARITH `x <= n ==> x <= n + &1`] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       HAS_DERIVATIVE_WITHIN_SUBSET)) THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Also negligibility of BV low-dimensional image.                           *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL = prove
 (`!f:real^1->real^N s.
        2 <= dimindex(:N) /\ f has_bounded_variation_on s /\ is_interval s
        ==> negligible(IMAGE f s)`,
  let lemma = prove
   (`!f:real^1->real^N a b.
          2 <= dimindex(:N) /\ f has_bounded_variation_on interval[a,b]
          ==> negligible(IMAGE f (interval[a,b]))`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FACTOR_THROUGH_VARIATION) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` (STRIP_ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN
     `IMAGE (f:real^1->real^N) (interval[a,b]) =
      IMAGE g { lift(vector_variation (interval[a,u]) f) | u |
                u IN interval[a,b]}`
    SUBST1_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; o_DEF] THEN ASM SET_TAC[];
      MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE_LOWDIM THEN
      ASM_REWRITE_TAC[DIMINDEX_1; ARITH_RULE `1 < n <=> 2 <= n`] THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      MAP_EVERY EXISTS_TAC [`(:real^1)`; `&1`] THEN
      ASM_SIMP_TAC[GSYM dist; REAL_MUL_LID; IN_INTER; IN_UNIV; OPEN_UNIV]]) in
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
   `IMAGE (f:real^1->real^N)
        (closure s INTER UNIONS {interval[--vec n,vec n] | n IN (:num)})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTER_UNIONS; IMAGE_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPEC `closure s INTER interval[--vec n:real^1,vec n]`
     IS_INTERVAL_COMPACT) THEN
    SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_INTERVAL; CLOSED_CLOSURE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IS_INTERVAL_CONVEX_1]) THEN
    ASM_SIMP_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CLOSURE; CONVEX_INTER;
                 CONVEX_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUBSET THEN
    EXISTS_TAC `closure s:real^1->bool` THEN
    ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ON_CLOSURE; IS_INTERVAL_CONVEX_1] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC IMAGE_SUBSET THEN
    REWRITE_TAC[SUBSET_INTER; CLOSURE_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `(!x. ?n. x IN f n)
      ==> s SUBSET UNIONS {f n | n IN UNIV}`) THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; GSYM REAL_ABS_BOUNDS] THEN
    REWRITE_TAC[GSYM FORALL_DROP; DROP_VEC; REAL_ARCH_SIMPLE]]);;

let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE_LOWDIM = prove
 (`!f:real^1->real^N s.
        2 <= dimindex(:N) /\ f absolutely_continuous_on s /\ is_interval s
        ==> negligible(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_EXTENDS_TO_CLOSURE)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
   `IMAGE (g:real^1->real^N)
        (closure s INTER UNIONS {interval[--vec n,vec n] | n IN (:num)})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTER_UNIONS; IMAGE_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
    MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; FORALL_IN_IMAGE; o_THM] THEN
    X_GEN_TAC `n:num` THEN DISCH_THEN(K ALL_TAC) THEN
    MP_TAC(ISPEC `closure s INTER interval[--vec n:real^1,vec n]`
     IS_INTERVAL_COMPACT) THEN
    SIMP_TAC[CLOSED_INTER_COMPACT; COMPACT_INTERVAL; CLOSED_CLOSURE] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IS_INTERVAL_CONVEX_1]) THEN
    ASM_SIMP_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CLOSURE; CONVEX_INTER;
                 CONVEX_INTERVAL; LEFT_IMP_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL THEN
    ASM_REWRITE_TAC[IS_INTERVAL_INTERVAL] THEN
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON THEN
    REWRITE_TAC[BOUNDED_INTERVAL] THEN
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `closure s:real^1->bool` THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> g x = f x) /\ s SUBSET c /\ u = UNIV
      ==> IMAGE f s SUBSET IMAGE g (c INTER u)`) THEN
    ASM_REWRITE_TAC[CLOSURE_SUBSET; UNIONS_GSPEC; EXTENSION] THEN
    REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_NEG; GSYM REAL_ABS_BOUNDS] THEN
    REWRITE_TAC[GSYM FORALL_DROP; DROP_VEC; REAL_ARCH_SIMPLE]]);;

let NEGLIGIBLE_RECTIFIABLE_PATH_IMAGE = prove
 (`!g:real^1->real^N.
        2 <= dimindex(:N) /\ rectifiable_path g ==> negligible(path_image g)`,
  REWRITE_TAC[rectifiable_path; path_image] THEN
  SIMP_TAC[NEGLIGIBLE_IMAGE_BOUNDED_VARIATION_INTERVAL;
           IS_INTERVAL_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Properties of Lebesgue measurable sets.                                   *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. measurable s ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lebesgue_measurable] THEN
  MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
  ASM_REWRITE_TAC[indicator; GSYM MEASURABLE_INTEGRABLE]);;

let NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. negligible s ==> lebesgue_measurable s`,
  SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let LEBESGUE_MEASURABLE_EMPTY = prove
 (`lebesgue_measurable {}`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_EMPTY]);;

let LEBESGUE_MEASURABLE_UNIV = prove
 (`lebesgue_measurable (:real^N)`,
  REWRITE_TAC[lebesgue_measurable; indicator; IN_UNIV; MEASURABLE_ON_CONST]);;

let LEBESGUE_MEASURABLE_COMPACT = prove
 (`!s:real^N->bool. compact s ==> lebesgue_measurable s`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_COMPACT]);;

let LEBESGUE_MEASURABLE_INTERVAL = prove
 (`(!a b:real^N. lebesgue_measurable(interval[a,b])) /\
   (!a b:real^N. lebesgue_measurable(interval(a,b)))`,
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_INTERVAL]);;

let LEBESGUE_MEASURABLE_INTER = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s INTER t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_INTER]);;

let LEBESGUE_MEASURABLE_UNION = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s UNION t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_UNION]);;

let LEBESGUE_MEASURABLE_DIFF = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ lebesgue_measurable t
        ==> lebesgue_measurable(s DIFF t)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_DIFF]);;

let LEBESGUE_MEASURABLE_COMPL = prove
 (`!s. lebesgue_measurable((:real^N) DIFF s) <=> lebesgue_measurable s`,
  MESON_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_UNIV;
            SET_RULE `UNIV DIFF (UNIV DIFF s) = s`]);;

let LEBESGUE_MEASURABLE_ON_SUBINTERVALS = prove
 (`!s. lebesgue_measurable s <=>
       !a b:real^N. lebesgue_measurable(s INTER interval[a,b])`,
  GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_INTER] THEN
  REWRITE_TAC[lebesgue_measurable] THEN DISCH_TAC THEN
  MATCH_MP_TAC INTEGRABLE_SUBINTERVALS_IMP_MEASURABLE THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. vec 1):real^N->real^1` THEN
  REWRITE_TAC[INTEGRABLE_CONST] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; indicator; IN_INTER] THEN MESON_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[indicator] THEN
    COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC; NORM_REAL; GSYM drop] THEN
    REAL_ARITH_TAC]);;

let LEBESGUE_MEASURABLE_CLOSED = prove
 (`!s:real^N->bool. closed s ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  ASM_SIMP_TAC[CLOSED_INTER_COMPACT; LEBESGUE_MEASURABLE_COMPACT;
               COMPACT_INTERVAL]);;

let LEBESGUE_MEASURABLE_OPEN = prove
 (`!s:real^N->bool. open s ==> lebesgue_measurable s`,
  REWRITE_TAC[OPEN_CLOSED] THEN REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED]);;

let LEBESGUE_MEASURABLE_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ lebesgue_measurable s
        ==> lebesgue_measurable t`,
  MESON_TAC[OPEN_IN_OPEN; LEBESGUE_MEASURABLE_OPEN;
            LEBESGUE_MEASURABLE_INTER]);;

let LEBESGUE_MEASURABLE_CLOSED_IN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ lebesgue_measurable s
        ==> lebesgue_measurable t`,
  MESON_TAC[CLOSED_IN_CLOSED; LEBESGUE_MEASURABLE_CLOSED;
            LEBESGUE_MEASURABLE_INTER]);;

let LEBESGUE_MEASURABLE_UNIONS = prove
 (`!f. FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
       ==> lebesgue_measurable (UNIONS f)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_UNIONS]);;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS = prove
 (`!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (UNIONS f)`,
  REWRITE_TAC[indicator; lebesgue_measurable; MEASURABLE_ON_UNIV] THEN
  REWRITE_TAC[MEASURABLE_ON_COUNTABLE_UNIONS]);;

let LEBESGUE_MEASURABLE_COUNTABLE_UNIONS_EXPLICIT = prove
 (`!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(UNIONS {s n | n IN (:num)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; IN_UNIV; NUM_COUNTABLE]);;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS = prove
 (`!f:(real^N->bool)->bool.
        COUNTABLE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INTERS_UNIONS; LEBESGUE_MEASURABLE_COMPL] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE;
               LEBESGUE_MEASURABLE_COMPL]);;

let LEBESGUE_MEASURABLE_COUNTABLE_INTERS_EXPLICIT = prove
 (`!s:num->real^N->bool.
        (!n. lebesgue_measurable(s n))
        ==> lebesgue_measurable(INTERS {s n | n IN (:num)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; COUNTABLE_IMAGE;
               NUM_COUNTABLE]);;

let LEBESGUE_MEASURABLE_INTERS = prove
 (`!f:(real^N->bool)->bool.
        FINITE f /\ (!s. s IN f ==> lebesgue_measurable s)
        ==> lebesgue_measurable (INTERS f)`,
  SIMP_TAC[LEBESGUE_MEASURABLE_COUNTABLE_INTERS; FINITE_IMP_COUNTABLE]);;

let GDELTA_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. gdelta s ==> lebesgue_measurable s`,
  GEN_TAC THEN REWRITE_TAC[gdelta] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_OPEN]);;

let FSIGMA_IMP_LEBESGUE_MEASURABLE = prove
 (`!s:real^N->bool. fsigma s ==> lebesgue_measurable s`,
  GEN_TAC THEN REWRITE_TAC[fsigma] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED]);;

let LEBESGUE_MEASURABLE_IFF_MEASURABLE = prove
 (`!s:real^N->bool. bounded s ==> (lebesgue_measurable s <=> measurable s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  REWRITE_TAC[lebesgue_measurable; indicator; MEASURABLE_INTEGRABLE] THEN
  SUBGOAL_THEN `?a b:real^N. s = s INTER interval[a,b]`
   (REPEAT_TCL CHOOSE_THEN SUBST1_TAC)
  THENL [REWRITE_TAC[SET_RULE `s = s INTER t <=> s SUBSET t`] THEN
         ASM_MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER; MESON[]
   `(if P x /\ Q x then a else b) =
    (if Q x then if P x then a else b else b)`] THEN
  REWRITE_TAC[MEASURABLE_ON_UNIV; INTEGRABLE_RESTRICT_UNIV] THEN
  STRIP_TAC THEN MATCH_MP_TAC
    MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. vec 1):real^N->real^1` THEN
  ASM_REWRITE_TAC[INTEGRABLE_CONST; NORM_REAL; DROP_VEC; GSYM drop] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN SIMP_TAC[DROP_VEC] THEN
  REAL_ARITH_TAC);;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS = prove
 (`!s:real^N->bool.
        lebesgue_measurable s <=>
        (!a b. measurable(s INTER interval[a,b]))`,
  MESON_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS;
            LEBESGUE_MEASURABLE_IFF_MEASURABLE;
            BOUNDED_INTER; BOUNDED_INTERVAL]);;

let LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS = prove
 (`!s:real^N->bool.
        lebesgue_measurable s <=>
        (!n. measurable(s INTER interval[--vec n,vec n]))`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV
   [LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS] THEN
  EQ_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a b:real^N. ?n. s INTER interval[a,b] =
                     ((s INTER interval[--vec n,vec n]) INTER interval[a,b])`
   (fun th -> ASM_MESON_TAC[th; MEASURABLE_INTERVAL; MEASURABLE_INTER]) THEN
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`interval[a:real^N,b]`; `vec 0:real^N`]
        BOUNDED_SUBSET_CBALL) THEN
  REWRITE_TAC[BOUNDED_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPEC `r:real` REAL_ARCH_SIMPLE) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `i SUBSET b ==> b SUBSET n ==> s INTER i = (s INTER n) INTER i`)) THEN
  REWRITE_TAC[SUBSET; IN_CBALL_0; IN_INTERVAL; VEC_COMPONENT;
              VECTOR_NEG_COMPONENT; GSYM REAL_ABS_BOUNDS]  THEN
  ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]);;

let MEASURABLE_ON_MEASURABLE_SUBSET = prove
 (`!f s t. s SUBSET t /\ f measurable_on t /\ measurable s
           ==> f measurable_on s`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
            MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let MEASURABLE_ON_CASES = prove
 (`!P f g:real^M->real^N s.
        lebesgue_measurable {x | P x} /\
        f measurable_on s /\ g measurable_on s
        ==> (\x. if P x then f x else g x) measurable_on s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. (if x IN s then if P x then (f:real^M->real^N) x else g x else vec 0) =
        (if x IN {x | P x} then if x IN s then f x else vec 0 else vec 0) +
        (if x IN (:real^M) DIFF {x | P x}
         then if x IN s then g x else vec 0 else vec 0)`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN REWRITE_TAC[IN_UNIV; IN_ELIM_THM; IN_DIFF] THEN
    MESON_TAC[VECTOR_ADD_LID; VECTOR_ADD_RID];
    MATCH_MP_TAC MEASURABLE_ON_ADD THEN
    CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_RESTRICT THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL]]);;

let LEBESGUE_MEASURABLE_JORDAN = prove
 (`!s:real^N->bool. negligible(frontier s) ==> lebesgue_measurable s`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
  MATCH_MP_TAC MEASURABLE_JORDAN THEN
  SIMP_TAC[BOUNDED_INTER; BOUNDED_INTERVAL] THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `frontier s UNION frontier(interval[a:real^N,b])` THEN
  ASM_REWRITE_TAC[FRONTIER_INTER_SUBSET; NEGLIGIBLE_UNION_EQ] THEN
  SIMP_TAC[NEGLIGIBLE_CONVEX_FRONTIER; CONVEX_INTERVAL]);;

let LEBESGUE_MEASURABLE_CONVEX = prove
 (`!s:real^N->bool. convex s ==> lebesgue_measurable s`,
  SIMP_TAC[LEBESGUE_MEASURABLE_JORDAN; NEGLIGIBLE_CONVEX_FRONTIER]);;

(* ------------------------------------------------------------------------- *)
(* Invariance theorems for Lebesgue measurability.                           *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_TRANSLATION = prove
 (`!f:real^M->real^N s a.
          f measurable_on (IMAGE (\x. a + x) s)
          ==> (\x. f(a + x)) measurable_on s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:num->real^M->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `IMAGE (\x:real^M. --a + x) k` THEN
  EXISTS_TAC `\n. (g:num->real^M->real^N) n o (\x. a + x)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    X_GEN_TAC `x:real^M` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `a + x:real^M`) THEN
    REWRITE_TAC[o_DEF; IN_IMAGE] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `x:real^N = --a + y <=> a + x = y`] THEN
    REWRITE_TAC[UNWIND_THM1; VECTOR_ARITH `a + x:real^N = a + y <=> x = y`]]);;

let MEASURABLE_ON_TRANSLATION_EQ = prove
 (`!f:real^M->real^N s a.
        (\x. f(a + x)) measurable_on s <=>
        f measurable_on (IMAGE (\x. a + x) s)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MEASURABLE_ON_TRANSLATION] THEN
  MP_TAC(ISPECL [`\x. (f:real^M->real^N) (a + x)`;
                 `IMAGE (\x:real^M. a + x) s`; `--a:real^M`]
    MEASURABLE_ON_TRANSLATION) THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; ETA_AX; IMAGE_ID; VECTOR_ARITH
   `--a + a + x:real^N = x /\ a + --a + x = x`]);;

let NEGLIGIBLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ negligible s /\ dimindex(:M) <= dimindex(:N)
        ==> negligible (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR]);;

let MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N h:real^N->real^P s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`,
  let lemma = prove
   (`!f:real^N->real^P g:real^M->real^N h s.
        dimindex(:M) = dimindex(:N) /\
        linear g /\ linear h /\ (!x. h(g x) = x) /\ (!x. g(h x) = x)
        ==> (f o g) measurable_on s ==> f measurable_on (IMAGE g s)`,
    REPEAT GEN_TAC THEN REWRITE_TAC[measurable_on] THEN
    STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool`
     (X_CHOOSE_THEN `G:num->real^M->real^P` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `IMAGE (g:real^M->real^N) k` THEN
    EXISTS_TAC `\n x. (G:num->real^M->real^P) n ((h:real^N->real^M) x)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_GEN THEN
      ASM_MESON_TAC[LE_REFL];
      GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      ASM_MESON_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `(h:real^N->real^M) y`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[o_THM] THEN
      AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[]]) in
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; FUN_EQ_THM; o_THM; I_THM] THEN
  X_GEN_TAC `g:real^N->real^M` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^N. (f:real^M->real^N) ((g:real^N->real^M) y) = y`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (f:real^M->real^N) UNIV = UNIV` MP_TAC THENL
     [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
    ASM_MESON_TAC[LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN];
    ALL_TAC] THEN
  EQ_TAC THENL [ASM_MESON_TAC[lemma]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`(h:real^N->real^P) o (f:real^M->real^N)`;
                 `g:real^N->real^M`; `f:real^M->real^N`;
                 `IMAGE (f:real^M->real^N) s`] lemma) THEN
  ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID; ETA_AX] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

let MEASURABLE_ON_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N h:real^N->real^P s.
        linear f /\ (!x y. f x = f y ==> x = y)
        ==> ((h o f) measurable_on s <=> h measurable_on (IMAGE f s))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN THEN
  ASM_MESON_TAC[]);;

let LEBESGUE_MEASURABLE_TRANSLATION = prove
 (`!a:real^N s.
     lebesgue_measurable (IMAGE (\x. a + x) s) <=>
     lebesgue_measurable s`,
  ONCE_REWRITE_TAC[LEBESGUE_MEASURABLE_ON_SUBINTERVALS] THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_IFF_MEASURABLE;
           BOUNDED_INTER; BOUNDED_INTERVAL] THEN
  GEOM_TRANSLATE_TAC[]);;

add_translation_invariants [LEBESGUE_MEASURABLE_TRANSLATION];;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ = prove
 (`!f:real^N->real^N s.
        linear f /\ (!x y. f x = f y ==> x = y)
         ==> (lebesgue_measurable (IMAGE f s) <=>
              lebesgue_measurable s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC o
        MATCH_MP LINEAR_BIJECTIVE_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[lebesgue_measurable] THEN MP_TAC(ISPECL
   [`g:real^N->real^N`; `indicator(s:real^N->bool)`; `(:real^N)`]
   MEASURABLE_ON_LINEAR_IMAGE_EQ) THEN
  ASM_REWRITE_TAC[indicator; o_DEF] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; MATCH_MP_TAC EQ_IMP] THEN
  BINOP_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
    AP_THM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    AP_TERM_TAC THEN ASM SET_TAC[]]);;

add_linear_invariants [LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ];;

(* ------------------------------------------------------------------------- *)
(* Various common equivalent forms of function measurability.                *)
(* ------------------------------------------------------------------------- *)

let (MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT,
     MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT) = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k < a}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        ?g. (!n. (g n) measurable_on (:real^M)) /\
            (!n. FINITE(IMAGE (g n) (:real^M))) /\
            (!x. ((\n. g n x) --> f x) sequentially))`,
  let lemma0 = prove
   (`!f:real^M->real^1 n m.
          integer m /\
          m / &2 pow n <= drop(f x) /\
          drop(f x) < (m + &1) / &2 pow n /\
          abs(m) <= &2 pow (2 * n)
          ==> vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                   (\k. k / &2 pow n %
                        indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                              drop(f y) < (k + &1) / &2 pow n}
                                  x) =
              lift(m / &2 pow n)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {m} (\k. k / &2 pow n %
                    indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(k:real = m)` THEN ASM_SIMP_TAC[REAL_EQ_INTEGERS] THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VSUM_SING; indicator; IN_ELIM_THM; LIFT_EQ_CMUL]]) in
  let lemma1 = prove
   (`!f:real^M->real^1.
          (!a b. lebesgue_measurable {x | a <= drop(f x) /\ drop(f x) < b})
          ==> ?g. (!n. (g n) measurable_on (:real^M)) /\
                  (!n. FINITE(IMAGE (g n) (:real^M))) /\
                  (!x. ((\n. g n x) --> f x) sequentially)`,
    REPEAT STRIP_TAC THEN
    EXISTS_TAC
     `\n x. vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                 (\k. k / &2 pow n %
                      indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                            drop(f y) < (k + &1) / &2 pow n}
                                x)` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
      REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; IN_ELIM_THM] THEN
      GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
      ASM_REWRITE_TAC[GSYM lebesgue_measurable; ETA_AX];
      X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (\k. lift(k / &2 pow n))
                        {k | integer k /\ abs(k) <= &2 pow (2 * n)}` THEN
      CONJ_TAC THENL
       [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_IMAGE] THEN
      ASM_CASES_TAC
       `?k. integer k /\ abs k <= &2 pow (2 * n) /\
            k / &2 pow n <= drop(f(x:real^M)) /\
            drop(f x) < (k + &1) / &2 pow n`
      THENL
       [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
        X_GEN_TAC `m:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        MATCH_MP_TAC lemma0 THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `&0` THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; INTEGER_CLOSED; REAL_ABS_NUM] THEN
        SIMP_TAC[REAL_POW_LE; REAL_POS; real_div; REAL_MUL_LZERO] THEN
        REWRITE_TAC[LIFT_NUM; GSYM real_div] THEN
        MATCH_MP_TAC VSUM_EQ_0 THEN
        X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
        REWRITE_TAC[indicator; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      MP_TAC(ISPECL [`&2`; `abs(drop((f:real^M->real^1) x))`]
          REAL_ARCH_POW) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
      X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
      REWRITE_TAC[REAL_POW_INV] THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `N2:num` MP_TAC) THEN
      SUBST1_TAC(REAL_ARITH `inv(&2 pow N2) = &1 / &2 pow N2`) THEN
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN DISCH_TAC THEN
      EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
      ABBREV_TAC `m = floor(&2 pow n * drop(f(x:real^M)))` THEN
      SUBGOAL_THEN `dist(lift(m / &2 pow n),(f:real^M->real^1) x) < e`
      MP_TAC THENL
       [REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
        MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&2 pow n)` THEN
        REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
        SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; GSYM REAL_ABS_NZ;
                 REAL_OF_NUM_EQ; ARITH] THEN
        MATCH_MP_TAC(REAL_ARITH
         `x <= y /\ y < x + &1 /\ &1 <= z ==> abs(x - y) < z`) THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `e * &2 pow N2` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POW; REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC(NORM_ARITH
         `x:real^1 = y ==> dist(y,z) < e ==> dist(x,z) < e`) THEN
        MATCH_MP_TAC lemma0 THEN
        SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
        EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
        SIMP_TAC[REAL_ABS_BOUNDS; REAL_LE_FLOOR; REAL_FLOOR_LE;
                 INTEGER_CLOSED] THEN
        MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> --e <= x /\ x - &1 < e`) THEN
        REWRITE_TAC[MULT_2; REAL_POW_ADD; REAL_ABS_MUL; REAL_ABS_POW;
                    REAL_ABS_NUM] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
         `x < e ==> e <= d ==> x <= d`))] THEN
      MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      ASM_ARITH_TAC]) in
  MATCH_MP_TAC(MESON[]
   `(!f. P f ==> Q f) /\ (!f. Q f ==> R f) /\ (!f. R f ==> P f)
    ==> (!f. P f <=> Q f) /\ (!f. P f <=> R f)`) THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `g:real^M->real^N` THEN DISCH_TAC THEN
    ABBREV_TAC `f:real^M->real^N = \x. --(g x)` THEN
    SUBGOAL_THEN `(f:real^M->real^N) measurable_on (:real^M)` ASSUME_TAC THENL
     [EXPAND_TAC "f" THEN MATCH_MP_TAC MEASURABLE_ON_NEG THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM REAL_LT_NEG2] THEN X_GEN_TAC `a:real` THEN
    SPEC_TAC(`--a:real`,`a:real`) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    SIMP_TAC[GSYM VECTOR_NEG_COMPONENT] THEN DISCH_THEN(K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:num` o
      GEN_REWRITE_RULE I [MEASURABLE_ON_COMPONENTWISE]) THEN
    ASM_REWRITE_TAC[] THEN  REPEAT STRIP_TAC THEN
    MP_TAC(GEN `d:real` (ISPECL
     [`\x. lift ((f:real^M->real^N) x$k)`;
       `(\x. lift a + (lambda i. d)):real^M->real^1`;
      `(:real^M)`] MEASURABLE_ON_MIN)) THEN
    ASM_REWRITE_TAC[MEASURABLE_ON_CONST] THEN
    DISCH_THEN(fun th ->
      MP_TAC(GEN `n:num` (ISPEC `&n + &1` (MATCH_MP MEASURABLE_ON_CMUL
        (MATCH_MP MEASURABLE_ON_SUB
       (CONJ (SPEC `inv(&n + &1)` th) (SPEC `&0` th))))))) THEN
    REWRITE_TAC[lebesgue_measurable; indicator] THEN
    DISCH_THEN(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
          MEASURABLE_ON_LIMIT)) THEN
    EXISTS_TAC `{}:real^M->bool` THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; IN_DIFF; IN_UNIV; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SIMP_TAC[LIM_SEQUENTIALLY; DIST_REAL; VECTOR_MUL_COMPONENT;
             VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT;
             LAMBDA_BETA; DIMINDEX_1; ARITH] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP; REAL_ADD_RID] THEN
    SIMP_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`; REAL_ARITH
     `&0 < d ==> (min x (a + d) - min x a =
                  if x <= a then &0 else if x <= a + d then x - a else d)`] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `a < (f:real^M->real^N) x $k` THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[REAL_ARITH `(x:real^N)$k <= a <=> ~(a < x$k)`] THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO; DROP_VEC; REAL_SUB_REFL; REAL_ABS_NUM] THEN
    MP_TAC(SPEC `((f:real^M->real^N) x)$k - a` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[REAL_SUB_LT] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `a + inv(&n + &1) < ((f:real^M->real^N) x)$k` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `N < f - a ==> n <= N ==> a + n < f`)) THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_ARITH `~(&n + &1 = &0)`] THEN
      ASM_REAL_ARITH_TAC];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. 1 <= k /\ k <= dimindex(:N)
          ==> ?g. (!n. (g n) measurable_on (:real^M)) /\
                  (!n. FINITE(IMAGE (g n) (:real^M))) /\
                  (!x. ((\n. g n x) --> lift((f x:real^N)$k)) sequentially)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC lemma1 THEN
      ASM_SIMP_TAC[LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
      REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | Q x} DIFF {x | ~P x}`] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
      ASM_SIMP_TAC[REAL_NOT_LE];
      GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV) [RIGHT_IMP_EXISTS_THM]] THEN
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->num->real^M->real^1` MP_TAC) THEN
    REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    EXISTS_TAC
      `\n x. (lambda k. drop((g:num->num->real^M->real^1) k n x)):real^N` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN ONCE_REWRITE_TAC[MEASURABLE_ON_COMPONENTWISE] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX];
      X_GEN_TAC `n:num` THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:real^N | !i. 1 <= i /\ i <= dimindex(:N)
                        ==> lift(x$i) IN IMAGE (g i (n:num)) (:real^M)}` THEN
      ASM_SIMP_TAC[GSYM IN_IMAGE_LIFT_DROP; SET_RULE `{x | x IN s} = s`;
                   FINITE_IMAGE; FINITE_CART] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
      SIMP_TAC[IN_IMAGE; IN_UNIV; LAMBDA_BETA; DROP_EQ] THEN MESON_TAC[];
      X_GEN_TAC `x:real^M` THEN ONCE_REWRITE_TAC[LIM_COMPONENTWISE_LIFT] THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX]];
    X_GEN_TAC `f:real^M->real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
    MAP_EVERY EXISTS_TAC [`g:num->real^M->real^N`; `{}:real^M->bool`] THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k >= a}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x >= a <=> ~(x < a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k > a}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[REAL_NEG_NEG] `(!x. P x) <=> (!x:real. P(--x))`] THEN
  REWRITE_TAC[real_gt; VECTOR_NEG_COMPONENT; REAL_LT_NEG2]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a k. 1 <= k /\ k <= dimindex(:N)
              ==> lebesgue_measurable {x | f(x)$k <= a}`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x <= a <=> ~(x > a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]);;

let (MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL,
    MEASURABLE_ON_PREIMAGE_OPEN) = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a b. lebesgue_measurable {x | f(x) IN interval(a,b)}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. open t ==> lebesgue_measurable {x | f(x) IN t})`,
  let ulemma = prove
   (`{x | f x IN UNIONS D} = UNIONS {{x | f(x) IN s} | s IN D}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  MATCH_MP_TAC(MESON[]
   `(!f. P f ==> Q f) /\ (!f. Q f ==> R f) /\ (!f. R f ==> P f)
    ==> (!f. P f <=> Q f) /\ (!f. P f <=> R f)`) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN SUBGOAL_THEN
    `{x | (f:real^M->real^N) x IN interval(a,b)} =
        INTERS {{x | a$k < f(x)$k} | k IN 1..dimindex(:N)} INTER
        INTERS {{x | (--b)$k < --(f(x))$k} | k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[IN_INTERVAL; GSYM IN_NUMSEG] THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_LT_NEG2] THEN
      REWRITE_TAC[INTERS_GSPEC] THEN SET_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
      CONJ_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
         [MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]);
        FIRST_X_ASSUM(MP_TAC o MATCH_MP MEASURABLE_ON_NEG) THEN
        REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT]] THEN
      ASM_SIMP_TAC[real_gt]];
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_OPEN_INTERVALS) THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[ulemma] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM];
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE
      `{x:real^M | (f x)$k < a} = {x | f x IN {y:real^N | y$k < a}}`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT]]);;

let MEASURABLE_ON_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !t. closed t ==> lebesgue_measurable {x | f(x) IN t}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL; closed] THEN
  REWRITE_TAC[SET_RULE
   `UNIV DIFF {x | f x IN t} = {x | f x IN (UNIV DIFF t)}`] THEN
  REWRITE_TAC[MESON[SET_RULE `UNIV DIFF (UNIV DIFF s) = s`]
   `(!s. P(UNIV DIFF s)) <=> (!s. P s)`] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN]);;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL = prove
 (`!f:real^M->real^N.
         f measurable_on (:real^M) <=>
         !a b. lebesgue_measurable {x | f(x) IN interval[a,b]}`,
  let ulemma = prove
   (`{x | f x IN UNIONS D} = UNIONS {{x | f(x) IN s} | s IN D}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  GEN_TAC THEN EQ_TAC THENL
   [SIMP_TAC[MEASURABLE_ON_PREIMAGE_CLOSED; CLOSED_INTERVAL]; DISCH_TAC] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
  DISCH_THEN(X_CHOOSE_THEN `D:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ONCE_REWRITE_TAC[ulemma] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_SIMP_TAC[LEFT_IMP_EXISTS_THM]);;

let LEBESGUE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N t.
        f measurable_on (:real^M) /\ open t
        ==> lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[MEASURABLE_ON_PREIMAGE_OPEN]);;

let LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N t.
        f measurable_on (:real^M) /\ closed t
        ==> lebesgue_measurable {x | f(x) IN t}`,
  SIMP_TAC[MEASURABLE_ON_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k <= (a:real^N)$k}`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | !k. P k ==> f x$k <= a k} =
                     {x | f(x) IN {y | !k. P k ==> y$k <= a k}}`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
        [MEASURABLE_ON_PREIMAGE_CLOSED]) THEN
    REWRITE_TAC[CLOSED_INTERVAL_LEFT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{x | (f:real^M->real^N) x$k <= a} =
      UNIONS
       {{x | !j. 1 <= j /\ j <= dimindex(:N) ==>
                 f x$j <= ((lambda i. if i = k then a else &n):real^N)$j} |
        n IN (:num)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN SIMP_TAC[LAMBDA_BETA] THEN
      SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN GEN_TAC THEN
      ASM_CASES_TAC `(y:real^N)$k <= a` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC
       `sup {(y:real^N)$j | j IN 1..dimindex(:N)}` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[REAL_SUP_LE_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1]  THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
                   FORALL_IN_IMAGE]]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k >= (a:real^N)$k}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_ORTHANT_LE] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[VECTOR_NEG_NEG] `(!x:real^N. P x) <=> (!x. P(--x))`] THEN
  REWRITE_TAC[REAL_ARITH `--x <= --y <=> x >= y`; VECTOR_NEG_COMPONENT]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k < (a:real^N)$k}`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN
    ONCE_REWRITE_TAC[SET_RULE `{x | !k. P k ==> f x$k < a k} =
                     {x | f(x) IN {y | !k. P k ==> y$k < a k}}`] THEN
    FIRST_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I
        [MEASURABLE_ON_PREIMAGE_OPEN]) THEN
    REWRITE_TAC[OPEN_INTERVAL_LEFT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `{x | (f:real^M->real^N) x$k < a} =
      UNIONS
       {{x | !j. 1 <= j /\ j <= dimindex(:N) ==>
                 f x$j < ((lambda i. if i = k then a else &n):real^N)$j} |
        n IN (:num)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN SIMP_TAC[LAMBDA_BETA] THEN
      SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN GEN_TAC THEN
      ASM_CASES_TAC `(y:real^N)$k < a` THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPEC
       `&1 + sup {(y:real^N)$j | j IN 1..dimindex(:N)}` REAL_ARCH_SIMPLE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[REAL_ARITH `&1 + x <= y <=> x <= y - &1`] THEN
      SIMP_TAC[REAL_SUP_LE_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1]  THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN
      ASM_MESON_TAC[REAL_ARITH `x <= y - &1 ==> x < y`];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
                   FORALL_IN_IMAGE]]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !a. lebesgue_measurable {x | !k. 1 <= k /\ k <= dimindex(:N)
                                         ==> f(x)$k > (a:real^N)$k}`,
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_ORTHANT_LT] THEN
  GEN_REWRITE_TAC LAND_CONV
   [MESON[VECTOR_NEG_NEG] `(!x:real^N. P x) <=> (!x. P(--x))`] THEN
  REWRITE_TAC[REAL_ARITH `--x < --y <=> x > y`; VECTOR_NEG_COMPONENT]);;

let MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT_INCREASING = prove
 (`!f:real^N->real^1.
        f measurable_on (:real^N) /\ (!x. &0 <= drop(f x)) <=>
        ?g. (!n x. &0 <= drop(g n x) /\ drop(g n x) <= drop(f x)) /\
            (!n x. drop(g n x) <= drop(g(SUC n) x)) /\
            (!n. (g n) measurable_on (:real^N)) /\
            (!n. FINITE(IMAGE (g n) (:real^N))) /\
            (!x. ((\n. g n x) --> f x) sequentially)`,
  let lemma = prove
   (`!f:real^M->real^1 n m.
          integer m /\
          m / &2 pow n <= drop(f x) /\
          drop(f x) < (m + &1) / &2 pow n /\
          abs(m) <= &2 pow (2 * n)
          ==> vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
                   (\k. k / &2 pow n %
                        indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                              drop(f y) < (k + &1) / &2 pow n}
                                  x) =
              lift(m / &2 pow n)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
     `vsum {m} (\k. k / &2 pow n %
                    indicator {y:real^M | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[SING_SUBSET; IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      ASM_REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(k:real = m)` THEN ASM_SIMP_TAC[REAL_EQ_INTEGERS] THEN
      POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[VSUM_SING; indicator; IN_ELIM_THM; LIFT_EQ_CMUL]]) in
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [STRIP_TAC;
    DISCH_THEN(fun th -> CONJ_TAC THEN MP_TAC th) THENL
     [GEN_REWRITE_TAC RAND_CONV [MEASURABLE_ON_SIMPLE_FUNCTION_LIMIT] THEN
      MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[];
      MESON_TAC[REAL_LE_TRANS]]] THEN
  SUBGOAL_THEN
   `!a b. lebesgue_measurable {x:real^N | a <= drop(f x) /\ drop(f x) < b}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[SET_RULE `{x | P x /\ Q x} = {x | Q x} DIFF {x | ~P x}`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN REWRITE_TAC[REAL_NOT_LE] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I
     [MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT]) THEN
    SIMP_TAC[drop; FORALL_1; DIMINDEX_1];
    FIRST_X_ASSUM(K ALL_TAC o GEN_REWRITE_RULE I [measurable_on])] THEN
  REWRITE_TAC[FORALL_AND_THM; GSYM CONJ_ASSOC] THEN
  MATCH_MP_TAC(MESON[]
   `(!x. P x /\ R x ==> Q x) /\ (?x. P x /\ R x)
    ==> (?x. P x /\ Q x /\ R x)`) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `g:num->real^N->real^1` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^N`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_SEQUENTIALLY] o
        SPEC `x:real^N`) THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    DISCH_THEN(MP_TAC o SPEC `drop((g:num->real^N->real^1) n x - f x)`) THEN
    ASM_REWRITE_TAC[DROP_SUB; REAL_SUB_LT; NOT_EXISTS_THM] THEN
    X_GEN_TAC `N:num` THEN DISCH_THEN(MP_TAC o SPEC `N + n:num`) THEN
    REWRITE_TAC[LE_ADD; DIST_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH
     `f < g /\ g <= g' ==> ~(abs(g' - f) < g - f)`) THEN
    ASM_REWRITE_TAC[] THEN MP_TAC(ARITH_RULE `n:num <= N + n`) THEN
    SPEC_TAC(`N + n:num`,`m:num`) THEN SPEC_TAC(`n:num`,`n:num`) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC
   `\n x. vsum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
               (\k. k / &2 pow n %
                    indicator {y:real^N | k / &2 pow n <= drop(f y) /\
                                          drop(f y) < (k + &1) / &2 pow n}
                              x)` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `!n. FINITE {k | integer k /\ abs k <= &2 pow (2 * n)}`
  ASSUME_TAC THENL
   [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[VSUM_REAL; LIFT_DROP; o_DEF] THEN
    MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    X_GEN_TAC `k:real` THEN STRIP_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
    ASM_CASES_TAC `&0 <= k` THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
      REWRITE_TAC[DROP_INDICATOR_POS_LE];
      MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
      REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN REWRITE_TAC[indicator] THEN
      COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
      MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
      REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
      ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; REAL_MUL_LZERO; INTEGER_CLOSED] THEN
      ASM_REAL_ARITH_TAC];
    REPEAT GEN_TAC THEN SIMP_TAC[VSUM_REAL; LIFT_DROP; o_DEF; DROP_CMUL] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {k | integer k /\ abs(k) <= &2 pow (2 * n)}
          (\k. k / &2 pow n *
           (drop(indicator {y:real^N | k / &2 pow n <= drop(f y) /\
                         drop(f y) < (k + &1 / &2) / &2 pow n} x) +
            drop(indicator {y:real^N | (k + &1 / &2) / &2 pow n <= drop(f y) /\
                             drop(f y) < (k + &1) / &2 pow n} x)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      X_GEN_TAC `k:real` THEN STRIP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[indicator; IN_ELIM_THM] THEN
      REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[DROP_VEC]) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
     [REAL_ARITH `x / y = (&2 * x) * inv(&2) * inv(y)`] THEN
    REWRITE_TAC[GSYM REAL_INV_MUL] THEN REWRITE_TAC[GSYM real_div] THEN
    REWRITE_TAC[GSYM(CONJUNCT2 real_pow);
                REAL_ARITH `&2 * (k + &1 / &2) = &2 * k + &1`;
                REAL_ARITH `&2 * (k + &1) = (&2 * k + &1) + &1`] THEN
    ASM_SIMP_TAC[REAL_ADD_LDISTRIB; SUM_ADD]  THEN
    MATCH_MP_TAC(REAL_ARITH
     `!g. sum s f <= sum s g /\ a + sum s g <= b ==> a + sum s f <= b`) THEN
    EXISTS_TAC
     `\k. (&2 * k + &1) / &2 pow SUC n *
          drop
          (indicator
           {y | (&2 * k + &1) / &2 pow SUC n <= drop ((f:real^N->real^1) y) /\
                drop (f y) < ((&2 * k + &1) + &1) / &2 pow SUC n} x)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      SIMP_TAC[DROP_INDICATOR_POS_LE; REAL_LE_DIV2_EQ; REAL_LT_POW2] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `\x. &2 * x` SUM_IMAGE) THEN
    MP_TAC(ISPEC `\x. &2 * x + &1` SUM_IMAGE) THEN
    REWRITE_TAC[REAL_EQ_ADD_RCANCEL; REAL_EQ_MUL_LCANCEL] THEN
    REWRITE_TAC[REAL_OF_NUM_EQ; ARITH; IMP_CONJ; o_DEF] THEN
    REPEAT(DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th])) THEN
    W(MP_TAC o PART_MATCH (rand o rand) SUM_UNION o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[FINITE_IMAGE; SET_RULE
       `DISJOINT (IMAGE f s) (IMAGE g s) <=>
        !x. x IN s ==> !y. y IN s ==> ~(f x = g y)`] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:real` THEN STRIP_TAC THEN
      X_GEN_TAC `j:real` THEN STRIP_TAC THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
       `&2 * x = &2 * y + &1 ==> &2 * abs(x - y) = &1`)) THEN
      SUBGOAL_THEN `integer(i - j)` MP_TAC THENL
       [ASM_SIMP_TAC[INTEGER_CLOSED]; REWRITE_TAC[integer]] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_EQ] THEN
      DISCH_THEN(MP_TAC o AP_TERM `EVEN`) THEN
      REWRITE_TAC[EVEN_MULT; ARITH];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC SUM_SUBSET THEN
    ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> x IN u) /\ (!x. x IN t ==> x IN u)
        ==> !x. x IN (s UNION t) DIFF u ==> P x`) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      SIMP_TAC[INTEGER_CLOSED; ARITH_RULE `2 * SUC n = 2 + 2 * n`] THEN
      REWRITE_TAC[REAL_POW_ADD] THEN
      CONJ_TAC THENL [REAL_ARITH_TAC; REPEAT STRIP_TAC] THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x) <= n /\ &1 <= n ==> abs(&2 * x + &1) <= &2 pow 2 * n`) THEN
      ASM_REWRITE_TAC[REAL_LE_POW2];
      X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF] THEN
      STRIP_TAC THEN REWRITE_TAC[DROP_CMUL] THEN
      ASM_CASES_TAC `&0 <= k` THENL
       [MATCH_MP_TAC REAL_LE_MUL THEN
        ASM_SIMP_TAC[REAL_LE_DIV; REAL_POW_LE; REAL_POS] THEN
        REWRITE_TAC[DROP_INDICATOR_POS_LE];
        MATCH_MP_TAC(REAL_ARITH `x = &0 ==> &0 <= x`) THEN
        REWRITE_TAC[REAL_ENTIRE] THEN DISJ2_TAC THEN
        REWRITE_TAC[indicator] THEN
        COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC] THEN
        FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_ELIM_THM]) THEN
        MATCH_MP_TAC(TAUT `~b ==> a /\ b ==> c`) THEN
        REWRITE_TAC[REAL_NOT_LT] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&0` THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_POW2] THEN
        ASM_SIMP_TAC[GSYM REAL_LT_INTEGERS; REAL_MUL_LZERO;
                     INTEGER_CLOSED] THEN
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_VSUM THEN
    REWRITE_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; IN_ELIM_THM] THEN
    GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
    ASM_REWRITE_TAC[GSYM lebesgue_measurable; ETA_AX];
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\k. lift(k / &2 pow n))
                      {k | integer k /\ abs(k) <= &2 pow (2 * n)}` THEN
    CONJ_TAC THENL
     [SIMP_TAC[REAL_ABS_BOUNDS; FINITE_INTSEG; FINITE_IMAGE];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    ASM_CASES_TAC
     `?k. integer k /\ abs k <= &2 pow (2 * n) /\
          k / &2 pow n <= drop(f(x:real^N)) /\
          drop(f x) < (k + &1) / &2 pow n`
    THENL
     [FIRST_X_ASSUM(fun th -> MP_TAC th THEN MATCH_MP_TAC MONO_EXISTS) THEN
      X_GEN_TAC `m:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
      MATCH_MP_TAC lemma THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; INTEGER_CLOSED; REAL_ABS_NUM] THEN
      SIMP_TAC[REAL_POW_LE; REAL_POS; real_div; REAL_MUL_LZERO] THEN
      REWRITE_TAC[LIFT_NUM; GSYM real_div] THEN
      MATCH_MP_TAC VSUM_EQ_0 THEN
      X_GEN_TAC `k:real` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      REWRITE_TAC[VECTOR_MUL_EQ_0] THEN DISJ2_TAC THEN
      REWRITE_TAC[indicator; IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
    MP_TAC(ISPECL [`&2`; `abs(drop((f:real^N->real^1) x))`]
        REAL_ARCH_POW) THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; DISCH_THEN(X_CHOOSE_TAC `N1:num`)] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    REWRITE_TAC[REAL_POW_INV] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `N2:num` MP_TAC) THEN
    SUBST1_TAC(REAL_ARITH `inv(&2 pow N2) = &1 / &2 pow N2`) THEN
    SIMP_TAC[REAL_LT_LDIV_EQ; REAL_LT_POW2] THEN DISCH_TAC THEN
    EXISTS_TAC `MAX N1 N2` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    ABBREV_TAC `m = floor(&2 pow n * drop(f(x:real^N)))` THEN
    SUBGOAL_THEN `dist(lift(m / &2 pow n),(f:real^N->real^1) x) < e`
    MP_TAC THENL
     [REWRITE_TAC[DIST_REAL; GSYM drop; LIFT_DROP] THEN
      MATCH_MP_TAC REAL_LT_LCANCEL_IMP THEN EXISTS_TAC `abs(&2 pow n)` THEN
      REWRITE_TAC[GSYM REAL_ABS_MUL; REAL_SUB_LDISTRIB] THEN
      SIMP_TAC[REAL_DIV_LMUL; REAL_POW_EQ_0; GSYM REAL_ABS_NZ;
               REAL_OF_NUM_EQ; ARITH] THEN
      MATCH_MP_TAC(REAL_ARITH
       `x <= y /\ y < x + &1 /\ &1 <= z ==> abs(x - y) < z`) THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `e * &2 pow N2` THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POW; REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(NORM_ARITH
       `x:real^1 = y ==> dist(y,z) < e ==> dist(x,z) < e`) THEN
      MATCH_MP_TAC lemma THEN
      SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LT_RDIV_EQ; REAL_LT_POW2] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
      EXPAND_TAC "m" THEN REWRITE_TAC[FLOOR] THEN
      SIMP_TAC[REAL_ABS_BOUNDS; REAL_LE_FLOOR; REAL_FLOOR_LE;
               INTEGER_CLOSED] THEN
      MATCH_MP_TAC(REAL_ARITH `abs(x) <= e ==> --e <= x /\ x - &1 < e`) THEN
      REWRITE_TAC[MULT_2; REAL_POW_ADD; REAL_ABS_MUL; REAL_ABS_POW;
                  REAL_ABS_NUM] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN SIMP_TAC[REAL_POW_LE; REAL_POS] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `x < e ==> e <= d ==> x <= d`))] THEN
    MATCH_MP_TAC REAL_POW_MONO THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* More connections with measure where Lebesgue measurability is useful.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t /\ s SUBSET t
        ==> measurable s`,
  REWRITE_TAC[lebesgue_measurable; MEASURABLE_INTEGRABLE] THEN
  REWRITE_TAC[indicator] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
  EXISTS_TAC `(\x. if x IN t then vec 1 else vec 0):real^N->real^1` THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN GEN_TAC THEN
  REPEAT(COND_CASES_TAC THEN
         ASM_REWRITE_TAC[DROP_VEC; NORM_REAL; GSYM drop]) THEN
  REWRITE_TAC[REAL_ABS_NUM; REAL_LE_REFL; REAL_POS] THEN ASM SET_TAC[]);;

let MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE = prove
 (`!s t:real^N->bool.
        lebesgue_measurable s /\ measurable t ==> measurable(s INTER t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `t:real^N->bool` THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_INTER; MEASURABLE_IMP_LEBESGUE_MEASURABLE;
               INTER_SUBSET]);;

let MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE = prove
 (`!s t:real^N->bool.
        measurable s /\ lebesgue_measurable t ==> measurable(s INTER t)`,
  MESON_TAC[INTER_COMM; MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE]);;

let MEASURABLE_INTER_HALFSPACE_LE = prove
 (`!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i <= a})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_COMPONENT_LE; LEBESGUE_MEASURABLE_CLOSED]);;

let MEASURABLE_INTER_HALFSPACE_GE = prove
 (`!s a i. measurable s ==> measurable(s INTER {x:real^N | x$i >= a})`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:N) /\ !z:real^N. z$i = z$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE THEN
  ASM_SIMP_TAC[CLOSED_HALFSPACE_COMPONENT_GE; LEBESGUE_MEASURABLE_CLOSED]);;

let MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE = prove
 (`!s t. measurable s /\ lebesgue_measurable t ==> measurable(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
  ASM_SIMP_TAC[MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE;
                LEBESGUE_MEASURABLE_COMPL]);;

let MEASURABLE_OPEN_IN = prove
 (`!s t:real^N->bool.
        open_in (subtopology euclidean s) t /\ measurable s
        ==> measurable t`,
  MESON_TAC[MEASURABLE_LEBESGUE_MEASURABLE_SUBSET; OPEN_IN_IMP_SUBSET;
    LEBESGUE_MEASURABLE_OPEN_IN; MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

let MEASURABLE_CLOSED_IN = prove
 (`!s t:real^N->bool.
        closed_in (subtopology euclidean s) t /\ measurable s
        ==> measurable t`,
  MESON_TAC[MEASURABLE_LEBESGUE_MEASURABLE_SUBSET; CLOSED_IN_IMP_SUBSET;
    LEBESGUE_MEASURABLE_CLOSED_IN; MEASURABLE_IMP_LEBESGUE_MEASURABLE]);;

(* ------------------------------------------------------------------------- *)
(* Negigibility of set with uncountably many disjoint translates.            *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_DISJOINT_TRANSLATES = prove
 (`!s:real^N->bool k z.
        lebesgue_measurable s /\ z limit_point_of k /\
        pairwise (\a b. DISJOINT (IMAGE (\x. a + x) s) (IMAGE (\x. b + x) s)) k
        ==> negligible s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  ABBREV_TAC `t = s INTER interval[a:real^N,b]` THEN
  SUBGOAL_THEN `measurable(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
                  MEASURABLE_INTERVAL; INTER_COMM];
    ALL_TAC] THEN
  SUBGOAL_THEN `bounded(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[BOUNDED_INTER; BOUNDED_INTERVAL]; ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_EQ_0] THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= x /\ ~(&0 < x) ==> x = &0`) THEN
  ASM_SIMP_TAC[MEASURE_POS_LE] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1` o
    GEN_REWRITE_RULE I [LIMPT_INFINITE_CBALL]) THEN
  REWRITE_TAC[REAL_LT_01] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o
    SPEC `measure(IMAGE (\x:real^N. z + x) (interval[a - vec 1,b + vec 1]))` o
    MATCH_MP REAL_ARCH) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `k INTER cball(z:real^N,&1)`]
    CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INFINITE]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET_INTER; LEFT_IMP_EXISTS_THM; REAL_NOT_LT] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LE_TRANS
   `measure(UNIONS(IMAGE (\a. IMAGE (\x:real^N. a + x) t) u))` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  SUBGOAL_THEN
   `UNIONS(IMAGE (\a. IMAGE (\x:real^N. a + x) t) u) has_measure
    &n * measure(t:real^N->bool)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`\a. IMAGE (\x:real^N. a + x) t`; `u:real^N->bool`]
        HAS_MEASURE_DISJOINT_UNIONS_IMAGE) THEN
    ASM_SIMP_TAC[MEASURABLE_TRANSLATION_EQ; MEASURE_TRANSLATION;
                 SUM_CONST] THEN
    DISCH_THEN MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM SET_TAC[];
    REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN STRIP_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; MATCH_MP_TAC MEASURE_SUBSET] THEN
  ASM_REWRITE_TAC[MEASURABLE_TRANSLATION_EQ; MEASURABLE_INTERVAL] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE; IMP_CONJ;
              RIGHT_FORALL_IMP_THM] THEN
  X_GEN_TAC `e:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_IMAGE; UNWIND_THM1; VECTOR_ARITH
   `d + e:real^N = z + y <=> e + d - z = y`] THEN
  SUBGOAL_THEN `x IN interval[a:real^N,b]` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL]] THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC[VEC_COMPONENT] THEN MATCH_MP_TAC(REAL_ARITH
   `abs(d) <= &1
    ==> a <= x /\ x <= b ==> a - &1 <= x + d /\ x + d <= b + &1`) THEN
  SUBGOAL_THEN `e IN cball(z:real^N,&1)` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_CBALL]] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[DIST_SYM] dist] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  MESON_TAC[REAL_LE_TRANS; COMPONENT_LE_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Sometimes convenient to restrict the sets in "preimage" characterization  *)
(* of measurable functions to choose points from a dense set.                *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k <= a})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `k:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!n. ?x. x IN r /\ a < x /\ x < a + inv(&n + &1)`
  MP_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_UNIV; CLOSURE_APPROACHABLE; EXISTS_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`lift(a + inv(&n + &1) / &2)`; `inv(&n + &1) / &2`]) THEN
    REWRITE_TAC[REAL_HALF; DIST_LIFT; REAL_LT_INV_EQ] THEN
    ANTS_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC MONO_EXISTS] THEN
    SIMP_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `t:num->real` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x$k <= a} =
    INTERS {{x | (f x)$k <= t n} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN EQ_TAC THENL
     [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `i < f - a ==> !j. j <= i /\ a < t /\ t < a + j ==> &0 < f - t`)) THEN
    EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k >= a})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) r:real->bool`]
        MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF; LIFT_NEG] THEN
    ASM_REWRITE_TAC[GSYM o_DEF; IMAGE_o; CLOSURE_NEGATIONS] THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
    MESON_TAC[VECTOR_NEG_NEG];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= --y <=> x >= y`]]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k < a})`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x < a <=> ~(x >= a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  SIMP_TAC[GSYM MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE_DENSE]);;

let MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT_DENSE = prove
 (`!f:real^M->real^N r.
        closure (IMAGE lift r) = (:real^1)
        ==> (f measurable_on (:real^M) <=>
             !a k. 1 <= k /\ k <= dimindex(:N) /\ a IN r
                   ==> lebesgue_measurable {x | f(x)$k > a})`,
  GEN_TAC THEN REWRITE_TAC[REAL_ARITH `x > a <=> ~(x <= a)`] THEN
  REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL] THEN
  SIMP_TAC[GSYM MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE_DENSE]);;

let MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval[a,b]})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN
   `!n. ?u v:real^N.
        (u IN t /\ u IN interval[(a - lambda i. inv(&n + &1)),a]) /\
        (v IN t /\ v IN interval[b,(b + lambda i. inv(&n + &1))])`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `a - i < a <=> &0 < i`;
                REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:num->real^N`; `v:num->real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x IN interval[a,b]} =
    INTERS {{x | f x IN interval[u n,v n]} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[IN_INTERVAL] THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    REWRITE_TAC[DE_MORGAN_THM; EXISTS_OR_THM; REAL_NOT_LE] THEN
    MATCH_MP_TAC MONO_OR THEN CONJ_TAC THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `!a i j. i < a - f /\ j <= i /\ a - j <= t /\ t <= a
                ==> &0 < t - f`) THEN EXISTS_TAC `(a:real^N)$k`;
      MATCH_MP_TAC(REAL_ARITH
       `!a i j. i < f - a /\ j <= i /\ a <= t /\ t <= a + j
                ==> &0 < f - t`) THEN EXISTS_TAC `(b:real^N)$k`] THEN
    MAP_EVERY EXISTS_TAC [`inv(&n)`; `inv(&n + &1)`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a b. a IN t /\ b IN t
                   ==> lebesgue_measurable {x | f(x) IN interval(a,b)})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  SUBGOAL_THEN
   `!n. ?u v:real^N.
        (u IN t /\ u IN interval[a,(a + lambda i. inv(&n + &1))]) /\
        (v IN t /\ v IN interval[(b - lambda i. inv(&n + &1)),b])`
  MP_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM; LEFT_EXISTS_AND_THM] THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `a - i < a <=> &0 < i`;
                REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:num->real^N`; `v:num->real^N`] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | (f:real^M->real^N) x IN interval(a,b)} =
    UNIONS {{x | f x IN interval(u n,v n)} | n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTERVAL] THEN
    EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LET_TRANS; REAL_LTE_TRANS]] THEN
    SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < inf { min ((y - a:real^N)$i) ((b - y:real^N)$i) |
                 i IN 1..dimindex(:N)}`
    MP_TAC THENL
     [SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; REAL_SUB_LT;
                   VECTOR_SUB_COMPONENT; IN_NUMSEG];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`])) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LE_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k <= (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_ORTHANT_LE] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `a:real^N` THEN
  SUBGOAL_THEN
   `!n. ?u:real^N.
        u IN t /\ u IN interval[a,(a + lambda i. inv(&n + &1))]`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `b < b + i <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:num->real^N` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | !i. 1 <= i /\ i <= dimindex(:N)
             ==> (f:real^M->real^N) x$i <= (a:real^N)$i} =
    INTERS {{x | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> (f:real^M->real^N) x$i <= (u n:real^N)$i} |
            n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:num` THEN
    ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THEN ASM_REWRITE_TAC[] THEN
    EQ_TAC THENL [ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[NOT_FORALL_THM; REAL_NOT_LE] THEN
    ONCE_REWRITE_TAC[GSYM REAL_SUB_LT] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(REAL_ARITH
     `!a i j. i < f - a /\ j <= i /\ a <= t /\ t <= a + j
              ==> &0 < f - t`) THEN EXISTS_TAC `(a:real^N)$k` THEN
    MAP_EVERY EXISTS_TAC [`inv(&n)`; `inv(&n + &1)`] THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GE_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k >= (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) t:real^N->bool`]
        MEASURABLE_ON_PREIMAGE_ORTHANT_LE_DENSE) THEN
  ASM_REWRITE_TAC[CLOSURE_NEGATIONS; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x <= --y <=> x >= y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_UNIV] THEN MESON_TAC[VECTOR_NEG_NEG]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_LT_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k < (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [MEASURABLE_ON_PREIMAGE_ORTHANT_LT] THEN
  EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN X_GEN_TAC `a:real^N` THEN
  SUBGOAL_THEN
   `!n. ?u:real^N.
        u IN t /\ u IN interval[(a - lambda i. inv(&n + &1)):real^N,a]`
  MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
     `~(interior s INTER t = {}) /\ interior s SUBSET s
      ==> ?x. x IN t /\ x IN s`) THEN
    REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
    W(MP_TAC o PART_MATCH (rand o rand) OPEN_INTER_CLOSURE_EQ_EMPTY o
      rand o snd) THEN
    REWRITE_TAC[OPEN_INTERVAL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[INTER_UNIV; INTERVAL_NE_EMPTY] THEN
    SIMP_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[REAL_ARITH `b - i < b <=> &0 < i`] THEN
    REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `u:num->real^N` THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_INTERVAL] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; LAMBDA_BETA]] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | !i. 1 <= i /\ i <= dimindex(:N)
             ==> (f:real^M->real^N) x$i < (a:real^N)$i} =
    UNIONS {{x | !i. 1 <= i /\ i <= dimindex(:N)
                      ==> (f:real^M->real^N) x$i < (u n:real^N)$i} |
            n IN (:num)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_INTERVAL] THEN
    EQ_TAC THENL [ALL_TAC; ASM_MESON_TAC[REAL_LET_TRANS; REAL_LTE_TRANS]] THEN
    SPEC_TAC(`(f:real^M->real^N) x`,`y:real^N`) THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 < inf { (a - y:real^N)$i | i IN 1..dimindex(:N)}`
    MP_TAC THENL
     [SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
               IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; REAL_LT_MIN; REAL_SUB_LT;
                   VECTOR_SUB_COMPONENT; IN_NUMSEG];
      ALL_TAC] THEN
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    SIMP_TAC[REAL_LT_INF_FINITE; SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG;
             IMAGE_EQ_EMPTY; NUMSEG_EMPTY; GSYM NOT_LE; DIMINDEX_GE_1] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; VECTOR_SUB_COMPONENT; IN_NUMSEG] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `k:num`])) THEN
    ASM_SIMP_TAC[VECTOR_SUB_COMPONENT; LAMBDA_BETA] THEN
    SUBGOAL_THEN `inv(&n + &1) <= inv(&n)` MP_TAC THENL
     [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    SIMP_TAC[COUNTABLE_IMAGE; NUM_COUNTABLE; SIMPLE_IMAGE] THEN
    ASM_SIMP_TAC[FORALL_IN_IMAGE]]);;

let MEASURABLE_ON_PREIMAGE_ORTHANT_GT_DENSE = prove
 (`!f:real^M->real^N t.
        closure t = (:real^N)
        ==> (f measurable_on (:real^M) <=>
             !a. a IN t
                 ==> lebesgue_measurable
                        {x | !k. 1 <= k /\ k <= dimindex(:N)
                                 ==> f(x)$k > (a:real^N)$k})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MEASURABLE_ON_NEG_EQ] THEN
  MP_TAC(ISPECL [`(\x. --f x):real^M->real^N`; `IMAGE (--) t:real^N->bool`]
        MEASURABLE_ON_PREIMAGE_ORTHANT_LT_DENSE) THEN
  ASM_REWRITE_TAC[CLOSURE_NEGATIONS; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_ARITH `--x < --y <=> x > y`] THEN
  DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_UNIV] THEN MESON_TAC[VECTOR_NEG_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Localized variants of function measurability equivalents.                 *)
(* ------------------------------------------------------------------------- *)

let [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_INTERVAL;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT;
     MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_INTERVAL] =
  (CONJUNCTS o prove)
 (`(!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> lebesgue_measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval[a,b]})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> lebesgue_measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k >= a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k > a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k <= a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> lebesgue_measurable {x | x IN s /\ (f x)$k < a})) /\
   (!f:real^M->real^N s.
      lebesgue_measurable s
      ==> (f measurable_on s <=>
           !a b. lebesgue_measurable {x | x IN s /\ f x IN interval(a,b)}))`,
  let lemma = prove
   (`!f s P. {x | P(if x IN s then f x else vec 0)} =
             if P(vec 0) then s INTER {x | P(f x)} UNION ((:real^M) DIFF s)
             else {x | x IN s /\ P(f x)}`,
    REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REPEAT(POP_ASSUM MP_TAC) THEN SET_TAC[]) in
  ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[MEASURABLE_ON_PREIMAGE_CLOSED];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_CLOSED_INTERVAL];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GE];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_GT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LE];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_HALFSPACE_COMPONENT_LT];
    REWRITE_TAC[MEASURABLE_ON_PREIMAGE_OPEN_INTERVAL]] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`] lemma) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  TRY(MATCH_MP_TAC(TAUT `(q <=> q') ==> (p ==> q <=> p ==> q')`)) THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
  EQ_TAC THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_UNION; LEBESGUE_MEASURABLE_COMPL] THEN
  UNDISCH_TAC `lebesgue_measurable(s:real^M->bool)` THEN
  REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP LEBESGUE_MEASURABLE_INTER) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ open t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN]);;

let LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ lebesgue_measurable s /\ closed t
        ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. open t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_OPEN] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[OPEN_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ lebesgue_measurable s <=>
        !t. closed t ==> lebesgue_measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[CLOSED_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED]);;

let [MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_INTERVAL;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT;
     MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_INTERVAL] =
  (CONJUNCTS o prove)
 (`(!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. closed t ==> measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval[a,b]})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !t. open t ==> measurable {x | x IN s /\ f x IN t})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k >= a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k > a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k <= a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a k. 1 <= k /\ k <= dimindex(:N)
                 ==> measurable {x | x IN s /\ (f x)$k < a})) /\
   (!f:real^M->real^N s.
      measurable s
      ==> (f measurable_on s <=>
           !a b. measurable {x | x IN s /\ f x IN interval(a,b)}))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MEASURABLE_IMP_LEBESGUE_MEASURABLE) THENL
   [ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED];
    ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED_INTERVAL];
    ASM_SIMP_TAC[MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GT];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LE];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT];
    ASM_SIMP_TAC
     [MEASURABLE_ON_LEBESGUE_MEASURABLE_PREIMAGE_OPEN_INTERVAL]] THEN
  EQ_TAC THEN SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_SIMP_TAC[] THEN SET_TAC[]);;

let MEASURABLE_MEASURABLE_PREIMAGE_OPEN = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ open t
        ==> measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_MEASURABLE_PREIMAGE_CLOSED = prove
 (`!f:real^M->real^N s t.
        f measurable_on s /\ measurable s /\ closed t
        ==> measurable {x | x IN s /\ f(x) IN t}`,
  MESON_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED]);;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. open t ==> measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_MEASURABLE_PREIMAGE_OPEN] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[OPEN_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN]);;

let MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED_EQ = prove
 (`!f:real^M->real^N s.
        f measurable_on s /\ measurable s <=>
        !t. closed t ==> measurable {x | x IN s /\ f(x) IN t}`,
  REPEAT GEN_TAC THEN EQ_TAC THEN
  SIMP_TAC[MEASURABLE_MEASURABLE_PREIMAGE_CLOSED] THEN
  DISCH_THEN(fun th -> MP_TAC th THEN MP_TAC(SPEC `(:real^N)` th)) THEN
  REWRITE_TAC[CLOSED_UNIV; SET_RULE `{x | x IN s /\ f x IN UNIV} = s`] THEN
  SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED]);;

(* ------------------------------------------------------------------------- *)
(* Regularity properties and Steinhaus, this time for Lebesgue measure.      *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_OUTER_OPEN = prove
 (`!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. open t /\
                s SUBSET t /\
                measurable(t DIFF s) /\
                measure(t DIFF s) < e`,
  REPEAT STRIP_TAC THEN MP_TAC(GEN `n:num`
   (ISPECL [`s INTER ball(vec 0:real^N,&2 pow n)`;
            `e / &4 / &2 pow n`]
        MEASURABLE_OUTER_OPEN)) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE; REAL_LT_DIV;
               MEASURABLE_BALL; REAL_LT_INV_EQ; REAL_LT_POW2;
               REAL_ARITH `&0 < e / &4 <=> &0 < e`] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `t:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `UNIONS(IMAGE t (:num)):real^N->bool` THEN
  ASM_SIMP_TAC[OPEN_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `norm(x:real^N)` REAL_ARCH_POW2) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[SUBSET]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[IN_BALL_0; IN_INTER];
    REWRITE_TAC[UNIONS_DIFF; SET_RULE
     `{f x | x IN IMAGE g s} = {f(g(x)) | x IN s}`] THEN
    MATCH_MP_TAC(MESON[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`]
        `&0 < e /\ P /\ x <= e / &2 ==> P /\ x < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
    ASM_SIMP_TAC[MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. e / &4 / &2 pow i)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `measure(t i DIFF (s INTER ball(vec 0:real^N,&2 pow i)))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MEASURE_SUBSET THEN
        ASM_SIMP_TAC[MEASURABLE_MEASURABLE_DIFF_LEGESGUE_MEASURABLE;
          MEASURABLE_INTER; MEASURABLE_BALL; LEBESGUE_MEASURABLE_INTER;
          MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
        SET_TAC[];
        ASM_SIMP_TAC[MEASURE_DIFF_SUBSET; MEASURABLE_DIFF; MEASURABLE_BALL;
                     MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
        ASM_SIMP_TAC[REAL_ARITH `t < s + e ==> t - s <= e`]];
      REWRITE_TAC[real_div; SUM_LMUL; REAL_INV_POW; SUM_GP] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[CONJUNCT1 LT] THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_LE_LMUL_EQ] THEN
      REWRITE_TAC[REAL_ARITH
        `&1 / &4 * (&1 - x) * &2 <= &1 / &2 <=> &0 <= x`] THEN
      MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV]]);;

let LEBESGUE_MEASURABLE_INNER_CLOSED = prove
 (`!s:real^N->bool e.
        lebesgue_measurable s /\ &0 < e
        ==> ?t. closed t /\
                t SUBSET s /\
                measurable(s DIFF t) /\
                measure(s DIFF t) < e`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool` o MATCH_MP
    LEBESGUE_MEASURABLE_OUTER_OPEN) THEN
  EXISTS_TAC `(:real^N) DIFF t` THEN POP_ASSUM MP_TAC THEN
  REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN
  REWRITE_TAC[GSYM OPEN_CLOSED] THENL
   [SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC;
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC] THEN
  SET_TAC[]);;

let STEINHAUS_LEBESGUE = prove
 (`!s:real^N->bool.
        lebesgue_measurable s /\ ~negligible s
        ==> ?d. &0 < d /\ ball(vec 0,d) SUBSET {x - y | x IN s /\ y IN s}`,
  GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
  REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  MP_TAC(ISPEC `s INTER interval[a:real^N,b]` STEINHAUS) THEN
  ASM_SIMP_TAC[GSYM MEASURABLE_MEASURE_POS_LT; MEASURABLE_INTERVAL;
               MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE] THEN
  SET_TAC[]);;

let LEBESGUE_MEASURABLE_REGULAR_OUTER = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. open(c n)) /\
                  s = INTERS {c n | n IN (:num)} DIFF k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LEBESGUE_MEASURABLE_OUTER_OPEN)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
  REWRITE_TAC[REAL_LT_POW2; SKOLEM_THM; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `c:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `INTERS {c n | n IN (:num)} DIFF s:real^N->bool` THEN
  EXISTS_TAC `c:num->real^N->bool` THEN
  ASM_REWRITE_TAC[SET_RULE `s = t DIFF (t DIFF s) <=> s SUBSET t`] THEN
  ASM_REWRITE_TAC[SUBSET_INTERS; FORALL_IN_GSPEC] THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `(c:num->real^N->bool) n DIFF s` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SET_TAC[]; ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]]);;

let LEBESGUE_MEASURABLE_REGULAR_INNER = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?k c. negligible k /\ (!n. compact(c n)) /\
                  s = UNIONS {c n | n IN (:num)} UNION k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    LEBESGUE_MEASURABLE_INNER_CLOSED)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
  REWRITE_TAC[REAL_LT_POW2; SKOLEM_THM; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `c:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `s DIFF UNIONS {c n | n IN (:num)}:real^N->bool` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    EXISTS_TAC `s DIFF (c:num->real^N->bool) n` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SET_TAC[]; ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TRANS]];
    SUBGOAL_THEN
     `?d. (!n. compact(d n:real^N->bool)) /\
          UNIONS {d n | n IN (:num)} = UNIONS {c n | n IN (:num)}`
    MP_TAC THENL
     [MP_TAC(GEN `n:num` (ISPEC
       `(c:num->real^N->bool) n` CLOSED_UNION_COMPACT_SUBSETS)) THEN
      ASM_REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN DISCH_THEN
       (X_CHOOSE_THEN `d:num->num->real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN
       `COUNTABLE {d n m:real^N->bool | n IN (:num) /\ m IN (:num)}`
      MP_TAC THENL
       [MATCH_MP_TAC COUNTABLE_PRODUCT_DEPENDENT THEN
        REWRITE_TAC[NUM_COUNTABLE];
        DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          COUNTABLE_AS_IMAGE)) THEN
        ANTS_TAC THENL [SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[SET_RULE `s = t UNION (s DIFF t) <=> t SUBSET s`] THEN
      ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC]]]);;

(* ------------------------------------------------------------------------- *)
(* A Lebesgue measurable set is almost an F_sigma.                           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_ALMOST_FSIGMA = prove
 (`!s:real^N->bool.
        lebesgue_measurable s
        ==> ?c t. fsigma c /\ negligible t /\ c UNION t = s /\ DISJOINT c t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[fsigma; LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[] `(?a b c. P a b c) <=> (?c b a. P a b c)`] THEN
  REWRITE_TAC[TAUT `(p /\ q /\ r) /\ s /\ t /\ u <=>
                    r /\ t /\ u /\ p /\ q /\ s`] THEN
  REWRITE_TAC[UNWIND_THM1] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        LEBESGUE_MEASURABLE_INNER_CLOSED)) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&n + &1)`) THEN
  REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM; SKOLEM_THM; FORALL_AND_THM] THEN
  X_GEN_TAC `f:num->real^N->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `IMAGE (f:num->real^N->bool) (:num)` THEN
  EXISTS_TAC `s DIFF UNIONS (IMAGE (f:num->real^N->bool) (:num))` THEN
  ASM_SIMP_TAC[SET_RULE `DISJOINT s (u DIFF s)`; COUNTABLE_IMAGE;
               NUM_COUNTABLE; FORALL_IN_IMAGE; IN_UNIV; UNIONS_SUBSET;
               SET_RULE `s UNION (u DIFF s) = u <=> s SUBSET u`] THEN
  REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [REAL_ARCH_INV]) THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s DIFF (f:num->real^N->bool) n` THEN
  ASM_REWRITE_TAC[UNIONS_IMAGE] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS `inv(&n + &1)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN TRANS_TAC REAL_LE_TRANS `inv(&n)` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existence of nonmeasurable subsets of any set of positive measure.        *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS = prove
 (`!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> lebesgue_measurable t`,
  let lemma = prove
   (`!s:real^N->bool.
      lebesgue_measurable s /\
      (!x y q. x IN s /\ y IN s /\ rational q /\ y = q % basis 1 + x ==> y = x)
      ==> negligible s`,
    SIMP_TAC[VECTOR_ARITH `q + x:real^N = x <=> q = vec 0`; VECTOR_MUL_EQ_0;
             BASIS_NONZERO; DIMINDEX_GE_1; ARITH] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_TAC THEN MP_TAC(ISPEC `s:real^N->bool` STEINHAUS_LEBESGUE) THEN
    ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `q:real` o MATCH_MP RATIONAL_BETWEEN) THEN
    FIRST_X_ASSUM
     (MP_TAC o SPEC `q % basis 1:real^N` o GEN_REWRITE_RULE I [SUBSET]) THEN
    SIMP_TAC[IN_BALL_0; NORM_MUL; NORM_BASIS; DIMINDEX_GE_1;
             ARITH; NOT_IMP] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[IN_ELIM_THM]] THEN
    ASM_REWRITE_TAC[REAL_MUL_RID; IN_ELIM_THM; NOT_EXISTS_THM;
                    VECTOR_ARITH `q:real^N = x - y <=> x = q + y`] THEN
    ASM_CASES_TAC `q = &0` THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]]) in
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[NEGLIGIBLE_SUBSET; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    DISCH_TAC] THEN
  ABBREV_TAC
   `(canonize:real^N->real^N) =
    \x. @y. y IN s /\ ?q. rational q /\ q % basis 1 + y = x` THEN
  SUBGOAL_THEN
   `!x:real^N. x IN s
               ==> canonize x IN s /\
                   ?q. rational q /\ q % basis 1 + canonize x = x`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN EXPAND_TAC "canonize" THEN
    CONV_TAC SELECT_CONV THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `&0` THEN
    REWRITE_TAC[RATIONAL_CLOSED] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `v = IMAGE (canonize:real^N->real^N) s` THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
   `UNIONS (IMAGE (\q. IMAGE (\x:real^N. q % basis 1 + x) v) rational)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_IMAGE; SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
  SIMP_TAC[COUNTABLE_RATIONAL; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_TRANSLATION_EQ] THEN GEN_TAC THEN
  DISCH_THEN(K ALL_TAC) THEN MATCH_MP_TAC lemma THEN
  CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "v" THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  X_GEN_TAC `q:real` THEN REPEAT DISCH_TAC THEN
  EXPAND_TAC "canonize" THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  X_GEN_TAC `z:real^N` THEN AP_TERM_TAC THEN FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `y:real^N` th) THEN MP_TAC(SPEC `x:real^N` th)) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `q % b + x:real^N = y <=> x = y - q % b`] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x - q % b:real^N = y - r % b - s % b <=>
                   y + (q - r - s) % b = x /\ x + (r + s - q) % b = y`] THEN
  STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC
   (BINDER_CONV o RAND_CONV o RAND_CONV o LAND_CONV) [SYM th]) THEN
  SIMP_TAC[VECTOR_MUL_EQ_0; BASIS_NONZERO; DIMINDEX_GE_1; ARITH; VECTOR_ARITH
   `y - q % b:real^N = (y + r % b) - s % b <=> (q + r - s) % b = vec 0`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[REAL_ARITH `a + b - c = &0 <=> c = a + b`; UNWIND_THM2] THEN
  ASM_SIMP_TAC[RATIONAL_CLOSED]);;

let NEGLIGIBLE_IFF_MEASURABLE_SUBSETS = prove
 (`!s:real^N->bool. negligible s <=> !t. t SUBSET s ==> measurable t`,
  MESON_TAC[NEGLIGIBLE_SUBSET; NEGLIGIBLE_IMP_MEASURABLE;
            MEASURABLE_IMP_LEBESGUE_MEASURABLE;
            NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS]);;

(* ------------------------------------------------------------------------- *)
(* Preserving Lebesgue measurability vs. preserving negligibility.           *)
(* ------------------------------------------------------------------------- *)

let PRESERVES_LEBESGUE_MEASURABLE_IMP_PRESERVES_NEGLIGIBLE = prove
 (`!f s:real^N->bool.
        (!t. negligible t /\ t SUBSET s ==> lebesgue_measurable(IMAGE f t))
        ==> (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[NEGLIGIBLE_IFF_LEBESGUE_MEASURABLE_SUBSETS] THEN
  REWRITE_TAC[FORALL_SUBSET_IMAGE] THEN
  ASM_MESON_TAC[NEGLIGIBLE_SUBSET; SUBSET_TRANS]);;

let LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\
        (!t. negligible t /\ t SUBSET s ==> negligible(IMAGE f t))
        ==> !t. lebesgue_measurable t /\ t SUBSET s
                ==> lebesgue_measurable(IMAGE f t)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(STRIP_ASSUME_TAC o
    MATCH_MP LEBESGUE_MEASURABLE_REGULAR_INNER) THEN
  ASM_REWRITE_TAC[IMAGE_UNION; IMAGE_UNIONS] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
  SUBGOAL_THEN `(k:real^M->bool) SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE]] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
  REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o; FORALL_IN_IMAGE] THEN
  SIMP_TAC[IN_UNIV; COUNTABLE_IMAGE; NUM_COUNTABLE] THEN
  GEN_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_COMPACT THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
    CONTINUOUS_ON_SUBSET)) THEN ASM SET_TAC[]);;

let PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE = prove
 (`!f:real^M->real^N.
        f continuous_on s
        ==> ((!t. lebesgue_measurable t /\ t SUBSET s
                  ==> lebesgue_measurable (IMAGE f t)) <=>
             (!t. negligible t /\ t SUBSET s ==> negligible (IMAGE f t)))`,
  MESON_TAC[LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE;
            PRESERVES_LEBESGUE_MEASURABLE_IMP_PRESERVES_NEGLIGIBLE;
            NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE]);;

let LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\
        f differentiable_on s /\ lebesgue_measurable s
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC
   (REWRITE_RULE[IMP_IMP; RIGHT_IMP_FORALL_THM]
        LEBESGUE_MEASURABLE_CONTINUOUS_IMAGE) THEN
  EXISTS_TAC `s:real^M->bool` THEN
  ASM_SIMP_TAC[SUBSET_REFL; DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
  ASM_MESON_TAC[DIFFERENTIABLE_ON_SUBSET]);;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ lebesgue_measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR]);;

let MEASURABLE_LINEAR_IMAGE_GEN = prove
 (`!f:real^M->real^N s.
        linear f /\ measurable s /\ dimindex(:M) <= dimindex(:N)
        ==> measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o MATCH_MP (ARITH_RULE
   `m:num <= n ==> m < n \/ m = n`))
  THENL
   [MATCH_MP_TAC NEGLIGIBLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_LOWDIM THEN
    ASM_SIMP_TAC[DIFFERENTIABLE_ON_LINEAR];
    ASM_CASES_TAC `!x y. (f:real^M->real^N) x = f y ==> x = y` THENL
     [ASM_MESON_TAC[MEASURABLE_LINEAR_IMAGE_EQ_GEN]; ALL_TAC] THEN
    MATCH_MP_TAC NEGLIGIBLE_IMP_MEASURABLE THEN
    MATCH_MP_TAC NEGLIGIBLE_LOWDIM THEN
    MP_TAC(ISPECL [`f:real^M->real^N`; `(:real^M)`]
        DIM_IMAGE_KERNEL_GEN) THEN
    ASM_REWRITE_TAC[SUBSPACE_UNIV; DIM_UNIV] THEN ONCE_ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(ARITH_RULE
     `x <= y /\ ~(d = 0) ==> x < y + d`) THEN
    SIMP_TAC[DIM_SUBSET; IMAGE_SUBSET; SUBSET_UNIV] THEN
    REWRITE_TAC[IN_UNIV; DIM_EQ_0] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP LINEAR_INJECTIVE_0) THEN ASM SET_TAC[]]);;

let LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ_GEN = prove
 (`!f:real^M->real^N s.
        dimindex(:M) = dimindex(:N) /\ linear f /\ (!x y. f x = f y ==> x = y)
        ==> (lebesgue_measurable(IMAGE f s) <=> lebesgue_measurable s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. f((g:real^N->real^M) y) = y` ASSUME_TAC THENL
   [MP_TAC(ISPEC `f:real^M->real^N` LINEAR_SURJECTIVE_IFF_INJECTIVE_GEN) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [ALL_TAC;
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LE_REFL]] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `s = IMAGE (g:real^N->real^M) (IMAGE f s)` SUBST1_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of continuous functions.                                    *)
(* ------------------------------------------------------------------------- *)

let CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ lebesgue_measurable s
        ==> f measurable_on s`,
  let lemma = prove
   (`!s. lebesgue_measurable s
         ==> ?u:num->real^M->bool.
                (!n. closed(u n)) /\ (!n. u n SUBSET s) /\
                (!n. measurable(s DIFF u n) /\
                     measure(s DIFF u n) < inv(&n + &1)) /\
                (!n. u(n) SUBSET u(SUC n))`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `!n t. closed t /\ t SUBSET s
            ==> ?u:real^M->bool.
                      closed u /\ t SUBSET u /\ u SUBSET s /\
                      measurable(s DIFF u) /\ measure(s DIFF u) < inv(&n + &1)`
    MP_TAC THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`s DIFF t:real^M->bool`; `inv(&n + &1)`]
        LEBESGUE_MEASURABLE_INNER_CLOSED) THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; LEBESGUE_MEASURABLE_CLOSED] THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t UNION u:real^M->bool` THEN ASM_SIMP_TAC[CLOSED_UNION] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[SET_RULE `s DIFF (t UNION u) = s DIFF t DIFF u`];
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
      REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `v:num->(real^M->bool)->(real^M->bool)` THEN DISCH_TAC THEN
      MP_TAC(prove_recursive_functions_exist num_RECURSION
          `(u:num->real^M->bool) 0 = v 0 {} /\
           (!n. u(SUC n) = v (SUC n) (u n))`) THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:num->real^M->bool` THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `!n. closed(u n) /\ (u:num->real^M->bool) n SUBSET s`
      ASSUME_TAC THENL
       [INDUCT_TAC THEN
        ASM_SIMP_TAC[CLOSED_EMPTY; EMPTY_SUBSET];
        ASM_SIMP_TAC[]] THEN
      INDUCT_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[CLOSED_EMPTY; EMPTY_SUBSET]]) in
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `u:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP lemma) THEN
  SUBGOAL_THEN `lebesgue_measurable((:real^M) DIFF s)` MP_TAC THENL
   [ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_COMPL]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:num->real^M->bool` STRIP_ASSUME_TAC o
    MATCH_MP lemma) THEN
  REWRITE_TAC[measurable_on] THEN
  EXISTS_TAC `(:real^M) DIFF
           (UNIONS {u n | n IN (:num)} UNION UNIONS {v n | n IN (:num)})` THEN
  SUBGOAL_THEN
   `!n. ?g. g continuous_on (:real^M) /\
            (!x. x IN u(n) UNION v(n:num)
                 ==> g x = if x IN s then (f:real^M->real^N)(x) else vec 0)`
  MP_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC TIETZE_UNBOUNDED THEN
    ASM_SIMP_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; CLOSED_UNION] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_CONST] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN MATCH_MP_TAC MONO_EXISTS] THEN
  X_GEN_TAC `g:num->real^M->real^N` THEN
  REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(s DIFF UNIONS {u n | n IN (:num)}) UNION
                ((:real^M) DIFF s DIFF UNIONS {v n | n IN (:num)})` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC NEGLIGIBLE_UNION THEN CONJ_TAC THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THENL
     [EXISTS_TAC `s DIFF u(n:num):real^M->bool`;
      EXISTS_TAC `(:real^M) DIFF s DIFF v(n:num):real^M->bool`] THEN
    (CONJ_TAC THENL [SET_TAC[]; ASM_REWRITE_TAC[]] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_TRANS THEN
     EXISTS_TAC `inv(&n)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT] THEN
     CONJ_TAC THENL [ASM_ARITH_TAC; REAL_ARITH_TAC]);
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[SET_RULE
     `~(x IN (UNIV DIFF (s UNION t))) <=> x IN s \/ x IN t`] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[OR_EXISTS_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `n:num` THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNION] THEN
    SUBGOAL_THEN
     `!i j. i <= j ==> (u:num->real^M->bool)(i) SUBSET u(j) /\
                       (v:num->real^M->bool)(i) SUBSET v(j)`
     (fun th -> ASM_MESON_TAC[SUBSET; th]) THEN
    MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
   ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET = prove
 (`!f:real^M->real^N s.
        f continuous_on s /\ closed s ==> f measurable_on s`,
  SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET;
           LEBESGUE_MEASURABLE_CLOSED]);;

let CONTINUOUS_AE_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s m.
        f continuous_on (s DIFF m) /\ lebesgue_measurable s /\ negligible m
        ==> f measurable_on s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) measurable_on (s DIFF m)` MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_DIFF; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    MATCH_MP_TAC MEASURABLE_ON_SPIKE_SET THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
       NEGLIGIBLE_SUBSET)) THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Measurability of a.e. derivatives.                                        *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_VECTOR_DERIVATIVE = prove
 (`!f:real^1->real^N f' s k.
        negligible k /\ negligible(frontier s) /\
        (!x. x IN (s DIFF k) ==> (f has_vector_derivative f'(x)) (at x))
        ==> f' measurable_on s`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
  ABBREV_TAC `g:real^1->real^N = \x. if x IN s then f(x) else vec 0` THEN
  SUBGOAL_THEN `(g:real^1->real^N) measurable_on (:real^1)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN REWRITE_TAC[MEASURABLE_ON_UNIV] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
    EXISTS_TAC `s DIFF k:real^1->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `k:real^1->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_ON THEN
        MATCH_MP_TAC DIFFERENTIABLE_AT_IMP_DIFFERENTIABLE_ON THEN
        ASM_MESON_TAC[differentiable; has_vector_derivative];
        MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
        ASM_SIMP_TAC[NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE] THEN
        ASM_SIMP_TAC[LEBESGUE_MEASURABLE_JORDAN]]];
     ALL_TAC] THEN
  MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN
  EXISTS_TAC `\n x. (&n + &1) % (g(x + lift(inv(&n + &1))) - g(x):real^N)` THEN
  EXISTS_TAC `k UNION frontier s:real^1->bool` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN CONJ_TAC THENL
   [X_GEN_TAC `n:num` THEN MATCH_MP_TAC MEASURABLE_ON_CMUL THEN
    MATCH_MP_TAC MEASURABLE_ON_SUB THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ADD_SYM] THEN
    REWRITE_TAC[MEASURABLE_ON_TRANSLATION_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
     `g measurable_on s ==> t = s ==> g measurable_on t`)) THEN
    MATCH_MP_TAC(SET_RULE
     `!g. (!x. f(g x) = x /\ g(f x) = x) ==> IMAGE f UNIV = UNIV`) THEN
    EXISTS_TAC `\x. --(lift(inv(&n + &1))) + x` THEN VECTOR_ARITH_TAC;

    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_UNIV; IN_DIFF; IN_UNION; DE_MORGAN_THM; frontier;
                CLOSURE_INTERIOR] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `d:real` THEN ASM_SIMP_TAC[DIST_REFL] THEN STRIP_TAC THEN
    MATCH_MP_TAC LIM_TRANSFORM_EVENTUALLY THENL
     [EXISTS_TAC `(\n. vec 0):num->real^N`;
      EXISTS_TAC `(\n. (&n + &1) % (f(x + lift (inv (&n + &1))) - f x))
                  :num->real^N`] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
       MP_TAC(SPEC `d:real` REAL_ARCH_INV) THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
       X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
       DISCH_TAC THEN
       SUBGOAL_THEN `dist(x,x + lift(inv(&n + &1))) < d` ASSUME_TAC THENL
        [REWRITE_TAC[NORM_ARITH `dist(a:real^N,a + x) = norm x`] THEN
         REWRITE_TAC[NORM_LIFT; REAL_ABS_INV] THEN
         REWRITE_TAC[REAL_ARITH `abs(&n + &1) = &n + &1`] THEN
         MATCH_MP_TAC REAL_LT_TRANS THEN EXISTS_TAC `inv(&N)` THEN
         ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
         ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
         EXPAND_TAC "g" THEN REWRITE_TAC[] THEN ASM_SIMP_TAC[DIST_REFL] THEN
         VECTOR_ARITH_TAC];
       ALL_TAC]) THEN
     REWRITE_TAC[LIM_CONST] THEN
     UNDISCH_THEN
      `!x. x IN s DIFF k
           ==> ((f:real^1->real^N) has_vector_derivative f' x) (at x)`
      (MP_TAC o SPEC `x:real^1`) THEN
     ASM_SIMP_TAC[IN_DIFF; DIST_REFL; has_vector_derivative] THEN
     REWRITE_TAC[has_derivative; NETLIMIT_AT] THEN
     DISCH_THEN(MP_TAC o CONJUNCT2) THEN
     REWRITE_TAC[LIM_AT; LIM_SEQUENTIALLY] THEN DISCH_TAC THEN
     X_GEN_TAC `e:real` THEN DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_TAC `k:real`) THEN
     MP_TAC(SPEC `k:real` REAL_ARCH_INV) THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
     X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
     DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `x +  lift(inv(&n + &1))` o CONJUNCT2) THEN
     REWRITE_TAC[NORM_ARITH `dist(x + a:real^N,x) = norm a`] THEN
     REWRITE_TAC[NORM_LIFT; REAL_ABS_INV; REAL_ARITH `abs(&n + &1) = &n + &1`;
              VECTOR_ARITH `(x + e) - x:real^N = e`; LIFT_DROP] THEN
     ANTS_TAC THENL
      [REWRITE_TAC[REAL_LT_INV_EQ] THEN
       CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_TRANS] THEN
       EXISTS_TAC `inv(&N)` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LT_INV2 THEN
       ASM_REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
       MATCH_MP_TAC(NORM_ARITH
        `x - y:real^N = z ==> dist(z,vec 0) < e ==> dist(x,y) < e`) THEN
       REWRITE_TAC[REAL_INV_INV; VECTOR_SUB_LDISTRIB; VECTOR_ADD_LDISTRIB] THEN
       SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID;
                REAL_ARITH `~(&n + &1 = &0)`] THEN
       VECTOR_ARITH_TAC]]);;

let ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER = prove
 (`!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on (s INTER t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC
    MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
  EXISTS_TAC
   `\x. lift(norm(if x IN s then (f:real^M->real^N) x else vec 0))` THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; IN_UNIV; IN_INTER;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  REWRITE_TAC[MESON[]
   `(if p /\ q then x else y) = if q then if p then x else y else y`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_CASES THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = s`; MEASURABLE_ON_0] THEN
    ASM_SIMP_TAC[INTEGRABLE_IMP_MEASURABLE;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    X_GEN_TAC `x:real^M` THEN ASM_CASES_TAC `(x:real^M) IN t` THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; LIFT_DROP; NORM_0; NORM_POS_LE]]);;

let ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET = prove
 (`!f:real^M->real^N s t.
        f absolutely_integrable_on s /\ t SUBSET s /\ lebesgue_measurable t
        ==> f absolutely_integrable_on t`,
  MESON_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
            SET_RULE `s SUBSET t ==> s = t INTER s`]);;

(* ------------------------------------------------------------------------- *)
(* Various Vitali-type covering lemmas.                                      *)
(* ------------------------------------------------------------------------- *)

let WIENER_COVERING_LEMMA_BALLS = prove
 (`!k a:A->real^N r s.
        FINITE k /\ s SUBSET UNIONS(IMAGE (\i. ball(a i,r i)) k)
        ==> ?c. c SUBSET k /\
                pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
                s SUBSET UNIONS(IMAGE (\i. ball(a i,&3 * r i)) c)`,
  REPLICATE_TAC 3 GEN_TAC THEN WF_INDUCT_TAC `CARD(k:A->bool)` THEN
  X_GEN_TAC `s:real^N->bool` THEN ASM_CASES_TAC `k:A->bool = {}` THEN
  ASM_REWRITE_TAC[PAIRWISE_EMPTY; SUBSET_EMPTY; IMAGE_CLAUSES;
                  FINITE_EMPTY; UNWIND_THM2] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (r:A->real) k` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:A` THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(r:A->real) n <= &0` THENL
   [EXISTS_TAC `{}:A->bool` THEN
    ASM_REWRITE_TAC[PAIRWISE_EMPTY; EMPTY_SUBSET] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET u ==> u = {} ==> s SUBSET t`)) THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_IMAGE; BALL_EQ_EMPTY] THEN
    ASM_MESON_TAC[REAL_LE_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{i | i IN k /\ DISJOINT (ball((a:A->real^N) i,r i)) (ball(a n,r n))}`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `i IN s ==> ~P i ==> {j | j IN s /\ P j} PSUBSET s`)) THEN
    ASM_REWRITE_TAC[GSYM DISJOINT_EMPTY_REFL; BALL_EQ_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s DIFF ball((a:A->real^N) n,&3 * r n)`) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET UNIONS(IMAGE h f)
      ==> g SUBSET f /\ (!i. i IN f DIFF g ==> h i SUBSET b)
         ==> s DIFF b SUBSET UNIONS(IMAGE h g)`)) THEN
    REWRITE_TAC[SUBSET_RESTRICT; SET_RULE
     `i IN k DIFF {x | x IN k /\ P x} <=> i IN k /\ ~P i`] THEN
    X_GEN_TAC `m:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DISJOINT; EXTENSION; SUBSET; NOT_IN_EMPTY; IN_BALL; IN_INTER] THEN
    CONV_TAC NORM_ARITH;
    DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(n:A) INSERT c` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIRWISE_INSERT; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    ASM SET_TAC[]]);;

let WIENER_COVERING_LEMMA_CBALLS = prove
 (`!k a:A->real^N r s.
       FINITE k /\ s SUBSET UNIONS(IMAGE (\i. cball(a i,r i)) k)
       ==> ?c. c SUBSET k /\
               pairwise (\i j. DISJOINT (cball(a i,r i)) (cball(a j,r j))) c /\
               s SUBSET UNIONS(IMAGE (\i. cball(a i,&3 * r i)) c)`,
  REPLICATE_TAC 3 GEN_TAC THEN WF_INDUCT_TAC `CARD(k:A->bool)` THEN
  X_GEN_TAC `s:real^N->bool` THEN ASM_CASES_TAC `k:A->bool = {}` THEN
  ASM_REWRITE_TAC[PAIRWISE_EMPTY; SUBSET_EMPTY; IMAGE_CLAUSES;
                  FINITE_EMPTY; UNWIND_THM2] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (r:A->real) k` SUP_FINITE) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `n:A` THEN DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_CASES_TAC `(r:A->real) n < &0` THENL
   [EXISTS_TAC `{}:A->bool` THEN
    ASM_REWRITE_TAC[PAIRWISE_EMPTY; EMPTY_SUBSET] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET u ==> u = {} ==> s SUBSET t`)) THEN
    REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_IMAGE; CBALL_EQ_EMPTY] THEN
    ASM_MESON_TAC[REAL_LET_TRANS];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC
   `{i | i IN k /\
         DISJOINT (cball((a:A->real^N) i,r i)) (cball(a n,r n))}`) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC CARD_PSUBSET THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (SET_RULE `i IN s ==> ~P i ==> {j | j IN s /\ P j} PSUBSET s`)) THEN
    ASM_REWRITE_TAC[GSYM DISJOINT_EMPTY_REFL; CBALL_EQ_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `s DIFF cball((a:A->real^N) n,&3 * r n)`) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET UNIONS(IMAGE h f)
      ==> g SUBSET f /\ (!i. i IN f DIFF g ==> h i SUBSET b)
         ==> s DIFF b SUBSET UNIONS(IMAGE h g)`)) THEN
    REWRITE_TAC[SUBSET_RESTRICT; SET_RULE
     `i IN k DIFF {x | x IN k /\ P x} <=> i IN k /\ ~P i`] THEN
    X_GEN_TAC `m:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:A`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[DISJOINT; EXTENSION; SUBSET;
             NOT_IN_EMPTY; IN_CBALL; IN_INTER] THEN
    CONV_TAC NORM_ARITH;
    DISCH_THEN(X_CHOOSE_THEN `c:A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(n:A) INSERT c` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[PAIRWISE_INSERT; IMAGE_CLAUSES; UNIONS_INSERT] THEN
    ASM SET_TAC[]]);;

let VITALI_COVERING_THEOREM_BALLS = prove
 (`!k a:A->real^N r s.
        measurable s /\ measurable(UNIONS {ball(a i,r i) | i IN k}) /\
        (!x d. x IN s /\ &0 < d
               ==> ?i. i IN k /\ x IN ball(a i,r i) /\ r i < d)
        ==> ?c. COUNTABLE c /\ c SUBSET k /\
                pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
                negligible(s DIFF UNIONS {ball(a i,r i) | i IN c})`,
  let lemma0 = prove
   (`(?f g. P f g) <=> (?f:A->B#C. P (FST o f) (SND o f))`,
    EQ_TAC THENL [STRIP_TAC; MESON_TAC[]] THEN
    EXISTS_TAC `\x. (f:A->B) x,(g:A->C) x` THEN
    ASM_REWRITE_TAC[o_DEF; ETA_AX])
  and lemma1 = prove
   (`!k a:A->real^N r.
        measurable(UNIONS {ball(a i,r i) | i IN k})
        ==> ?c. FINITE c /\ c SUBSET k /\
                pairwise (\i j. DISJOINT (ball(a i,r i)) (ball(a j,r j))) c /\
                measure(UNIONS {ball(a i,r i) | i IN k}) / &2 /
                &3 pow (dimindex(:N))
                <= measure(UNIONS {ball(a i,r i) | i IN c})`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `negligible(UNIONS {ball((a:A->real^N) i,r i) | i IN k})`
    THENL
     [EXISTS_TAC `{}:A->bool` THEN
      REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; PAIRWISE_EMPTY] THEN
      REWRITE_TAC[SET_RULE`{f i | i IN {}} = {}`; UNIONS_0; MEASURE_EMPTY] THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN REWRITE_TAC[real_div; REAL_ENTIRE] THEN
      ASM_SIMP_TAC[MEASURE_EQ_0];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{ball((a:A->real^N) i,r i) | i IN k}` LINDELOF) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; OPEN_BALL] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
      [TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[SIMPLE_IMAGE] THEN
    REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:A->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
    MP_TAC(ISPECL
     [`{ball((a:A->real^N) i,r i) | i IN d}`;
      `measure(UNIONS {ball((a:A->real^N) i,r i) | i IN d})`;
      `measure(UNIONS {ball((a:A->real^N) i,r i) | i IN d}) / &2`]
     MEASURE_COUNTABLE_UNIONS_APPROACHABLE) THEN
    ASM_SIMP_TAC[REAL_HALF; MEASURABLE_MEASURE_POS_LT;
                 FORALL_IN_GSPEC; MEASURABLE_BALL] THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[CONJ_SYM] THEN
      REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; MEASURABLE_UNIONS; FORALL_IN_IMAGE;
                   MEASURABLE_BALL; FINITE_IMAGE] THEN
      ASM SET_TAC[];
      ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
      REWRITE_TAC[REAL_ARITH `a - a / &2 = a / &2`] THEN
      REWRITE_TAC[GSYM SIMPLE_IMAGE; LEFT_IMP_EXISTS_THM]] THEN
    X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:A->bool`; `a:A->real^N`; `r:A->real`;
                   `UNIONS {ball((a:A->real^N) x,r x) | x IN c}`]
          WIENER_COVERING_LEMMA_BALLS) THEN
    ASM_REWRITE_TAC[GSYM SIMPLE_IMAGE; SUBSET_REFL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:A->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; DISCH_TAC] THEN
    SIMP_TAC[REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &3`] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < y ==> y <= z ==> x <= z`)) THEN
    TRANS_TAC REAL_LE_TRANS
     `measure(UNIONS {ball ((a:A->real^N) x,&3 * r x) | x IN f})` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_BALL] THEN
      ASM_SIMP_TAC[FINITE_IMAGE];
      REWRITE_TAC[SIMPLE_IMAGE] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
        lhand o snd) THEN
      ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_POW_LT; REAL_ARITH `&0 < &3`] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURE_DISJOINT_UNIONS_IMAGE o
      rand o snd) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
    ASM_REWRITE_TAC[MEASURABLE_BALL] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[real_div; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ; REAL_POW_LT;
             REAL_ARITH `&0 < &3`] THEN
    REWRITE_TAC[REAL_ARITH `a * &3 pow n = abs(&3) pow n * a`] THEN
    SIMP_TAC[GSYM MEASURE_SCALING; MEASURABLE_BALL] THEN
    SIMP_TAC[GSYM BALL_SCALING; REAL_ARITH `&0 < &3`] THEN
    REWRITE_TAC[VECTOR_ARITH `&3 % x:real^N = &2 % x + x`] THEN
    REWRITE_TAC[BALL_TRANSLATION; MEASURE_TRANSLATION; REAL_LE_REFL]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 / &2 / &3 pow dimindex(:N)` ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC) THEN
    TRY(MATCH_MP_TAC REAL_POW_LT) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 / &2 / &3 pow dimindex(:N) < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `inv x <= &1 ==> &1 / &2 / x < &1`) THEN
    MATCH_MP_TAC REAL_INV_LE_1 THEN MATCH_MP_TAC REAL_POW_LE_1 THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k'. k' SUBSET k
         ==> measurable(UNIONS {ball((a:A->real^N) i,r i) | i IN k'})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `{ball((a:A->real^N) i,r i) | i IN k'}` LINDELOF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; SIMPLE_IMAGE; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `k'':A->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
    MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `UNIONS {ball((a:A->real^N) i,r i) | i IN k}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    SIMP_TAC[MEASURABLE_BALL; MEASURABLE_IMP_LEBESGUE_MEASURABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c d. (!n. FINITE(c n) /\ c n SUBSET k /\ d n SUBSET k /\
               (!i j. i IN c n /\ j IN d n
                      ==> DISJOINT (ball(a i,r i)) (ball(a j,r j))) /\
               pairwise (\i j. DISJOINT
                                (ball(a i,r i)) (ball(a j,r j))) (c n) /\
               measurable(UNIONS {ball((a:A->real^N) i,r i) | i IN d n}) /\
               measure(UNIONS {ball((a:A->real^N) i,r i) | i IN d n})
                <= (&1 - &1 / &2 / &3 pow dimindex(:N)) pow n *
                   measure(UNIONS {ball(a i,r i) | i IN k}) /\
               !x e. x IN s DIFF UNIONS {cball(a i,r i) | i IN c n} /\ &0 < e
                     ==> ?j. j IN d n /\ x IN ball(a j,r j) /\ r j < e) /\
          (!n. c n SUBSET c (SUC n) /\ d(SUC n) SUBSET d n)`
  MP_TAC THENL
   [REWRITE_TAC[lemma0; o_DEF] THEN MATCH_MP_TAC DEPENDENT_CHOICE THEN
    REWRITE_TAC[FORALL_PAIR_THM; EXISTS_PAIR_THM] THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`{}:A->bool`; `k:A->bool`] THEN
      REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY; real_pow] THEN
      REWRITE_TAC[SUBSET_REFL; PAIRWISE_EMPTY; REAL_MUL_LID; REAL_LE_REFL] THEN
      ASM_REWRITE_TAC[SET_RULE `{f x | x | F} = {}`; UNIONS_0; DIFF_EMPTY];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `c:A->bool`; `d:A->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:A->bool`; `a:A->real^N`; `r:A->real`] lemma1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c':A->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `c UNION c':A->bool` THEN
    ABBREV_TAC `d' = {i | i IN d /\
                          ball((a:A->real^N) i,r i) INTER
                          UNIONS {cball(a j,r j) | j IN c'} = {}}` THEN
    EXISTS_TAC `d':A->bool` THEN
    ASM_REWRITE_TAC[FINITE_UNION; UNION_SUBSET; GSYM CONJ_ASSOC] THEN
    REPLICATE_TAC 2
     (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; DISCH_TAC]) THEN
    SUBGOAL_THEN `(d':A->bool) SUBSET d` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[SUBSET_UNION]] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_UNION] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN EXPAND_TAC "d'" THEN
      X_GEN_TAC `j:A` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      DISCH_THEN(MP_TAC o SPEC `i:A` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(a:A->real^N) i`; `(r:A->real) i`]
        BALL_SUBSET_CBALL) THEN SET_TAC[];
      ASM_REWRITE_TAC[PAIRWISE_UNION] THEN ASM SET_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      TRANS_TAC REAL_LE_TRANS
       `(&1 - &1 / &2 / &3 pow dimindex (:N)) *
        measure(UNIONS {ball((a:A->real^N) i,r i) | i IN d})` THEN
      REWRITE_TAC[real_pow; GSYM REAL_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL; REAL_LT_IMP_LE; REAL_SUB_LT] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
        `u / &2 / p <= x ==> x + y <= u ==> y <= (&1 - &1 / &2 / p) * u`)) THEN
      W(MP_TAC o PART_MATCH
          (rand o rand) MEASURE_DISJOINT_UNION o lhand o snd) THEN
      ANTS_TAC THENL
       [REPEAT(CONJ_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC]) THEN
        EXPAND_TAC "d'" THEN REWRITE_TAC[SET_RULE
         `DISJOINT s (UNIONS f) <=> !t. t IN f ==> DISJOINT s t`] THEN
        REWRITE_TAC[FORALL_IN_GSPEC] THEN GEN_TAC THEN MATCH_MP_TAC(SET_RULE
         `(!x. g x SUBSET f x)
          ==> p /\ b INTER UNIONS {f x | x IN s} = {}
              ==> DISJOINT (UNIONS {g x | x IN s}) b`) THEN
        REWRITE_TAC[BALL_SUBSET_CBALL];
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[SET_RULE
         `UNIONS{f x | x IN s} UNION UNIONS{f x | x IN t} =
          UNIONS {f x | x IN s UNION t}`] THEN
        MATCH_MP_TAC MEASURE_SUBSET THEN REPEAT CONJ_TAC THEN
        TRY(FIRST_X_ASSUM MATCH_MP_TAC) THEN ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `e:real`] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN MP_TAC(ISPEC
       `(:real^N) DIFF UNIONS {cball(a(i:A),r i) | i IN c UNION c'}`
        OPEN_CONTAINS_BALL) THEN
      ASM_SIMP_TAC[GSYM closed; CLOSED_UNIONS; SIMPLE_IMAGE; FINITE_IMAGE;
                   FORALL_IN_IMAGE; CLOSED_CBALL; FINITE_UNION] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[IN_UNIV; IN_DIFF; LEFT_IMP_EXISTS_THM;
                      GSYM SIMPLE_IMAGE] THEN
      X_GEN_TAC `e':real` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `min e (e' / &2)`]) THEN
      ASM_REWRITE_TAC[REAL_HALF; REAL_LT_MIN] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
       X_GEN_TAC `i:A` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "d'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `b SUBSET UNIV DIFF UNIONS f
        ==> UNIONS g SUBSET UNIONS f /\ c SUBSET b
        ==> c INTER UNIONS g = {}`)) THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_BALL]) THEN
      REPEAT(FIRST_X_ASSUM
       (MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_NOT_LE])) THEN
      CONV_TAC NORM_ARITH];
    REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`c:num->A->bool`; `d:num->A->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `UNIONS {(c:num->A->bool) n | n IN (:num)}` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; NUM_COUNTABLE;
                   FORALL_IN_IMAGE; FINITE_IMP_COUNTABLE];
      REWRITE_TAC[UNIONS_GSPEC] THEN ASM SET_TAC[];
      REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[UNIONS_GSPEC; FORALL_IN_GSPEC; IN_UNIV] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; RIGHT_IMP_FORALL_THM] THEN
      ONCE_REWRITE_TAC[MESON[]
       `(!a b c d. P a b c d) <=> (!b d a c. P a b c d)`] THEN
      MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN DISCH_TAC THEN
      MAP_EVERY X_GEN_TAC [`i:A`; `j:A`] THEN REPEAT STRIP_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `a IN s ==> s SUBSET t ==> a IN t`)) THEN
      UNDISCH_TAC `m:num <= n` THEN
      MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`n:num`; `m:num`] THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[NEGLIGIBLE_OUTER] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`inv(&1 - &1 / &2 / &3 pow dimindex (:N))`;
                     `measure(UNIONS{ball((a:A->real^N) i,r i) | i IN k}) / e`]
          REAL_ARCH_POW) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; LEFT_IMP_EXISTS_THM; REAL_POW_INV] THEN
      REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
      X_GEN_TAC `n:num` THEN
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_POW_LT; REAL_SUB_LT] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN DISCH_TAC THEN
      EXISTS_TAC `UNIONS {ball((a:A->real^N) i,r i) | i IN d(n:num)} UNION
                  UNIONS {sphere(a i,r i) | i IN c n}` THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SET_RULE
         `s SUBSET u UNION v <=> s DIFF v SUBSET u`] THEN
        GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`n:num`; `x:real^N`; `&1`]) THEN
        REWRITE_TAC[REAL_LT_01] THEN MATCH_MP_TAC MONO_IMP THEN
        CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
        REWRITE_TAC[GSYM BALL_UNION_SPHERE; UNIONS_GSPEC] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `negligible(UNIONS{sphere((a:A->real^N) i,r i) | i IN c(n:num)})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
        ASM_SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
        REWRITE_TAC[NEGLIGIBLE_SPHERE];
        ALL_TAC] THEN
      ASM_SIMP_TAC[MEASURABLE_UNION; NEGLIGIBLE_IMP_MEASURABLE] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_NEGLIGIBLE_UNION o
        lhand o snd) THEN
      ASM_SIMP_TAC[MEASURABLE_UNION; NEGLIGIBLE_IMP_MEASURABLE] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; INTER_SUBSET];
        DISCH_THEN SUBST1_TAC THEN
        ASM_SIMP_TAC[MEASURE_EQ_0; REAL_ADD_RID] THEN
        ASM_MESON_TAC[REAL_LET_TRANS]]]]);;

(* ------------------------------------------------------------------------- *)
(* More refined measurability bounds for Lipschitz or differentiable images. *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s.
        dimindex(:M) <= dimindex(:N) /\ lebesgue_measurable s /\
        (!x. x IN s
             ==> ?t b. open t /\ x IN t /\
                       !y. y IN s INTER t
                           ==> norm(f y - f x) <= b * norm(y - x))
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) continuous_on s` MP_TAC THENL
   [REWRITE_TAC[continuous_on] THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; dist] THEN
    MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `B:real`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def]) THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d (e / (abs B + &1))` THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_MIN; REAL_ARITH `&0 < abs B + &1`] THEN
    X_GEN_TAC `y:real^M` THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < abs B + &1`] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    TRANS_TAC REAL_LE_TRANS `B * norm(y - x:real^M)` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE; REAL_ARITH `B <= abs B + &1`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[dist];
    DISCH_THEN(MP_TAC o MATCH_MP
     PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE) THEN
    DISCH_THEN(MP_TAC o snd o EQ_IMP_RULE) THEN
    ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
    X_GEN_TAC `u:real^M->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE,MEASURE_LOCALLY_LIPSCHITZ_IMAGE =
 (CONJ_PAIR o prove)
 (`(!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\
        measurable s /\
        (!x. x IN s
             ==> ?t. open t /\
                     x IN t /\
                     (!y. y IN s INTER t
                          ==> norm(f y - f x) <= B * norm(y - x)))
        ==> measurable(IMAGE f s)) /\
   (!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\
        measurable s /\
        (!x. x IN s
             ==> ?t. open t /\
                     x IN t /\
                     (!y. y IN s INTER t
                          ==> norm(f y - f x) <= B * norm(y - x)))
        ==> measure(IMAGE f s) <= B pow dimindex(:N) * measure s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x. ?e. x IN s
            ==> &0 < e /\
                !y. y IN s INTER ball(x,e)
                    ==> norm((f:real^M->real^N) y - f x) <= B * norm(y - x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^M` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL; SUBSET; IN_INTER] THEN MESON_TAC[];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM]] THEN
  X_GEN_TAC `r:real^M->real` THEN DISCH_THEN(LABEL_TAC "*") THEN
  ASM_CASES_TAC `B < &0` THENL
   [SUBGOAL_THEN `negligible(s:real^M->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC DISCRETE_IMP_COUNTABLE THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      EXISTS_TAC `(r:real^M->real) x` THEN
      REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^M` o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
      ANTS_TAC THENL [ALL_TAC; CONV_TAC NORM_ARITH] THEN
      MATCH_MP_TAC(NORM_ARITH `&0 < --x ==> ~(norm(a:real^M) <= x)`) THEN
      REWRITE_TAC[GSYM REAL_MUL_LNEG] THEN MATCH_MP_TAC REAL_LT_MUL THEN
      ASM_SIMP_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
      SUBGOAL_THEN `negligible(IMAGE (f:real^M->real^N) s)` ASSUME_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN ASM SET_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_EQ_MEASURE_0]) THEN
        ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LE_REFL]]];
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT])] THEN
  ASM_CASES_TAC `dimindex(:M) < dimindex(:N)` THENL
   [SUBGOAL_THEN `negligible(IMAGE (f:real^M->real^N) s)` MP_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE_LOWDIM THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[NEGLIGIBLE_EQ_MEASURE_0; REAL_POS; REAL_POW_LE; REAL_LE_MUL;
                   MEASURE_POS_LE]];
    ALL_TAC] THEN
  ASM_CASES_TAC `B = &0` THENL
   [SUBGOAL_THEN `negligible(IMAGE (f:real^M->real^N) s)` MP_TAC THENL
     [ALL_TAC;
      ASM_SIMP_TAC[NEGLIGIBLE_EQ_MEASURE_0; REAL_POS; REAL_POW_LE; REAL_LE_MUL;
                   MEASURE_POS_LE]] THEN
    MP_TAC(ISPEC `{ball(x:real^M,r x) | x IN s}` LINDELOF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; SIMPLE_IMAGE; OPEN_BALL] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^M->real^N)
                 (UNIONS (IMAGE (\x. s INTER ball(x,r x)) c))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `UNIONS (IMAGE (\x. {(f:real^M->real^N) x}) c)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
        ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; NEGLIGIBLE_SING];
        REWRITE_TAC[IMAGE_UNIONS; GSYM IMAGE_o; o_DEF] THEN
        MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x SUBSET g x)
          ==> UNIONS (IMAGE f s) SUBSET UNIONS (IMAGE g s)`) THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`)) THEN
        ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN
        REWRITE_TAC[REAL_MUL_LZERO; NORM_ARITH
         `norm(x - y:real^M) <= &0 <=> x = y`] THEN
        SET_TAC[]];
      TRANS_TAC SUBSET_TRANS
       `IMAGE (f:real^M->real^N)
              (s INTER UNIONS(IMAGE (\x. ball (x,r x)) c))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[INTER_UNIONS] THEN ASM SET_TAC[]] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM; IN_INTER] THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `x:real^M` THEN ASM_SIMP_TAC[CENTRE_IN_BALL]];
    SUBGOAL_THEN `&0 < B` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]] THEN
  SUBGOAL_THEN
   `measurable(IMAGE (f:real^M->real^N) s) /\
    !e. &0 < e ==> measure(IMAGE f s) <= B pow dimindex(:N) * (measure s + e)`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[REAL_LT_01]
     `(!e. &0 < e ==> P /\ Q e) ==> P /\ (!e. &0 < e ==> Q e)`);
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (MP_TAC o SPEC
       `(measure(IMAGE (f:real^M->real^N) s) / B pow dimindex(:N) - measure s)
             / &2`)) THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_RDIV_EQ; REAL_ADD_LDISTRIB; REAL_HALF;
                 REAL_LT_IMP_NZ; REAL_DIV_LMUL; REAL_POW_LT; REAL_ARITH
                  `B * (x - y) / &2 = (B * x - B * y) / &2`] THEN
    REAL_ARITH_TAC] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `e:real`] MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:real^M->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{(x,t) | x IN s /\ t <= (r:real^M->real) x /\ ball(x,t) SUBSET u}`;
    `FST:real^M#real->real^M`;
    `SND:real^M#real->real`; `s:real^M->bool`]
   VITALI_COVERING_THEOREM_BALLS) THEN
  ASM_REWRITE_TAC[EXISTS_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      W(MP_TAC o PART_MATCH (rand o lhand o snd o dest_forall o lhand)
        LINDELOF o rand o rand o snd) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC;
                  SIMPLE_IMAGE; OPEN_BALL] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; COUNTABLE_IMAGE] THEN
      SIMP_TAC[FORALL_PAIR_THM; MEASURABLE_IMP_LEBESGUE_MEASURABLE;
               MEASURABLE_BALL];
      MAP_EVERY X_GEN_TAC [`x:real^M`; `d:real`] THEN STRIP_TAC THEN
      EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min (d / &2) (min d' (r(x:real^M)))` THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL; REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      TRANS_TAC SUBSET_TRANS `ball(x:real^M,d')` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `c:real^M#real->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `measurable(IMAGE (f:real^M->real^N) (s INTER UNIONS {ball i | i IN c})) /\
    measure(IMAGE (f:real^M->real^N) (s INTER UNIONS {ball i | i IN c}))
    <= B pow dimindex(:N) * (measure(s:real^M->bool) + e)`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       MEASURABLE_NEGLIGIBLE_SYMDIFF);
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
     `IMAGE (f:real^M->real^N) (s DIFF UNIONS {ball i | i IN c})` THEN
    (CONJ_TAC THENL [ALL_TAC; SET_TAC[]]) THEN
    MATCH_MP_TAC NEGLIGIBLE_LOCALLY_LIPSCHITZ_IMAGE THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC(MESON[MEASURABLE_LEBESGUE_MEASURABLE_SUBSET; REAL_LE_TRANS;
                     MEASURE_SUBSET]
    `!t. lebesgue_measurable s /\ s SUBSET t /\ measurable t /\ measure t <= b
         ==> measurable s /\ measure s <= b`) THEN
  EXISTS_TAC `UNIONS {ball((f:real^M->real^N) (FST x),B * SND x) |
                      (x:real^M#real) IN c}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; GSYM IMAGE_o; IMAGE_UNIONS] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; o_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_INTER;
                 MEASURABLE_BALL] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INTER_UNIONS; IMAGE_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
    MATCH_MP_TAC UNIONS_MONO_IMAGE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; o_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `t:real`] THEN STRIP_TAC THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:real^M` THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    STRIP_TAC THEN REMOVE_THEN "*" (MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `y:real^M`)) THEN
    ASM_REWRITE_TAC[IN_INTER; GSYM dist; IN_BALL] THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [DIST_SYM] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS) THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[MEASURABLE_BALL] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
  X_GEN_TAC `k:real^M#real->bool` THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
    lhand o snd) THEN
  ASM_REWRITE_TAC[MEASURABLE_BALL] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
  TRANS_TAC REAL_LE_TRANS
   `sum k (\a:real^M#real. abs B pow dimindex(:N) * measure(ball a))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `t:real`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^M->real^N) x = B % inv(B) % f x` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; VECTOR_MUL_LID];
      ALL_TAC] THEN
    ASM_SIMP_TAC[BALL_SCALING; MEASURE_SCALING; MEASURABLE_BALL] THEN
    SUBGOAL_THEN `dimindex(:N) = dimindex(:M)` SUBST1_TAC THENL
     [ASM_ARITH_TAC; MATCH_MP_TAC REAL_LE_LMUL] THEN
    ASM_SIMP_TAC[REAL_POW_LE; REAL_ABS_POS] THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_ADD_RID] THEN
    REWRITE_TAC[BALL_TRANSLATION; MEASURE_TRANSLATION] THEN
    SUBGOAL_THEN
     `ball(vec 0:real^N,t) = IMAGE (\x. lambda i. x$i) (ball(vec 0:real^M,t))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[IN_BALL_0; NORM_LT_SQUARE] THEN
      SIMP_TAC[dot; LAMBDA_BETA] THEN
      SUBGOAL_THEN `dimindex(:M) = dimindex(:N)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[]] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      EXISTS_TAC `(lambda i. (y:real^N)$i):real^M` THEN
      SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN
      SUBGOAL_THEN `dimindex(:N) = dimindex(:M)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; SIMP_TAC[LAMBDA_BETA]];
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC MEASURE_ISOMETRY THEN
      CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SIMP_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
               LAMBDA_BETA; CART_EQ] THEN
      X_GEN_TAC `z:real^M` THEN
      SIMP_TAC[NORM_EQ; dot; LAMBDA_BETA] THEN
      SUBGOAL_THEN `dimindex(:M) = dimindex(:N)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[]]];
    REWRITE_TAC[SUM_LMUL] THEN ASM_REWRITE_TAC[real_abs] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_POW_LE] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `u < s + e ==> x <= u ==> x <= s + e`)) THEN
    W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNIONS_IMAGE o
        lhand o snd) THEN
    ASM_REWRITE_TAC[FORALL_PAIR_THM; MEASURABLE_BALL] THEN ANTS_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FORALL_PAIR_THM;
                 MEASURABLE_BALL; FINITE_IMAGE] THEN
    ASM SET_TAC[]]);;

let LEBESGUE_MEASURABLE_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ lebesgue_measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> lebesgue_measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`(:real^M)`; `B:real`] THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; IN_INTER]);;

let MEASURABLE_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> measurable(IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURABLE_LOCALLY_LIPSCHITZ_IMAGE THEN
  EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^M)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; IN_INTER]);;

let MEASURE_LIPSCHITZ_IMAGE = prove
 (`!f:real^M->real^N s B.
        dimindex(:M) <= dimindex(:N) /\ measurable s /\
        (!x y. x IN s /\ y IN s ==> norm(f x - f y) <= B * norm(x - y))
        ==> measure(IMAGE f s) <= B pow dimindex(:N) * measure s`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MEASURE_LOCALLY_LIPSCHITZ_IMAGE THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^M)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; IN_INTER]);;

let MEASURABLE_BOUNDED_DIFFERENTIABLE_IMAGE,
    MEASURE_BOUNDED_DIFFERENTIABLE_IMAGE =
 (CONJ_PAIR o prove)
 (`(!f:real^N->real^N f' s B.
      measurable s /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x within s) /\
               abs(det(matrix(f' x))) <= B)
      ==> measurable(IMAGE f s)) /\
   (!f:real^N->real^N f' s B.
      measurable s /\
      (!x. x IN s
           ==> (f has_derivative f' x) (at x within s) /\
               abs(det(matrix(f' x))) <= B)
      ==> measure(IMAGE f s) <= B * measure s)`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  ASM_CASES_TAC `B < &0` THENL
   [ASM_SIMP_TAC[REAL_ARITH `B < &0 ==> ~(abs x <= B)`] THEN
    SIMP_TAC[GSYM NOT_EXISTS_THM; MEMBER_NOT_EMPTY] THEN
    REWRITE_TAC[IMAGE_CLAUSES; MEASURE_EMPTY; MEASURABLE_EMPTY] THEN
    REAL_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[REAL_NOT_LT]) THEN STRIP_TAC] THEN
 SUBGOAL_THEN
   `measurable(IMAGE (f:real^N->real^N) s) /\
    !e. &0 < e ==> measure(IMAGE f s) <= (B + e) * measure s`
  MP_TAC THENL
   [MATCH_MP_TAC(MESON[REAL_LT_01]
     `(!e. &0 < e ==> P /\ Q e) ==> P /\ (!e. &0 < e ==> Q e)`);
    FIRST_X_ASSUM(MP_TAC o MATCH_MP MEASURE_POS_LE) THEN
    REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[REAL_MUL_RZERO; REAL_LT_01];
      FIRST_X_ASSUM(MP_TAC o SPEC
        `(measure(IMAGE (f:real^N->real^N) s) / measure s - B) / &2`) THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC]] THEN
  SUBGOAL_THEN
   `!d e. &0 < d /\ &0 < e
          ==> measurable(IMAGE (f:real^N->real^N) s) /\
              measure(IMAGE f s) <= (B + e) * (measure s + d)`
  MP_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THENL [ASM_MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `(measure(IMAGE (f:real^N->real^N) s) / (B + e) - measure s) / &2`) THEN
    SUBGOAL_THEN `&0 < B + e` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; REWRITE_TAC[]] THEN
    ASM_SIMP_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM REAL_LE_LDIV_EQ)] THEN
    ASM_REAL_ARITH_TAC] THEN
  MAP_EVERY X_GEN_TAC [`m:real`; `e:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `m:real`] MEASURABLE_OUTER_OPEN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->real^N) differentiable_on s` ASSUME_TAC THENL
   [REWRITE_TAC[differentiable_on; differentiable] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x d. x IN s /\ &0 < d
          ==> ?r. &0 < r /\ r < d /\ ball(x,r) SUBSET u /\
                  measurable(IMAGE (f:real^N->real^N) (s INTER ball(x,r))) /\
                  measure(IMAGE f (s INTER ball(x,r)))
                  <= (B + e) * measure(ball(x,r))`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE ((f':real^N->real^N->real^N) x) (ball(vec 0,&1))`;
                   `e * measure(ball(vec 0:real^N,&1))`]
        MEASURE_SEMICONTINUOUS_WITH_HAUSDIST_EXPLICIT) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o
      GEN_REWRITE_RULE I [has_derivative_within]) THEN
    ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; CONVEX_BALL;
                 NEGLIGIBLE_CONVEX_FRONTIER] THEN
    ASM_SIMP_TAC[BOUNDED_LINEAR_IMAGE; BOUNDED_BALL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; MEASURE_BALL_POS; REAL_LT_01] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I
      [OPEN_CONTAINS_BALL]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [LIM_WITHIN]) THEN
    DISCH_THEN(MP_TAC o SPEC `k:real`) THEN ASM_REWRITE_TAC[DIST_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `r = min (min l (n / &2)) (min (&1) (d / &2))` THEN
    EXISTS_TAC `r:real` THEN REPLICATE_TAC 2
     (MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC]) THEN
    CONJ_TAC THENL
     [TRANS_TAC SUBSET_TRANS `ball(x:real^N,l)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
     `IMAGE (\x. inv(r) % x)
            (IMAGE (\y. --(f x) + y)
                   (IMAGE (f:real^N->real^N) (s INTER ball(x,r))))`) THEN
    ASM_SIMP_TAC[MEASURE_LINEAR_IMAGE; MEASURABLE_BALL; MEASURE_TRANSLATION;
                 MEASURABLE_TRANSLATION] THEN
    MATCH_MP_TAC(TAUT
     `q /\ (q ==> p) /\ (p ==> r ==> s) ==> (p /\ q ==> r) ==> s`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE; IN_INTER; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      ASM_CASES_TAC `y:real^N = x` THENL
       [EXISTS_TAC `vec 0:real^N` THEN
        ASM_REWRITE_TAC[DIST_REFL; REAL_LT_01] THEN
        FIRST_X_ASSUM(SUBST1_TAC o MATCH_MP LINEAR_0) THEN
        REWRITE_TAC[VECTOR_ARITH `r % (--x + x):real^N = vec 0`] THEN
        ASM_REWRITE_TAC[DIST_REFL];
        EXISTS_TAC `inv(r) % (y - x):real^N` THEN
        FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
        ASM_REWRITE_TAC[DIST_0; NORM_MUL; REAL_ABS_INV; DIST_MUL] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < x ==> &0 < abs x`] THEN
        REWRITE_TAC[NORM_ARITH
         `norm(y - x:real^N) < &1 * r <=> dist(x,y) < r`] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
        ASM_REWRITE_TAC[GSYM DIST_NZ] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
        REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; GSYM dist; GSYM DIST_NZ] THEN
        MATCH_MP_TAC(NORM_ARITH
         `a <= b ==> dist(y:real^N,x + f) < a ==> dist(--x + y,f) < b`) THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
        ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN
      W(MP_TAC o PART_MATCH (rand o rand)
         LEBESGUE_MEASURABLE_IFF_MEASURABLE o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC BOUNDED_SUBSET THEN
        EXISTS_TAC
         `{a + b | a IN IMAGE ((f':real^N->real^N->real^N) x)
                              (ball(vec 0,&1)) /\
                   b IN ball(vec 0,k)}` THEN
        ASM_SIMP_TAC[BOUNDED_SUMS; BOUNDED_BALL; BOUNDED_LINEAR_IMAGE] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
        ONCE_REWRITE_TAC[TAUT `(p /\ q) /\ r <=> r /\ p /\ q`] THEN
        REWRITE_TAC[UNWIND_THM2; VECTOR_ARITH
         `x:real^N = a + b <=> b = x - a`] THEN
        REWRITE_TAC[IN_BALL_0; GSYM dist] THEN ASM_MESON_TAC[DIST_SYM];
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
        REWRITE_TAC[LE_REFL; LINEAR_SCALING] THEN
        REWRITE_TAC[LEBESGUE_MEASURABLE_TRANSLATION] THEN
        MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFFERENTIABLE_IMAGE THEN
        ASM_SIMP_TAC[LE_REFL; MEASURABLE_IMP_LEBESGUE_MEASURABLE;
                     MEASURABLE_INTER; MEASURABLE_BALL] THEN
        MATCH_MP_TAC DIFFERENTIABLE_ON_SUBSET THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o ISPEC `\x:real^N. r % x` o
      MATCH_MP(ONCE_REWRITE_RULE[IMP_CONJ_ALT] MEASURABLE_LINEAR_IMAGE)) THEN
    REWRITE_TAC[LINEAR_SCALING] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM IMAGE_o] THEN
    ASM_SIMP_TAC[o_DEF; VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ] THEN
    REWRITE_TAC[VECTOR_MUL_LID; IMAGE_ID] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^N) x` o
       MATCH_MP MEASURABLE_TRANSLATION) THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [GSYM IMAGE_o] THEN
    REWRITE_TAC[o_DEF; VECTOR_ARITH `x + --x + y:real^N = y`] THEN
    REWRITE_TAC[IMAGE_ID] THEN DISCH_TAC THEN
    ASM_SIMP_TAC[MEASURE_SCALING; MEASURABLE_TRANSLATION] THEN
    REWRITE_TAC[MEASURE_TRANSLATION; REAL_ABS_INV; REAL_POW_INV] THEN
    REWRITE_TAC[ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_POW_LT;
                 REAL_ARITH `&0 < r ==> &0 < abs r`] THEN
    MATCH_MP_TAC(REAL_ARITH `y <= z ==> x < y ==> x <= z`) THEN
    ONCE_REWRITE_TAC[REAL_ARITH
     `(a * b + c) * r:real = a * r * b + c * r`] THEN
    SIMP_TAC[GSYM MEASURE_SCALING; MEASURABLE_BALL] THEN
    ASM_SIMP_TAC[GSYM BALL_SCALING] THEN MATCH_MP_TAC(REAL_ARITH
     `x <= a * m /\ w * z * y <= b * m
      ==> x + (w * y) * z <= (a + b) * m`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS] THEN
      SIMP_TAC[MEASURE_POS_LE; MEASURABLE_BALL] THEN
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM REAL_MUL_ASSOC];
      ASM_SIMP_TAC[REAL_LE_LMUL_EQ] THEN
      SIMP_TAC[GSYM MEASURE_SCALING; MEASURABLE_BALL] THEN
      ASM_SIMP_TAC[GSYM BALL_SCALING]] THEN
    REWRITE_TAC[VECTOR_MUL_RZERO; REAL_MUL_RID] THEN
    SUBST1_TAC(VECTOR_ARITH `x:real^N = x + vec 0`) THEN
    REWRITE_TAC[BALL_TRANSLATION; MEASURE_TRANSLATION; REAL_LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; LEFT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  X_GEN_TAC `r:real^N->real->real` THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`{(x:real^N,(r:real^N->real->real) x t) | x IN s /\ &0 < t}`;
    `FST:real^N#real->real^N`;
    `SND:real^N#real->real`; `s:real^N->bool`]
   VITALI_COVERING_THEOREM_BALLS) THEN
  ASM_REWRITE_TAC[EXISTS_IN_GSPEC] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      W(MP_TAC o PART_MATCH (rand o lhand o snd o dest_forall o lhand)
        LINDELOF o rand o rand o snd) THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC;
                  SIMPLE_IMAGE; OPEN_BALL] THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)
       [TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
      REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; COUNTABLE_IMAGE] THEN
      SIMP_TAC[FORALL_PAIR_THM; MEASURABLE_IMP_LEBESGUE_MEASURABLE;
               MEASURABLE_BALL];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `d:real`] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`x:real^N`; `d:real`] THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM_MESON_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `c:real^N#real->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN
   `measurable(IMAGE (f:real^N->real^N) (s INTER UNIONS {ball i | i IN c})) /\
    measure(IMAGE (f:real^N->real^N) (s INTER UNIONS {ball i | i IN c}))
    <= (B + e) * (measure s + m)`
  MP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC MONO_AND THEN CONJ_TAC THENL
     [MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       MEASURABLE_NEGLIGIBLE_SYMDIFF);
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
     `IMAGE (f:real^N->real^N) (s DIFF UNIONS {ball i | i IN c})` THEN
    (CONJ_TAC THENL [ALL_TAC; SET_TAC[]]) THEN
    MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
    ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC DIFFERENTIABLE_ON_SUBSET THEN
    EXISTS_TAC `s:real^N->bool` THEN
    REWRITE_TAC[SUBSET_DIFF; differentiable_on; differentiable] THEN
    ASM_MESON_TAC[]] THEN
  REWRITE_TAC[INTER_UNIONS; SIMPLE_IMAGE; GSYM IMAGE_o; IMAGE_UNIONS] THEN
  MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  REWRITE_TAC[o_DEF] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
  X_GEN_TAC `k:real^N#real->bool` THEN STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
    lhand o snd) THEN
  ASM_REWRITE_TAC[MEASURABLE_BALL] THEN ANTS_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`)) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; o_THM] THEN ASM SET_TAC[];
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
  TRANS_TAC REAL_LE_TRANS
   `sum k (\a:real^N#real. (B + e) * measure(ball a))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    REPEAT(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `s SUBSET t ==> (!x. x IN t ==> P x) ==> (!x. x IN s ==> P x)`))) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `u < s + e ==> x <= u ==> x <= s + e`)) THEN
  W(MP_TAC o PART_MATCH (rand o rand) MEASURE_DISJOINT_UNIONS_IMAGE o
      lhand o snd) THEN
  ASM_REWRITE_TAC[FORALL_PAIR_THM; MEASURABLE_BALL] THEN ANTS_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM SET_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC MEASURE_SUBSET THEN
  ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FORALL_PAIR_THM;
               MEASURABLE_BALL; FINITE_IMAGE] THEN
  ASM SET_TAC[]);;

let MEASURABLE_DIFFERENTIABLE_IMAGE,MEASURE_DIFFERENTIABLE_IMAGE =
  (CONJ_PAIR o prove)
  (`(!f:real^N->real^N f' s.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (\x. lift(abs(det(matrix(f' x))))) integrable_on s
        ==> measurable(IMAGE f s)) /\
    (!f:real^N->real^N f' s b.
        lebesgue_measurable s /\
        (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
        (\x. lift(abs(det(matrix(f' x))))) integrable_on s /\
        drop(integral s (\x. lift(abs(det(matrix(f' x)))))) <= b
        ==> measure(IMAGE f s) <= b)`,
  let lemma = prove
   (`!f:real^N->real^N f' s.
          measurable s /\
          (!x. x IN s ==> (f has_derivative f'(x)) (at x within s)) /\
          (\x. lift(abs(det(matrix(f' x))))) integrable_on s
          ==> measurable(IMAGE f s) /\
              measure(IMAGE f s)
               <= drop(integral s (\x. lift(abs(det(matrix(f' x))))))`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    ABBREV_TAC
     `m = integral s (\x:real^N. lift(abs(det(matrix(f' x):real^N^N))))` THEN
    SUBGOAL_THEN
     `measurable(IMAGE (f:real^N->real^N) s) /\
      !e. &0 < e
          ==> measure(IMAGE (f:real^N->real^N) s) <= drop m + e * measure s`
    MP_TAC THENL
     [MATCH_MP_TAC(MESON[REAL_LT_01]
       `(!e. &0 < e ==> P /\ Q e) ==> P /\ (!e. &0 < e ==> Q e)`);
      MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MEASURE_POS_LE) THEN
      REWRITE_TAC[REAL_ARITH `&0 <= x <=> x = &0 \/ &0 < x`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_RID] THENL
       [MESON_TAC[REAL_LT_01]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
      REWRITE_TAC[REAL_ARITH `(m + e) - f:real = (m - f) + e`] THEN
      ABBREV_TAC `x = drop m - measure (IMAGE (f:real^N->real^N) s)` THEN
      DISCH_THEN(MP_TAC o SPEC `--x / &2 / measure(s:real^N->bool)`) THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_LT_RDIV_EQ] THEN
      REAL_ARITH_TAC] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    ABBREV_TAC
      `t = \n. {x | x IN s /\
                    &n * e <= abs(det(matrix(f'(x:real^N)):real^N^N)) /\
                    abs(det(matrix(f' x))) < (&n + &1) * e}` THEN
    SUBGOAL_THEN
     `!n. measurable((t:num->real^N->bool) n)`
    ASSUME_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[SET_RULE `{x | x IN s /\ P x /\ Q x} =
                     {x | x IN s /\ P x} INTER {x | x IN s /\ Q x}`] THEN
      MATCH_MP_TAC MEASURABLE_INTER THEN CONJ_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP INTEGRABLE_IMP_MEASURABLE) THENL
       [ASM_SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_GE];
        ASM_SIMP_TAC[MEASURABLE_ON_MEASURABLE_PREIMAGE_HALFSPACE_COMPONENT_LT]]
      THEN REWRITE_TAC[DIMINDEX_1; FORALL_1; real_ge] THEN
      SIMP_TAC[GSYM drop; LIFT_DROP];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `s:real^N->bool = UNIONS {t n | n IN (:num)}`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [th] THEN
                GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[UNIONS_GSPEC; IN_UNIV; IN_ELIM_THM] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_CASES_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LT_LDIV_EQ] THEN
      MP_TAC(ISPEC
       `abs(det(matrix(f'(x:real^N)):real^N^N)) / e` FLOOR_POS) THEN
      ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_ABS_POS] THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `n:num` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[FLOOR];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNIONS] THEN
    REWRITE_TAC[SIMPLE_IMAGE; GSYM IMAGE_o] THEN
    ONCE_REWRITE_TAC[GSYM SIMPLE_IMAGE] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
    REWRITE_TAC[o_THM] THEN CONJ_TAC THEN X_GEN_TAC `n:num` THENL
     [MATCH_MP_TAC MEASURABLE_BOUNDED_DIFFERENTIABLE_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`f':real^N->real^N->real^N`; `(&n + &1) * e`] THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "t" THEN SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
        HAS_DERIVATIVE_WITHIN_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum(0..n) (\k. ((&k + &1) * e) * measure(t k:real^N->bool))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC MEASURE_BOUNDED_DIFFERENTIABLE_IMAGE THEN
      EXISTS_TAC `f':real^N->real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "t" THEN SIMP_TAC[IN_ELIM_THM; REAL_LT_IMP_LE] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT]
        HAS_DERIVATIVE_WITHIN_SUBSET) THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ADD_RDISTRIB; GSYM REAL_MUL_ASSOC; SUM_ADD_NUMSEG] THEN
    REWRITE_TAC[REAL_MUL_LID] THEN ONCE_REWRITE_TAC[REAL_ADD_SYM] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LMUL; REAL_LE_LMUL_EQ] THEN
      W(MP_TAC o PART_MATCH (rand o rand)
        MEASURE_DISJOINT_UNIONS_IMAGE_STRONG o lhand o snd) THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FINITE_NUMSEG] THEN ANTS_TAC THENL
       [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `k < n <=> k + 1 <= n`] THEN
        EXPAND_TAC "t" THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD; SET_RULE
         `DISJOINT {x | P x} {x | Q x} <=> !x. P x /\ Q x ==> F`] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LT_LDIV_EQ] THEN
        REAL_ARITH_TAC;
        DISCH_THEN(SUBST1_TAC o SYM)] THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_UNIONS; FORALL_IN_IMAGE; FINITE_IMAGE;
                   FINITE_NUMSEG; UNIONS_SUBSET] THEN
      EXPAND_TAC "t" THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUM_VSUM; o_DEF; LIFT_CMUL] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_MEASURE] THEN
    ASM_SIMP_TAC[GSYM INTEGRAL_CMUL; INTEGRABLE_ON_CONST] THEN
    TRANS_TAC REAL_LE_TRANS
     `drop(vsum (0..n)
                (\k. integral (t k)
                   (\x:real^N. lift(abs(det(matrix(f' x):real^N^N))))))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[DROP_VSUM; o_DEF] THEN MATCH_MP_TAC SUM_LE_NUMSEG THEN
      X_GEN_TAC `k:num` THEN STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[INTEGRABLE_ON_CONST; DROP_CMUL] THEN
      REWRITE_TAC[DROP_VEC; LIFT_DROP; REAL_MUL_RID] THEN
      CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "t" THEN SET_TAC[]] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
      CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "t" THEN SET_TAC[]] THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[DIMINDEX_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IMP_IMP; FORALL_1; GSYM drop; LIFT_DROP; REAL_ABS_POS];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `drop(vsum {t k | k IN 0..n}
      (\t. integral t
              (\x:real^N. lift(abs(det(matrix(f' x):real^N^N))))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      REWRITE_TAC[SIMPLE_IMAGE] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) VSUM_IMAGE_NONZERO o rand o snd) THEN
      REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
       [MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `k < n <=> k + 1 <= n`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
        STRIP_TAC THEN
        REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
        DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
         `i = j ==> DISJOINT i j ==> i = {}`)) THEN
        ANTS_TAC THENL [ALL_TAC; SIMP_TAC[INTEGRAL_EMPTY]] THEN
        EXPAND_TAC "t" THEN REWRITE_TAC[SET_RULE
         `DISJOINT {x | P x} {x | Q x} <=> !x. P x /\ Q x ==> F`] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LT_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]];
      ALL_TAC] THEN
    TRANS_TAC REAL_LE_TRANS
     `drop(integral (UNIONS {t k | k IN 0..n})
                    (\x:real^N. lift(abs(det(matrix(f' x):real^N^N)))))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN AP_TERM_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      MATCH_MP_TAC HAS_INTEGRAL_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE;
                   FORALL_IN_IMAGE; FINITE_NUMSEG] THEN
      CONJ_TAC THENL
       [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET THEN
        EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
        CONJ_TAC THENL [ALL_TAC; EXPAND_TAC "t" THEN SET_TAC[]] THEN
        MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
        ASM_REWRITE_TAC[DIMINDEX_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[IMP_IMP; FORALL_1; GSYM drop; LIFT_DROP; REAL_ABS_POS];
        REWRITE_TAC[CONJ_ASSOC] THEN ONCE_REWRITE_TAC[IMP_CONJ] THEN
        REWRITE_TAC[FORALL_IN_IMAGE_2] THEN
        MATCH_MP_TAC WLOG_LT THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [MESON_TAC[INTER_COMM]; ALL_TAC] THEN
        REWRITE_TAC[ARITH_RULE `k < n <=> k + 1 <= n`] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
        MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
        REPEAT STRIP_TAC THEN
        MATCH_MP_TAC(MESON[NEGLIGIBLE_EMPTY] `s = {} ==> negligible s`) THEN
        EXPAND_TAC "t" THEN REWRITE_TAC[SET_RULE
         `{x | P x} INTER {x | Q x} = {} <=> !x. P x /\ Q x ==> F`] THEN
        ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ; GSYM REAL_LT_LDIV_EQ] THEN
        ASM_REAL_ARITH_TAC];
      EXPAND_TAC "m" THEN MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_ABS_POS; UNIONS_SUBSET] THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN
      CONJ_TAC THENL [EXPAND_TAC "t" THEN SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
        ASM_REWRITE_TAC[DIMINDEX_1; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
        REWRITE_TAC[IMP_IMP; FORALL_1; GSYM drop; LIFT_DROP; REAL_ABS_POS];
        REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
        EXPAND_TAC "t" THEN SET_TAC[];
        MATCH_MP_TAC LEBESGUE_MEASURABLE_UNIONS THEN
        ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
        ASM_SIMP_TAC[FORALL_IN_IMAGE; MEASURABLE_IMP_LEBESGUE_MEASURABLE]]]) in
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[IMP_IMP; MESON[REAL_LE_REFL; REAL_LE_TRANS]
   `(!a. x <= a ==> y <= a) <=> y <= x`] THEN
  REWRITE_TAC[TAUT `(p ==> q) /\ (p ==> r) <=> p ==> q /\ r`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `s = UNIONS {interval[--vec n:real^N,vec n] INTER s | n IN (:num)}`
   (fun th ->
        SUBST1_TAC th THEN REWRITE_TAC[IMAGE_UNIONS] THEN
        REWRITE_TAC[SET_RULE `IMAGE f {g x | x IN s} = {f(g x) | x IN s}`] THEN
        MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG THEN
        SUBST1_TAC(SYM th))
  THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN
    SUBGOAL_THEN
     `!x:real^N. ?n. x IN interval[--vec n,vec n]`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    X_GEN_TAC `x:real^N` THEN
    MP_TAC(ISPEC `norm(x:real^N)` REAL_ARCH_SIMPLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    ASM_MESON_TAC[REAL_ABS_BOUNDS; COMPONENT_LE_NORM; REAL_LE_TRANS];
    ALL_TAC] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  SUBGOAL_THEN
   `UNIONS {IMAGE f (interval[--vec k,vec k] INTER s) | k <= n} =
    IMAGE (f:real^N->real^N) (interval [--vec n,vec n] INTER s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_GSPEC] THEN
    SUBGOAL_THEN
     `!x:real^N n. x IN interval[--vec n,vec n] <=>
                   ?k. k <= n /\ x IN interval[--vec k,vec k]`
    MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[LE_REFL]; ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `k:num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
    REWRITE_TAC[SUBSET_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    ASM_REWRITE_TAC[REAL_OF_NUM_LE; REAL_LE_NEG2];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^N->real^N`; `f':real^N->real^N->real^N`;
    `interval[--vec n:real^N,vec n] INTER s`]
        lemma) THEN
  ASM_SIMP_TAC[MEASURABLE_MEASURABLE_INTER_LEGESGUE_MEASURABLE;
               MEASURABLE_INTERVAL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[HAS_DERIVATIVE_WITHIN_SUBSET; INTER_SUBSET; IN_INTER];
      ALL_TAC];
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_REWRITE_TAC[LIFT_DROP; REAL_ABS_POS; INTER_SUBSET]] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN
  ONCE_REWRITE_TAC[GSYM INTEGRABLE_RESTRICT_INTER] THEN
  MATCH_MP_TAC INTEGRABLE_ON_SUBINTERVAL THEN EXISTS_TAC `(:real^N)` THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; INTEGRABLE_RESTRICT_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Approximation of L_1 functions by bounded continuous ones.                *)
(* Note that 100/fourier.ml has some generalizations to L_p spaces.          *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS = prove
 (`!f:real^M->real^N s e.
        lebesgue_measurable s /\ f absolutely_integrable_on s /\ &0 < e
        ==> ?g. g absolutely_integrable_on s /\
                g continuous_on (:real^M) /\
                bounded (IMAGE g (:real^M)) /\
                norm(integral s (\x. lift(norm(f x - g x)))) < e`,
  let lemma = prove
   (`!f:real^M->real^N s e.
          measurable s /\ f absolutely_integrable_on s /\ &0 < e
          ==> ?g. g absolutely_integrable_on s /\
                  g continuous_on (:real^M) /\
                  bounded (IMAGE g (:real^M)) /\
                  norm(integral s (\x. lift(norm(f x - g x)))) < e`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
      `?h. h absolutely_integrable_on s /\
           bounded (IMAGE h (:real^M)) /\
           norm(integral s (\x. lift(norm(f x - h x:real^N)))) < e / &2`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`\n x. lift(norm
         (f x - (lambda i. max (--(&n))
                             (min (&n) ((f:real^M->real^N)(x)$i)))))`;
        `(\x. vec 0):real^M->real^1`;
        `\x. lift(norm((f:real^M->real^N)(x)))`;
        `s:real^M->bool`]
            DOMINATED_CONVERGENCE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `!n. ((\x. lambda i. max (--(&n)) (min (&n) ((f x:real^N)$i)))
            :real^M->real^N) absolutely_integrable_on s`
      ASSUME_TAC THENL
       [GEN_TAC THEN
        FIRST_ASSUM(MP_TAC o SPEC `(\x. lambda i. &n):real^M->real^N` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTELY_INTEGRABLE_MIN)) THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
        DISCH_THEN(MP_TAC o SPEC `(\x. lambda i. --(&n)):real^M->real^N` o
          MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT] ABSOLUTELY_INTEGRABLE_MAX)) THEN
        ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_ON_CONST] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN
        SIMP_TAC[CART_EQ; LAMBDA_BETA];
        ALL_TAC] THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [X_GEN_TAC `n:num` THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
          MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB];
          ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                       ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
          MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN DISCH_TAC THEN
          REWRITE_TAC[LIFT_DROP; NORM_LIFT; REAL_ABS_NORM] THEN
          MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
          SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN REAL_ARITH_TAC;
          X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
          REWRITE_TAC[LIM_SEQUENTIALLY] THEN
          X_GEN_TAC `d:real` THEN DISCH_TAC THEN
          MP_TAC(SPEC `norm((f:real^M->real^N) x)` REAL_ARCH_SIMPLE) THEN
          MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
          DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
          REWRITE_TAC[DIST_0; NORM_LIFT; REAL_ABS_NORM; GSYM LIFT_SUB] THEN
          MATCH_MP_TAC(NORM_ARITH
           `&0 < d /\ x = y ==> norm(x:real^N - y) < d`) THEN
          ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
          MATCH_MP_TAC(REAL_ARITH
            `abs(x) <= n ==> x = max (--n) (min n x)`) THEN
          ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS; REAL_OF_NUM_LE]];
        DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
        DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
        REWRITE_TAC[INTEGRAL_0; DIST_0; LE_REFL] THEN DISCH_TAC THEN
        EXISTS_TAC `(\x. lambda i. max (--(&n)) (min (&n)
                               ((f:real^M->real^N)(x)$i))):real^M->real^N` THEN
        ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[BOUNDED_COMPONENTWISE] THEN
        REWRITE_TAC[bounded; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN EXISTS_TAC `&n` THEN
        X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[NORM_LIFT; LAMBDA_BETA] THEN REAL_ARITH_TAC];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `?k g. negligible k /\
            (!n. g n continuous_on (:real^M)) /\
            (!n x. norm(g n x:real^N) <= norm(B % vec 1:real^N)) /\
            (!x. x IN (s DIFF k)  ==> ((\n. g n x) --> h x) sequentially)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(h:real^M->real^N) measurable_on s` MP_TAC THENL
       [ASM_MESON_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE]; ALL_TAC] THEN
      REWRITE_TAC[measurable_on] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `k:real^M->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `g:num->real^M->real^N` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(\n x. lambda i. max (--B) (min B (((g n x):real^N)$i))):
                  num->real^M->real^N` THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `n:num` THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
        MP_TAC(ISPECL [`(:real^M)`; `(lambda i. B):real^N`]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MIN) THEN
        MP_TAC(ISPECL [`(:real^M)`; `(lambda i. --B):real^N`]
                  CONTINUOUS_ON_CONST) THEN
        REWRITE_TAC[IMP_IMP] THEN
        DISCH_THEN(MP_TAC o MATCH_MP CONTINUOUS_ON_MAX) THEN
        MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[LAMBDA_BETA; VEC_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[LIM_SEQUENTIALLY] THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `ee:real` THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
        MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
        MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(c - a:real^N) <= norm(b - a)
          ==> dist(b,a) < ee ==> dist(c,a) < ee`) THEN
        MATCH_MP_TAC NORM_LE_COMPONENTWISE THEN
        SIMP_TAC[LAMBDA_BETA; VECTOR_SUB_COMPONENT] THEN
        X_GEN_TAC `k:num` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o MATCH_MP NORM_BOUND_COMPONENT_LE) THEN
        DISCH_THEN(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. (g:num->real^M->real^N) n absolutely_integrable_on s`
    ASSUME_TAC THENL
     [X_GEN_TAC `n:num` THEN MATCH_MP_TAC
        MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
      EXISTS_TAC `(\x. lift(norm(B % vec 1:real^N))):real^M->real^1` THEN
      ASM_REWRITE_TAC[LIFT_DROP; INTEGRABLE_ON_CONST] THEN
      ONCE_REWRITE_TAC[GSYM MEASURABLE_ON_UNIV] THEN
      MATCH_MP_TAC(REWRITE_RULE[lebesgue_measurable; indicator]
          MEASURABLE_ON_RESTRICT) THEN
      ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON; ETA_AX] THEN
      MATCH_MP_TAC INTEGRABLE_IMP_MEASURABLE THEN
      ASM_REWRITE_TAC[GSYM MEASURABLE_INTEGRABLE];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n x. lift(norm((g:num->real^M->real^N) n x - h x))`;
      `(\x. vec 0):real^M->real^1`;
      `(\x. lift(B + norm(B % vec 1:real^N))):real^M->real^1`;
      `s DIFF k:real^M->bool`] DOMINATED_CONVERGENCE) THEN
    ASM_SIMP_TAC[INTEGRAL_0; INTEGRABLE_ON_CONST; MEASURABLE_DIFF;
                 NEGLIGIBLE_IMP_MEASURABLE] THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_LIFT; REAL_ABS_NORM] THEN REPEAT CONJ_TAC THENL
       [GEN_TAC THEN
        MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
        EXISTS_TAC `s:real^M->bool` THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                     ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REPEAT STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(g:real^N) <= b /\ norm(h) <= a ==> norm(g - h) <= a + b`) THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[GSYM LIM_NULL_NORM; GSYM LIM_NULL]];
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
      REWRITE_TAC[LE_REFL; DIST_0] THEN DISCH_TAC THEN
      EXISTS_TAC `(g:num->real^M->real^N) n` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm(integral s (\x. lift(norm(f x - h x)))) +
       norm(integral s (\x. lift(norm
             ((g:num->real^M->real^N) n x - h x))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(NORM_ARITH
         `norm(x:real^N) <= norm(y + z:real^N)
          ==> norm(x) <= norm(y) + norm(z)`) THEN
        W(MP_TAC o PART_MATCH (lhs o rand) (GSYM INTEGRAL_ADD) o
           rand o rand o snd) THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC(MESON[]
         `norm x = drop x /\ norm(a:real^N) <= drop x
          ==> norm a <= norm x`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC NORM_1_POS THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
          SIMP_TAC[DROP_ADD; LIFT_DROP; NORM_POS_LE; REAL_LE_ADD] THEN
          MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC;
          MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
          REWRITE_TAC[DROP_ADD; LIFT_DROP; NORM_LIFT; REAL_ABS_NORM] THEN
          REWRITE_TAC[NORM_ARITH
           `norm(f - g:real^N) <= norm(f - h) + norm(g - h)`] THEN
          CONJ_TAC THENL
           [ALL_TAC; MATCH_MP_TAC INTEGRABLE_ADD THEN CONJ_TAC]] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                     ABSOLUTELY_INTEGRABLE_SUB; ETA_AX];
        MATCH_MP_TAC(REAL_ARITH `a < e / &2 /\ b < e / &2 ==> a + b < e`) THEN
        ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
          (REAL_ARITH `x < e ==> x = y ==> y < e`)) THEN AP_TERM_TAC THEN
        MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
        MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(!u v. f absolutely_integrable_on (s INTER interval[u,v])) /\
    (!u v. (f:real^M->real^N) absolutely_integrable_on (s DIFF interval[u,v]))`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
                 LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b. norm(integral (s INTER interval[a,b]) (\x. lift(norm(f x))) -
               integral s (\x. lift(norm((f:real^M->real^N) x)))) < e / &3`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_integrable_on]) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[HAS_INTEGRAL_INTEGRAL] THEN
    REWRITE_TAC[HAS_INTEGRAL_ALT; INTEGRAL_RESTRICT_INTER] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &3` o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MESON_TAC[BOUNDED_SUBSET_CLOSED_INTERVAL; BOUNDED_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`f:real^M->real^N`; `s INTER interval[a:real^M,b]`; `e / &3`]
        lemma) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
               MEASURABLE_INTERVAL; REAL_ARITH `&0 < e / &3 <=> &0 < e`] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?c d. interval[a:real^M,b] SUBSET interval(c,d) /\
          measure(interval(c,d)) - measure(interval[a,b]) < e / &3 / B`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^M`; `b:real^M`;
                   `e / &3 / B / &2`]
        EXPAND_CLOSED_OPEN_INTERVAL) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF; REAL_ARITH `&0 < &3`] THEN
    REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REAL_ARITH
     `&0 < e ==> x <= y + e / &2 ==> x - y < e`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_ARITH `&0 < &3`];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\x. if x IN interval[a,b] then (g:real^M->real^N) x else vec 0`;
    `(:real^M)`;
    `interval[a,b] UNION ((:real^M) DIFF interval(c,d))`;
    `B:real`] TIETZE) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; IN_UNIV] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_IMP_LE; FORALL_IN_UNION] THEN
    SIMP_TAC[CLOSED_UNION; CLOSED_INTERVAL; GSYM OPEN_CLOSED; OPEN_INTERVAL;
             IN_DIFF; IN_UNIV] THEN
    ASM_SIMP_TAC[COND_RAND; NORM_0; COND_RATOR; REAL_LT_IMP_LE; COND_ID] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
    SIMP_TAC[CLOSED_INTERVAL; GSYM OPEN_CLOSED; OPEN_INTERVAL] THEN
    REWRITE_TAC[CONTINUOUS_ON_CONST] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ASM SET_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `h:real^M->real^N`] THEN
  REWRITE_TAC[FORALL_IN_UNION; bounded; FORALL_IN_IMAGE; IN_UNIV] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_EQ THEN
    EXISTS_TAC `\x. if x IN s INTER interval(c,d)
                    then (h:real^M->real^N) x else vec 0` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
    ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_INTER] THEN
    MATCH_MP_TAC
      MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_ABSOLUTELY_INTEGRABLE THEN
    EXISTS_TAC `(\x. lift B):real^M->real^1` THEN
    ASM_REWRITE_TAC[INTEGRABLE_CONST; LIFT_DROP] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_ON_CASES THEN
      ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = s`; MEASURABLE_ON_0] THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[INTEGRABLE_ON_OPEN_INTERVAL; INTEGRABLE_CONST];
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[NORM_0; REAL_LT_IMP_LE]];
    DISCH_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u v. h absolutely_integrable_on (s INTER interval[u,v])) /\
    (!u v. (h:real^M->real^N) absolutely_integrable_on (s DIFF interval[u,v]))`
  STRIP_ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[SET_RULE `s DIFF t = s INTER (UNIV DIFF t)`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_INTER;
                 LEBESGUE_MEASURABLE_INTERVAL; LEBESGUE_MEASURABLE_DIFF;
                 LEBESGUE_MEASURABLE_UNIV];
    ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `norm(integral (s INTER interval[a,b])
                   (\x. lift(norm((f:real^M->real^N) x - h x)))) +
     norm(integral (s DIFF interval[a,b])
                   (\x. lift(norm(f x - h x))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `a + b:real^N = c ==> norm(c) <= norm(a) + norm(b)`) THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; SET_RULE
     `(s INTER t) INTER (s DIFF t) = {} /\
      (s INTER t) UNION (s DIFF t) = s`] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
   `norm(integral s f) < e / &3
    ==> integral s f = integral s g /\
        y < &2 / &3 * e ==> norm(integral s g) + y < e`)) THEN
  CONJ_TAC THENL [MATCH_MP_TAC INTEGRAL_EQ THEN ASM SET_TAC[]; ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `drop(integral (s DIFF interval[a,b])
                   (\x. lift(norm((f:real^M->real^N) x)) +
                        lift(norm(h x:real^N))))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
                 ABSOLUTELY_INTEGRABLE_ADD; LIFT_DROP; DROP_ADD; NORM_LIFT;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    CONV_TAC NORM_ARITH;
    ASM_SIMP_TAC[INTEGRAL_ADD; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
                 ABSOLUTELY_INTEGRABLE_NORM; DROP_ADD]] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
   `x < e / &3 ==> z = x /\ y <= e / &3 ==> z + y < &2 / &3 * e`)) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[NORM_REAL; GSYM drop; DROP_SUB] THEN
    MATCH_MP_TAC(REAL_ARITH
     `z + y = x /\ &0 <= y ==> y = abs(z - x)`) THEN
    ASM_SIMP_TAC[INTEGRAL_DROP_POS; LIFT_DROP; NORM_POS_LE;
                  ABSOLUTELY_INTEGRABLE_NORM;
                  ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[GSYM DROP_ADD; DROP_EQ] THEN
    W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_UNION o lhand o snd) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; SET_RULE
     `(s INTER t) INTER (s DIFF t) = {} /\
      (s INTER t) UNION (s DIFF t) = s`]  THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `drop(integral (interval(c,d) DIFF interval[a,b]) (\x:real^M. lift B))` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM INTEGRAL_RESTRICT_UNIV] THEN
    MATCH_MP_TAC INTEGRAL_DROP_LE THEN
    ASM_REWRITE_TAC[INTEGRABLE_RESTRICT_UNIV; IN_UNIV] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; INTEGRABLE_ON_CONST;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_INTERVAL] THEN
    X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_DIFF] THEN
    ASM_CASES_TAC `x IN interval(c:real^M,d)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x IN interval[a:real^M,b]` THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC[REAL_LE_REFL; LIFT_DROP; NORM_0; REAL_LT_IMP_LE;
                 DROP_VEC] THEN
    ASM_MESON_TAC[IN_DIFF; IN_UNIV; NORM_0; REAL_LE_REFL];
    SIMP_TAC[LIFT_EQ_CMUL; INTEGRAL_CMUL; INTEGRABLE_ON_CONST;
             MEASURABLE_DIFF; MEASURABLE_INTERVAL; INTEGRAL_MEASURE] THEN
    REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `x < e ==> y = x ==> y <= e`)) THEN
    MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN
    ASM_REWRITE_TAC[MEASURABLE_INTERVAL]]);;

(* ------------------------------------------------------------------------- *)
(* A derivative-free formulation of (absolute) integration by parts.         *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTE_INTEGRATION_BY_PARTS = prove
 (`!(bop:real^M->real^N->real^P) (f:real^1->real^M) g f' g' a b.
        bilinear bop /\ drop a <= drop b /\
        f' absolutely_integrable_on interval[a,b] /\
        g' absolutely_integrable_on interval[a,b] /\
        (!x. x IN interval[a,b] ==> (f' has_integral f(x)) (interval[a,x])) /\
        (!x. x IN interval[a,b] ==> (g' has_integral g(x)) (interval[a,x]))
        ==> (\x. bop (f x) (g' x)) absolutely_integrable_on interval[a,b] /\
            (\x. bop (f' x) (g x)) absolutely_integrable_on interval[a,b] /\
            integral (interval[a,b]) (\x. bop (f x) (g' x)) +
            integral (interval[a,b]) (\x. bop (f' x) (g x)) =
            bop (f b) (g b) - bop (f a) (g a)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:real^1->real^M) continuous_on interval[a,b] /\
    (g:real^1->real^N) continuous_on interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_EQ THENL
     [EXISTS_TAC `\x. integral(interval[a,x]) (f':real^1->real^M)`;
      EXISTS_TAC `\x. integral(interval[a,x]) (g':real^1->real^N)`] THEN
    ASM_SIMP_TAC[INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(GEN `n:num`
   (ISPECL [`g':real^1->real^N`; `interval[a:real^1,b]`; `inv(&n + &1)`]
        ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS)) THEN
  MP_TAC(GEN `n:num`
   (ISPECL [`f':real^1->real^M`; `interval[a:real^1,b]`; `inv(&n + &1)`]
        ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS)) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL; REAL_LT_INV_EQ] THEN
  REWRITE_TAC[REAL_ARITH `&0 < &n + &1`; FORALL_AND_THM; SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff':num->real^1->real^M` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `gg':num->real^1->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(!n. ((ff':num->real^1->real^M) n) continuous_on interval[a,b]) /\
    (!n. ((gg':num->real^1->real^N) n) continuous_on interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]; ALL_TAC] THEN
  MAP_EVERY ABBREV_TAC
  [`ff = \n x. integral(interval[a,x]) ((ff':num->real^1->real^M) n)`;
   `gg = \n x. integral(interval[a,x]) ((gg':num->real^1->real^N) n)`] THEN
  SUBGOAL_THEN
   `(!n. (ff:num->real^1->real^M) n continuous_on interval[a,b]) /\
    (!n. (gg:num->real^1->real^N) n continuous_on interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MAP_EVERY EXPAND_TAC ["ff"; "gg"] THEN
    MATCH_MP_TAC INDEFINITE_INTEGRAL_CONTINUOUS_RIGHT THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^1->real^M) absolutely_integrable_on interval[a,b] /\
    (g:real^1->real^N) absolutely_integrable_on interval[a,b] /\
    (!n. (ff:num->real^1->real^M) n absolutely_integrable_on interval[a,b]) /\
    (!n. (gg:num->real^1->real^N) n absolutely_integrable_on interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_CONTINUOUS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!f:real^1->real^M g:real^1->real^N.
        f absolutely_integrable_on interval[a,b] /\
        g continuous_on interval[a,b]
        ==> (\x. (bop:real^M->real^N->real^P) (f x) (g x))
             absolutely_integrable_on interval[a,b]) /\
    (!f:real^1->real^M g:real^1->real^N.
        f continuous_on interval[a,b] /\
        g absolutely_integrable_on interval[a,b]
        ==> (\x. (bop:real^M->real^N->real^P) (f x) (g x))
             absolutely_integrable_on interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [MP_TAC(GEN `g:real^1->real^N`
       (ISPECL [`\x y. (bop:real^M->real^N->real^P) y x`;
                     `g:real^1->real^N`]
        ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT));
      MP_TAC(GEN `f:real^1->real^M`
       (ISPECL [`bop:real^M->real^N->real^P`; `f:real^1->real^M`]
        ABSOLUTELY_INTEGRABLE_BOUNDED_MEASURABLE_PRODUCT))] THEN
    ASM_REWRITE_TAC[BILINEAR_SWAP] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[CONTINUOUS_IMP_MEASURABLE_ON_CLOSED_SUBSET;
                 CLOSED_INTERVAL] THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[]; STRIP_TAC] THEN
  ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
  MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
  EXISTS_TAC `\n. (integral (interval [a,b]) (\x. bop (ff n x) (gg' n x)) +
                   integral (interval [a,b]) (\x. bop (ff' n x) (gg n x))) -
                  ((bop:real^M->real^N->real^P) (ff n b) (gg n b) -
                   bop ((ff:num->real^1->real^M) n a) (gg n a))` THEN
  REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC LIM_EVENTUALLY THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[VECTOR_ARITH
     `(i + j) - b:real^N = vec 0 <=> j = b - i`] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN MATCH_MP_TAC INTEGRATION_BY_PARTS THEN
    MAP_EVERY EXISTS_TAC
     [`(ff:num->real^1->real^M) n`; `(gg':num->real^1->real^N) n`;
      `{}:real^1->bool`] THEN
    ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY] THEN
    REWRITE_TAC[VECTOR_ARITH `b - a - (b - a - i):real^N = i`] THEN
    REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
    ASM_SIMP_TAC[BILINEAR_CONTINUOUS_ON_COMPOSE; ETA_AX;
                 ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    X_GEN_TAC `x:real^1` THEN REPEAT STRIP_TAC THENL
     [MP_TAC(ISPECL
       [`(ff':num->real^1->real^M) n`; `a:real^1`; `b:real^1`; `x:real^1`]
        INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE) THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET;
                      CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
        EXPAND_TAC "ff"];
      MP_TAC(ISPECL
       [`(gg':num->real^1->real^N) n`; `a:real^1`; `b:real^1`; `x:real^1`]
        INTEGRAL_HAS_VECTOR_DERIVATIVE_POINTWISE) THEN
      ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET;
                      CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN];
        EXPAND_TAC "gg"]] THEN
    REWRITE_TAC[has_vector_derivative; has_derivative] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [GSYM(CONJUNCT1
      INTERIOR_INTERVAL)]) THEN
    SIMP_TAC[NETLIMIT_WITHIN_INTERIOR; NETLIMIT_AT; LIM_WITHIN_INTERIOR]] THEN
  MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THENL
   [MATCH_MP_TAC LIM_ADD;
    MATCH_MP_TAC LIM_SUB THEN CONJ_TAC THEN
    MP_TAC(ISPECL [`sequentially`; `bop:real^M->real^N->real^P`]
     LIM_BILINEAR) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    (SUBGOAL_THEN
      `!x. x IN interval[a,b]
           ==> (f:real^1->real^M) x = integral (interval[a,x]) f' /\
               (g:real^1->real^N) x = integral (interval[a,x]) g'`
     MP_TAC THENL [ASM_MESON_TAC[INTEGRAL_UNIQUE]; ALL_TAC]) THEN
     ASM_SIMP_TAC[ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1] THEN
     DISCH_THEN(K ALL_TAC) THEN MAP_EVERY EXPAND_TAC ["ff"; "gg"] THEN
     REWRITE_TAC[INTEGRAL_REFL; LIM_CONST] THEN
     ONCE_REWRITE_TAC[LIM_NULL] THEN
     ASM_SIMP_TAC[GSYM INTEGRAL_SUB; INTEGRABLE_CONTINUOUS;
                  ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
     MATCH_MP_TAC LIM_NULL_COMPARISON THEN EXISTS_TAC `\n. inv(&n)` THEN
     REWRITE_TAC[SEQ_HARMONIC] THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
     EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
     W(MP_TAC o PART_MATCH (lhand o rand) ABSOLUTELY_INTEGRABLE_LE o
       lhand o snd) THEN
     ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB; ETA_AX] THEN
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
     ONCE_REWRITE_TAC[NORM_SUB] THEN
     MATCH_MP_TAC(REAL_ARITH `abs x < a ==> x <= a`) THEN
     REWRITE_TAC[GSYM ABS_DROP] THEN
     TRANS_TAC REAL_LTE_TRANS `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC REAL_LE_INV2 THEN
     REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
     UNDISCH_TAC `1 <= n` THEN ARITH_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `M:real` STRIP_ASSUME_TAC o MATCH_MP
   BILINEAR_BOUNDED_POS) THEN
  SUBGOAL_THEN
   `?B. &0 < B /\
        norm (integral(interval[a,b])
             (\x:real^1. lift(norm(f' x:real^M)))) <= B /\
        norm (integral(interval[a,b])
             (\x. lift(norm(g' x:real^N)))) <= B`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[NORM_REAL] THEN
    MESON_TAC[REAL_ARITH `&0 < max (abs a) (abs b) + &1 /\
                          abs a <= max (abs a) (abs b) + &1 /\
                          abs b <= max (abs a) (abs b) + &1`];
    ALL_TAC] THEN
  CONJ_TAC THEN ONCE_REWRITE_TAC[LIM_NULL] THEN REWRITE_TAC[] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; GSYM INTEGRAL_SUB;
               ABSOLUTELY_INTEGRABLE_CONTINUOUS; ETA_AX] THEN
  MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `\n. &2 * M * B * inv(&n + &1) + M * inv(&n + &1) pow 2` THEN
  REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ALL_TAC;
     REWRITE_TAC[LIFT_ADD; LIFT_CMUL] THEN MATCH_MP_TAC LIM_NULL_ADD THEN
     CONJ_TAC THEN REPEAT(MATCH_MP_TAC LIM_NULL_CMUL) THEN
     REWRITE_TAC[SEQ_HARMONIC_OFFSET] THEN
     SUBST1_TAC(VECTOR_ARITH `vec 0:real^1 = drop(vec 0) % vec 0`) THEN
     REWRITE_TAC[REAL_POW_2; LIFT_CMUL] THEN MATCH_MP_TAC LIM_MUL THEN
     REWRITE_TAC[o_DEF; LIFT_DROP; SEQ_HARMONIC_OFFSET]]) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THENL
   [ONCE_REWRITE_TAC[VECTOR_ARITH
     `bop a b - bop c d:real^N =
     (bop a b - bop a d) + (bop a d - bop c d)`];
    ONCE_REWRITE_TAC[VECTOR_ARITH
     `bop a b - bop c d:real^N =
     (bop a b - bop c b) + (bop c b - bop c d)`]] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_ADD o rand o lhand o snd) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
               INTEGRABLE_SUB; ETA_AX] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[REAL_ARITH
   `&2 * M * B * e + M * e pow 2 = M * (B + e) * e + M * B * e`] THEN
  MATCH_MP_TAC(NORM_ARITH
   `norm(x:real^N) <= a /\ norm y <= b ==> norm(x + y) <= a + b`) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [bilinear]) THEN
  DISCH_THEN(CONJUNCTS_THEN(MP_TAC o GEN_ALL o GSYM o MATCH_MP LINEAR_SUB o
        SPEC_ALL)) THEN
  SIMP_TAC[] THEN REPEAT(DISCH_THEN(K ALL_TAC)) THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_TRANS THENL
   [EXISTS_TAC `drop(integral(interval[a,b])
      (\x. lift(M * (B + inv(&n + &1)) *
                norm((gg':num->real^1->real^N) n x - g' x))))`;
    EXISTS_TAC `drop(integral(interval[a,b])
      (\x. lift(M * inv(&n + &1) * norm((g':real^1->real^N) x))))`;
    EXISTS_TAC `drop(integral(interval[a,b])
      (\x. lift(M * (B + inv(&n + &1)) *
                norm((ff':num->real^1->real^M) n x - f' x))))`;
    EXISTS_TAC `drop(integral(interval[a,b])
      (\x. lift(M * inv(&n + &1) *
                norm((f':real^1->real^M) x))))`] THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL;
     REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[LIFT_CMUL] THEN
     ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
      [INTEGRAL_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
       ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
       ABSOLUTELY_INTEGRABLE_CONTINUOUS; ETA_AX] THEN
     REWRITE_TAC[DROP_CMUL; GSYM REAL_MUL_ASSOC] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
     REWRITE_TAC[REAL_ARITH
      `inv x * a <= B * inv x <=> inv x * a <= inv x * B`] THEN
     MATCH_MP_TAC REAL_LE_LMUL THEN
     ASM_SIMP_TAC[REAL_LE_ADD; REAL_LT_IMP_LE; REAL_LE_INV_EQ; REAL_POS] THEN
     ONCE_REWRITE_TAC[NORM_SUB] THEN
     MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
     ASM_SIMP_TAC[GSYM ABS_DROP; REAL_LT_IMP_LE]]) THEN
  REWRITE_TAC[REAL_MUL_ASSOC] THEN REWRITE_TAC[LIFT_CMUL] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 4)
   [VECTOR_MUL_ASSOC; INTEGRABLE_CMUL; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE;
    ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_SUB;
    CONTINUOUS_ON_SUB; ABSOLUTELY_INTEGRABLE_CONTINUOUS; ETA_AX] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH
   `norm((bop:real^M->real^N->real^P) a b) <= M * norm a * norm b /\
    M * norm a * norm b <= c
    ==> norm(bop a b) <= c`) THEN
  ASM_REWRITE_TAC[DROP_CMUL; LIFT_DROP] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
  REWRITE_TAC[REAL_ARITH `a * x <= y * a <=> x * a <= y * a`] THEN
  MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE] THENL
   [MATCH_MP_TAC(NORM_ARITH
     `!f'. norm(f':real^N) <= B /\ norm(f - f') <= i
           ==> norm(f) <= B + i`) THEN
    EXISTS_TAC `(f:real^1->real^M) x` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(f:real^1->real^M) x = integral(interval[a,x]) f'`
      SUBST1_TAC THENL [ASM_MESON_TAC[INTEGRAL_UNIQUE]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) ABSOLUTELY_INTEGRABLE_LE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^1,b]` THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL];
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
      TRANS_TAC REAL_LE_TRANS
       `drop(integral (interval[a,b])
                      (\x. lift(norm((f':real^1->real^M) x))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
        REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL] THEN
        CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^1,b]` THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL];
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        ASM_SIMP_TAC[GSYM ABS_DROP; REAL_LT_IMP_LE]];
      ALL_TAC];
    ALL_TAC;
    MATCH_MP_TAC(NORM_ARITH
     `!g'. norm(g':real^N) <= B /\ norm(g - g') <= i
           ==> norm(g) <= B + i`) THEN
    EXISTS_TAC `(g:real^1->real^N) x` THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(g:real^1->real^N) x = integral(interval[a,x]) g'`
      SUBST1_TAC THENL [ASM_MESON_TAC[INTEGRAL_UNIQUE]; ALL_TAC] THEN
      W(MP_TAC o PART_MATCH (lhand o rand) ABSOLUTELY_INTEGRABLE_LE o
        lhand o snd) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^1,b]` THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL];
        MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
      TRANS_TAC REAL_LE_TRANS
       `drop(integral (interval[a,b])
                      (\x. lift(norm((g':real^1->real^N) x))))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
        REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL] THEN
        CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
        EXISTS_TAC `interval[a:real^1,b]` THEN
        ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL];
        MATCH_MP_TAC(REAL_ARITH `abs x <= a ==> x <= a`) THEN
        ASM_SIMP_TAC[GSYM ABS_DROP; REAL_LT_IMP_LE]];
      ALL_TAC];
    ALL_TAC] THEN
  (SUBGOAL_THEN
    `(f:real^1->real^M) x = integral(interval[a,x]) f' /\
     (g:real^1->real^N) x = integral(interval[a,x]) g'`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[INTEGRAL_UNIQUE];
      MAP_EVERY EXPAND_TAC ["ff"; "gg"]]) THEN
  (W(MP_TAC o PART_MATCH (rand o rand) INTEGRAL_SUB o rand o lhand o snd) THEN
   ANTS_TAC THENL
    [CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
     MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
     EXISTS_TAC `interval[a:real^1,b]` THEN
     ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL];
     DISCH_THEN(SUBST1_TAC o SYM)] THEN
   W(MP_TAC o PART_MATCH (lhand o rand) ABSOLUTELY_INTEGRABLE_LE o
     lhand o snd) THEN
   ANTS_TAC THENL
    [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN CONJ_TAC THEN
     MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
     EXISTS_TAC `interval[a:real^1,b]` THEN
     ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL; ETA_AX];
     MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)]) THEN
  REWRITE_TAC[] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
  FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[REAL_LE_TRANS; REAL_LT_IMP_LE]
   `norm(integral i f) < e ==> drop(integral j f) <= norm(integral i f)
    ==> drop(integral j f) <= e`) o SPEC `n:num`) THEN
  REWRITE_TAC[NORM_REAL; GSYM drop] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= x ==> a <= abs x`) THEN
  MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
  REWRITE_TAC[LIFT_DROP; NORM_POS_LE] THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL] THEN
  CONJ_TAC THEN MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
  EXISTS_TAC `interval[a:real^1,b]` THEN
  ASM_SIMP_TAC[SUBSET_INTERVAL_1; GSYM IN_INTERVAL_1; REAL_LE_REFL; ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Luzin's theorem (Talvila and Loeb's proof from Marius Junge's notes).     *)
(* ------------------------------------------------------------------------- *)

let LUZIN = prove
 (`!f:real^M->real^N s e.
        measurable s /\ f measurable_on s /\ &0 < e
        ==> ?k. compact k /\ k SUBSET s /\
                measure(s DIFF k) < e /\ f continuous_on k`,
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `v:num->real^N->bool` STRIP_ASSUME_TAC
    UNIV_SECOND_COUNTABLE_SEQUENCE THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
        MEASURABLE_ON_MEASURABLE_PREIMAGE_OPEN) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`]
        MEASURABLE_ON_MEASURABLE_PREIMAGE_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!n. ?k k'.
        compact k /\ k SUBSET {x | x IN s /\ (f:real^M->real^N) x IN v n} /\
        compact k' /\ k' SUBSET {x | x IN s /\ f x IN ((:real^N) DIFF v n)} /\
        measure(s DIFF (k UNION k')) < e / &4 / &2 pow n`
  MP_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`{x:real^M | x IN s /\ f(x) IN (v:num->real^N->bool) n}`;
                   `e / &4 / &2 / &2 pow n`] MEASURABLE_INNER_COMPACT) THEN
    ASM_SIMP_TAC[REAL_OF_NUM_LT; ARITH; REAL_LT_DIV; REAL_LT_POW2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`{x:real^M | x IN s /\ f(x) IN (:real^N) DIFF v(n:num)}`;
                   `e / &4 / &2 / &2 pow n`] MEASURABLE_INNER_COMPACT) THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; REAL_LT_DIV; REAL_POW_LT; REAL_OF_NUM_LT;
                 ARITH] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k':real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC
     `measure(({x | x IN s /\ (f:real^M->real^N) x IN v n} DIFF k) UNION
              ({x | x IN s /\ f x IN ((:real^N) DIFF v(n:num))} DIFF k'))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_COMPACT;
                   GSYM OPEN_CLOSED] THEN SET_TAC[];
      ASM_SIMP_TAC[MEASURE_UNION; MEASURABLE_DIFF; MEASURABLE_COMPACT;
                   GSYM OPEN_CLOSED; MEASURE_DIFF_SUBSET] THEN
      MATCH_MP_TAC(REAL_ARITH
       `s < k + e / &4 / &2 / d /\ s' < k' + e / &4 / &2 / d /\ m = &0
        ==> (s - k) + (s' - k') - m < e / &4 / d`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(MESON[MEASURE_EMPTY]
       `s = {} ==> measure s = &0`) THEN SET_TAC[]];
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; IN_DIFF; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`k:num->real^M->bool`; `k':num->real^M->bool`] THEN
    REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC] THEN
  EXISTS_TAC `INTERS {k n UNION k' n | n IN (:num)} :real^M->bool` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_INTERS THEN
    ASM_SIMP_TAC[FORALL_IN_GSPEC; COMPACT_UNION] THEN SET_TAC[];
    REWRITE_TAC[INTERS_GSPEC] THEN ASM SET_TAC[];
    REWRITE_TAC[DIFF_INTERS; SET_RULE
     `{f y | y IN {g x | x IN s}} = {f(g x) | x IN s}`] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
     (MESON[] `measurable s /\ measure s <= b ==> measure s <= b`) THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_UNION; MEASURABLE_COMPACT] THEN
    X_GEN_TAC `n:num` THEN MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `sum(0..n) (\i. e / &4 / &2 pow i)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_SIMP_TAC[real_div; SUM_LMUL; REAL_LE_LMUL_EQ; REAL_ARITH
     `(e * inv(&4)) * s <= e * inv(&2) <=> e * s <= e * &2`] THEN
    REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[REAL_ARITH
     `(&1 - s) / (&1 / &2) <= &2 <=> &0 <= s`] THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;

    REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[CONTINUOUS_WITHIN_OPEN; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?n:num. (f:real^M->real^N)(x) IN v(n) /\ v(n) SUBSET t`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_THEN
       `!s. open s ==> (?k. s:real^N->bool = UNIONS {v(n:num) | n IN k})`
       (MP_TAC o SPEC `t:real^N->bool`) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM; UNIONS_GSPEC] THEN ASM SET_TAC[];
      EXISTS_TAC `(:real^M) DIFF k'(n:num)` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]]]);;

let LUZIN_EQ,LUZIN_EQ_ALT = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k. compact k /\ k SUBSET s /\
                         measure(s DIFF k) < e /\ f continuous_on k)) /\
   (!f:real^M->real^N s.
        measurable s
        ==> (f measurable_on s <=>
             !e. &0 < e
                 ==> ?k g. compact k /\ k SUBSET s /\
                           measure(s DIFF k) < e /\
                           g continuous_on (:real^M) /\
                           (!x. x IN k ==> g x = f x)))`,
  REWRITE_TAC[AND_FORALL_THM] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `measurable(s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p) ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[LUZIN];
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `e:real` THEN
    ASM_CASES_TAC `&0 < e` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC TIETZE_UNBOUNDED THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN];
    DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `inv(&2 pow n)`) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    MAP_EVERY X_GEN_TAC [`k:num->real^M->bool`; `g:num->real^M->real^N`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LIMIT THEN MAP_EVERY EXISTS_TAC
     [`g:num->real^M->real^N`;
      `s DIFF UNIONS {INTERS {k m | n <= m} | n IN (:num)}:real^M->bool`] THEN
    REPEAT CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC CONTINUOUS_IMP_MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      ASM_MESON_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; CONTINUOUS_ON_SUBSET;
                    SUBSET_UNIV];
      SIMP_TAC[DIFF_UNIONS_NONEMPTY; SET_RULE `~({f x | x IN UNIV} = {})`] THEN
      REWRITE_TAC[NEGLIGIBLE_OUTER] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`inv(&2)`; `e / &4`] REAL_ARCH_POW_INV) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_POW_INV]] THEN
      DISCH_THEN(X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s DIFF INTERS {k m | n:num <= m}:real^M->bool` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[INTERS_GSPEC; FORALL_IN_GSPEC] THEN ASM SET_TAC[];
        MATCH_MP_TAC MEASURABLE_DIFF THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MEASURABLE_COUNTABLE_INTERS_GEN THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC; MEASURABLE_COMPACT] THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[LE_REFL]] THEN
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
        MATCH_MP_TAC COUNTABLE_IMAGE THEN
        MESON_TAC[NUM_COUNTABLE; COUNTABLE_SUBSET; SUBSET_UNIV];
        REWRITE_TAC[DIFF_INTERS] THEN
        MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC
         (MESON[] `measurable s /\ measure s <= b ==> measure s <= b`) THEN
        MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_GEN THEN
        ASM_SIMP_TAC[FORALL_IN_GSPEC; MEASURABLE_COMPACT; MEASURABLE_DIFF] THEN
        CONJ_TAC THENL
         [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          MATCH_MP_TAC COUNTABLE_IMAGE THEN
          REWRITE_TAC[SET_RULE `{x | x IN s} = s`] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          MATCH_MP_TAC COUNTABLE_IMAGE THEN
          MESON_TAC[NUM_COUNTABLE; COUNTABLE_SUBSET; SUBSET_UNIV];
          REWRITE_TAC[SIMPLE_IMAGE] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
          REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
          ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
          REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
          X_GEN_TAC `ns:num->bool` THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
          STRIP_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
          W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
          ASM_SIMP_TAC[o_DEF; MEASURE_POS_LE; MEASURABLE_DIFF;
                       MEASURABLE_COMPACT] THEN
          MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
          FIRST_ASSUM(MP_TAC o SPEC `\x:num. x` o
            MATCH_MP UPPER_BOUND_FINITE_SET) THEN
          REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `m:num` THEN
          STRIP_TAC THEN MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `sum (n..m) (\i. measure(s DIFF k i:real^M->bool))` THEN
          CONJ_TAC THENL
           [MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN
            ASM_SIMP_TAC[MEASURE_POS_LE; MEASURABLE_DIFF; MEASURABLE_COMPACT;
                         FINITE_NUMSEG; SUBSET; IN_NUMSEG];
            ALL_TAC] THEN
          MATCH_MP_TAC REAL_LE_TRANS THEN
          EXISTS_TAC `sum (n..m) (\i. inv(&2 pow i))` THEN
          ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE] THEN
          REWRITE_TAC[REAL_INV_POW; SUM_GP; LT] THEN
          COND_CASES_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN MATCH_MP_TAC(REAL_ARITH
           `a <= e / &4 /\ &0 <= b
            ==> (a - b) / (&1 / &2) <= e / &2`) THEN
          REWRITE_TAC[real_div; REAL_MUL_LID; REAL_POW_INV] THEN
          ASM_SIMP_TAC[GSYM real_div; REAL_LT_IMP_LE; REAL_LE_INV_EQ;
                       REAL_LT_POW2]]];
      REWRITE_TAC[SET_RULE `s DIFF (s DIFF t) = s INTER t`] THEN
      X_GEN_TAC `x:real^M` THEN REWRITE_TAC[UNIONS_GSPEC; IN_INTER] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM; INTERS_GSPEC] THEN
      STRIP_TAC THEN MATCH_MP_TAC LIM_EVENTUALLY THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Egorov's thoerem.                                                         *)
(* ------------------------------------------------------------------------- *)

let EGOROV = prove
 (`!f:num->real^M->real^N g s t.
        measurable s /\ negligible t /\
        (!n. f n measurable_on s) /\ g measurable_on s /\
        (!x. x IN s DIFF t ==> ((\n. f n x) --> g x) sequentially)
        ==> !d. &0 < d
                ==> ?k. k SUBSET s /\ measurable k /\ measure k < d /\
                        !e. &0 < e
                            ==> ?N. !n x. N <= n /\ x IN s DIFF k
                                          ==> dist(f n x,g x) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `e = \n m. UNIONS{{x | x IN s /\
                                    dist((f:num->real^M->real^N) k x,g x)
                                      >= inv(&m + &1)} | n <= k}` THEN
  SUBGOAL_THEN
   `!m n. measurable ((e:num->num->real^M->bool) n m)`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "e" THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[]] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
    SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_SUBSET_NUM; FORALL_IN_GSPEC] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[NORM_ARITH
     `dist(a:real^M,b) >= e <=> ~(dist(vec 0,a - b) < e)`] THEN
    REWRITE_TAC[GSYM IN_BALL; SET_RULE `~(x IN s) <=> x IN UNIV DIFF s`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_LEBESGUE_MEASURABLE_PREIMAGE_CLOSED THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; OPEN_BALL;
                 MEASURABLE_IMP_LEBESGUE_MEASURABLE] THEN
    MATCH_MP_TAC MEASURABLE_ON_SUB THEN CONJ_TAC THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] MEASURABLE_ON_SPIKE_SET) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[ETA_AX] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
     NEGLIGIBLE_SUBSET)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. ?k. measure((e:num->num->real^M->bool) k m) < d / &2 pow (m + 2)`
  MP_TAC THENL
   [GEN_TAC THEN MP_TAC(ISPEC
      `\n. (e:num->num->real^M->bool) n m` HAS_MEASURE_NESTED_INTERS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [GEN_TAC THEN EXPAND_TAC "e" THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ARITH_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)] THEN
    SUBGOAL_THEN
     `measure (INTERS {(e:num->num->real^M->bool) n m | n IN (:num)}) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MEASURE_EQ_0 THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^M->bool` THEN
      ASM_REWRITE_TAC[INTERS_GSPEC; SUBSET; IN_ELIM_THM; IN_UNIV] THEN
      X_GEN_TAC `x:real^M` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
      ASM_CASES_TAC `(x:real^M) IN t` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      EXPAND_TAC "e" THEN REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_DIFF] THEN
      ASM_CASES_TAC `(x:real^M) IN s` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LIM_SEQUENTIALLY; NOT_FORALL_THM; NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `inv(&m + &1)`) THEN
      REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &m + &1`] THEN
      REWRITE_TAC[DE_MORGAN_THM; real_ge; REAL_NOT_LE] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; LIFT_NUM; DIST_0; NORM_LIFT] THEN
    DISCH_THEN(MP_TAC o SPEC `d / &2 pow (m + 2)`) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_POW2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
    DISCH_THEN(MP_TAC o SPEC `N:num`) THEN REWRITE_TAC[LE_REFL] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `k:num->num` THEN DISCH_TAC] THEN
  EXISTS_TAC `UNIONS {(e:num->num->real^M->bool) (k m) m | m IN (:num)}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`\m. (e:num->num->real^M->bool) (k m) m`; `d / &2`]
        MEASURE_COUNTABLE_UNIONS_LE) THEN ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [X_GEN_TAC `n:num`;
      ASM_MESON_TAC[REAL_ARITH `&0 < d /\ x <= d / &2 ==> x < d`]] THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..n) (\m. d / &2 pow (m + 2))` THEN
    ASM_SIMP_TAC[SUM_LE_NUMSEG; REAL_LT_IMP_LE] THEN
    REWRITE_TAC[REAL_POW_ADD; real_div; REAL_INV_POW; REAL_MUL_ASSOC] THEN
    REWRITE_TAC[SUM_RMUL; SUM_LMUL; SUM_GP; CONJUNCT1 LT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    ASM_SIMP_TAC[REAL_LE_LMUL_EQ; GSYM REAL_MUL_ASSOC] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x ==> (&1 - x) / (&1 / &2) * &1 / &4 <= &1 / &2`) THEN
    MATCH_MP_TAC REAL_POW_LE THEN CONV_TAC REAL_RAT_REDUCE_CONV;

    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `m:num` THEN STRIP_TAC THEN EXISTS_TAC `(k:num->num) m` THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `x:real^M`] THEN EXPAND_TAC "e" THEN
    REWRITE_TAC[IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_EXISTS_THM; IN_UNIV] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPECL [`m:num`; `n:num`]) THEN
    ASM_REWRITE_TAC[REAL_NOT_LE; real_ge] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
     MATCH_MP (REAL_ARITH `i < e ==> m <= i ==> d < m ==> d < e`)) THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The Lebesgue differentiation theorem.                                     *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> negligible {x | x IN interval[a,b] /\ ~(f differentiable at x)}`,
  let lemma0 = prove
   (`k <= y - x ==> &0 < k
     ==> ?q. rational q /\ k / &3 < q - x /\ k / &3 < y - q`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`(x + y) / &2`; `k / &6`] RATIONAL_APPROXIMATION) THEN
    ANTS_TAC THENL [ALL_TAC; MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]] THEN
    ASM_REAL_ARITH_TAC) in
  let lemma1 = prove
   (`!f:real^1->real^1 a b.
          f has_bounded_variation_on interval[a,b]
          ==> ?t. negligible t /\
                  !x. x IN interval[a,b] DIFF t
                      ==> ?B. &0 < B /\
                              eventually
                               (\y. norm(f y - f x) <= B * norm(y - x))
                               (at x)`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?t. negligible t /\
          !x. x IN interval[a,b] DIFF t /\ (f:real^1->real^1) continuous at x
              ==> ?B. &0 < B /\
                      eventually
                        (\y. norm(f y - f x) <= B * norm(y - x)) (at x)`
    STRIP_ASSUME_TAC THENL
     [ALL_TAC;
      EXISTS_TAC `t UNION {x | x IN interval[a,b] /\
                               ~((f:real^1->real^1) continuous at x)}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; SET_RULE
       `x IN i DIFF (t UNION {x | x IN i /\ ~P x}) <=>
        x IN i DIFF t /\ P x`] THEN
      MATCH_MP_TAC NEGLIGIBLE_COUNTABLE THEN
      MATCH_MP_TAC HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES THEN
      ASM_REWRITE_TAC[]] THEN
    ABBREV_TAC
     `t = {x | x IN interval(a,b) /\
               (f:real^1->real^1) continuous at x /\
               ~(?B. &0 < B /\
                     eventually (\y. norm(f y - f x) <= B * norm (y - x))
                       (at x))}` THEN
    EXISTS_TAC `{a:real^1,b} UNION t` THEN CONJ_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY];
      EXPAND_TAC "t" THEN
      REWRITE_TAC[GSYM OPEN_CLOSED_INTERVAL_1;
                  SET_RULE `s DIFF (t UNION u) = s DIFF t DIFF u`] THEN
      EXPAND_TAC "t" THEN SET_TAC[]] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [has_bounded_variation_on]) THEN
    REWRITE_TAC[has_bounded_setvariation_on] THEN
    DISCH_THEN(X_CHOOSE_TAC `B:real`) THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!x. x IN t
          ==> ?u v. u IN interval[a,b] /\ v IN interval[a,b] /\
                    x IN interval(u,v) /\
                    (&3 * (abs B + &1) / e) * norm(v - u)
                    <= norm((f:real^1->real^1) u - f v)`
    MP_TAC THENL
     [ABBREV_TAC `M = &3 * (abs B + &1) / e` THEN
      SUBGOAL_THEN `&0 < M` ASSUME_TAC THENL
       [EXPAND_TAC "M" THEN
        REWRITE_TAC[REAL_ARITH `&0 < &3 * M <=> &0 < M`] THEN
        MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      X_GEN_TAC `x:real^1` THEN EXPAND_TAC "t" THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_EXISTS_THM] THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      DISCH_THEN(MP_TAC o SPEC `&3 * M`) THEN
      ASM_REWRITE_TAC[REAL_ARITH `&0 < &3 * M <=> &0 < M`] THEN
      REWRITE_TAC[EVENTUALLY_AT; NOT_EXISTS_THM] THEN
      MP_TAC(ISPEC `interval(a:real^1,b)` OPEN_CONTAINS_BALL) THEN
      REWRITE_TAC[OPEN_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^1` MP_TAC) THEN
      ASM_CASES_TAC `y:real^1 = x` THEN
      ASM_REWRITE_TAC[DIST_REFL; REAL_LT_REFL] THEN STRIP_TAC THEN
      SUBGOAL_THEN `y IN interval(a:real^1,b)` ASSUME_TAC THENL
       [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
      SUBGOAL_THEN `x IN interval[a:real^1,b] /\ y IN interval[a:real^1,b]`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
      MP_TAC(SPECL [`drop x`; `drop y`] REAL_LT_TOTAL) THEN
      ASM_REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [continuous_at]) THEN
      DISCH_THEN(MP_TAC o SPEC `M * norm(y - x:real^1)`) THEN
      ASM_SIMP_TAC[REAL_LT_MUL; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THENL
       [ABBREV_TAC `u = x - lift(min (norm(y - x)) (min d d') / &2)` THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1`)) THEN
        EXPAND_TAC "u" THEN
        REWRITE_TAC[NORM_ARITH `dist(x:real^1,x - a) = norm a`;
                    NORM_ARITH `dist(x - a:real^1,x) = norm a`] THEN
        REWRITE_TAC[NORM_LIFT] THEN ASM_REWRITE_TAC[] THEN
        REPEAT(ANTS_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC;
          DISCH_TAC]) THEN
        MAP_EVERY EXISTS_TAC [`u:real^1`; `y:real^1`] THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED] THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
          EXPAND_TAC "u" THEN REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
         `a < norm(y - x:real^N)
          ==> !b. dist(u,x) < b /\ c <= a - b ==> c <= norm(u - y)`)) THEN
        EXISTS_TAC `M * norm(y - x:real^1)` THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH
         `a <= (&3 * M) * y - M * y <=> a <= M * &2 * y`] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(x - u:real^N) <= norm(y - x)
          ==> norm(y - u) <= &2 * norm(y - x)`) THEN
        EXPAND_TAC "u" THEN
        REWRITE_TAC[NORM_LIFT; VECTOR_ARITH `x - (x - l):real^N = l`] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC;
        ABBREV_TAC `u = x + lift(min (norm(y - x)) (min d d') / &2)` THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1`)) THEN
        EXPAND_TAC "u" THEN
        REWRITE_TAC[NORM_ARITH `dist(x:real^1,x + a) = norm a`;
                    NORM_ARITH `dist(x + a:real^1,x) = norm a`] THEN
        REWRITE_TAC[NORM_LIFT] THEN ASM_REWRITE_TAC[] THEN
        REPEAT(ANTS_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC;
          DISCH_TAC]) THEN
        MAP_EVERY EXISTS_TAC [`y:real^1`; `u:real^1`] THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED] THEN
        CONJ_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
          ASM_REWRITE_TAC[IN_INTERVAL_1] THEN
          EXPAND_TAC "u" THEN REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
         `a < norm(y - x:real^N)
          ==> !b. dist(u,x) < b /\ c <= a - b ==> c <= norm(y - u)`)) THEN
        EXISTS_TAC `M * norm(y - x:real^1)` THEN ASM_REWRITE_TAC[] THEN
        ASM_SIMP_TAC[REAL_LE_LMUL_EQ; REAL_ARITH
         `a <= (&3 * M) * y - M * y <=> a <= M * &2 * y`] THEN
        MATCH_MP_TAC(NORM_ARITH
         `norm(x - u:real^N) <= norm(y - x)
          ==> norm(u - y) <= &2 * norm(y - x)`) THEN
        EXPAND_TAC "u" THEN
        REWRITE_TAC[NORM_LIFT; NORM_NEG; VECTOR_ARITH
          `x - (x + l):real^N = --l`] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[dist]) THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^1->real^1`; `v:real^1->real^1`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `IMAGE (\x:real^1. interval(u x:real^1,v x)) t`
          LINDELOF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_INTERVAL] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^1->bool` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[MESON[]
       `(?x. P x /\ Q x /\ R x) <=> ~(!x. Q x /\ P x ==> ~R x)`] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?p. FINITE p /\
          p SUBSET IMAGE (\x:real^1. interval[u x:real^1,v x]) c /\
          e < measure(UNIONS p)`
    MP_TAC THENL
     [ONCE_REWRITE_TAC[MESON[]
       `(?x. P x /\ Q x /\ R x) <=> ~(!x. Q x /\ P x ==> ~R x)`] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       (REWRITE_RULE[CONJ_ASSOC] MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN))) THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e < x ==> x <= e ==> F`) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `UNIONS(IMAGE f c) = u
        ==> t SUBSET u /\ (!x. x IN c ==> f x SUBSET g x)
            ==> t SUBSET UNIONS(IMAGE g c)`)) THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN ASM SET_TAC[];
      REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPEC `IMAGE (\x:real^1. interval[u x:real^1,v x]) p`
          AUSTIN_LEMMA) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:(real^1->bool)->bool` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `e < m ==> a < e / &3  ==> a >= m / &3 pow 1 ==> F`)) THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE]; ALL_TAC] THEN
      ASM_MESON_TAC[SUBSET; IN_IMAGE; MEASURABLE_INTERVAL];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS)] THEN
    SUBGOAL_THEN
     `e / &3 = (abs B + &1) / (&3 * (abs B + &1) / e)`
    SUBST1_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN CONV_TAC REAL_FIELD;
      ASM_SIMP_TAC[REAL_LT_RDIV_EQ; REAL_ARITH `&0 < &3 * M <=> &0 < M`;
                   REAL_LT_DIV; REAL_ARITH `&0 < abs B + &1`]] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= b ==> x < abs b + &1`) THEN
    FIRST_X_ASSUM(MP_TAC o SPECL
     [`D:(real^1->bool)->bool`; `UNIONS D:real^1->bool`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[division_of; GSYM CONJ_ASSOC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE]; ALL_TAC] THEN
      SIMP_TAC[SET_RULE `s IN t ==> s SUBSET UNIONS t`] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !x. x IN s ==> P x`)) THEN
        X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]; MESON_TAC[]] THEN
        ASM_MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
         `interior s SUBSET s /\ interior t SUBSET t /\
          DISJOINT s t ==> interior s INTER interior t = {}`) THEN
        REWRITE_TAC[INTERIOR_SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM SET_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
          `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> f x SUBSET u) ==> UNIONS s SUBSET u`)) THEN
        REWRITE_TAC[SUBSET_INTERVAL_1] THEN X_GEN_TAC `x:real^1` THEN
        DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL_1]] THEN
        REAL_ARITH_TAC];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LE_TRANS) THEN
      REWRITE_TAC[GSYM SUM_RMUL] THEN MATCH_MP_TAC SUM_LE THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE]; ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !x. x IN s ==> P x`)) THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_INTERVAL_1]] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `drop((u:real^1->real^1) x) <= drop(v x)` ASSUME_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (NORM_ARITH
       `x <= norm(u - v:real^N) ==> a <= x ==> a <= norm(v - u)`)) THEN
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      MATCH_MP_TAC(REAL_RING `x:real = y ==> x * c = c * y`) THEN
      ASM_REWRITE_TAC[MEASURE_INTERVAL_1; NORM_REAL] THEN
      REWRITE_TAC[GSYM drop; DROP_SUB] THEN ASM_REAL_ARITH_TAC]) in
  let lemma2 = prove
   (`!f a b k.
          f has_bounded_variation_on interval[a,b] /\ drop a < drop b /\ &0 < k
          ==> negligible
               {x | x IN interval[a,b] /\
                    !s. open s /\ x IN s
                        ==> (?u v. u IN interval[a,b] /\ u IN s /\
                                   v IN interval[a,b] /\ v IN s /\
                                   x IN interval(u,v) /\
                                   k <= (drop(f v) - drop(f u)) /
                                        (drop v - drop u)) /\
                            (?u v. u IN interval[a,b] /\ u IN s /\
                                   v IN interval[a,b] /\ v IN s /\
                                   x IN interval(u,v) /\
                                   (drop(f v) - drop(f u)) /
                                   (drop v - drop u) <= --k)}`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `(!t. s = t ==> negligible t) ==> negligible s`) THEN
    X_GEN_TAC `t':real^1->bool` THEN DISCH_TAC THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP
      HAS_BOUNDED_VARIATION_WORKS_ON_INTERVAL) THEN
    DISCH_THEN(MP_TAC o SPEC
     `vector_variation (interval[a,b]) (f:real^1->real^1) - k * e / &3`) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_ARITH `v <= v - e <=> ~(&0 < e)`;
                 REAL_ARITH `&0 < x / &3 <=> &0 < x`] THEN
    REWRITE_TAC[NOT_FORALL_THM; LEFT_IMP_EXISTS_THM; NOT_IMP; REAL_NOT_LE] THEN
    X_GEN_TAC `D:(real^1->bool)->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    ABBREV_TAC `t:real^1->bool = t' DIFF UNIONS {frontier i | i IN D}` THEN
    SUBGOAL_THEN `?c:real^1->bool. t SUBSET c /\ measurable c /\ measure c <= e`
    MP_TAC THENL
     [ALL_TAC;
      DISCH_THEN(X_CHOOSE_THEN `c:real^1->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `c UNION UNIONS {frontier i:real^1->bool | i IN D}` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `negligible(UNIONS {frontier i:real^1->bool | i IN D})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
        ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
        FIRST_ASSUM(fun th ->
          ONCE_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
        REPEAT STRIP_TAC THEN
        REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; OPEN_CLOSED_INTERVAL_1] THEN
        ASM_SIMP_TAC[ENDS_IN_INTERVAL; INSERT_SUBSET; EMPTY_SUBSET; SET_RULE
         `t SUBSET s ==> s DIFF (s DIFF t) = t`] THEN
        REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY];
        ASM_SIMP_TAC[MEASURABLE_UNION; NEGLIGIBLE_IMP_MEASURABLE] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          MEASURE_UNION_LE o lhand o snd) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[NEGLIGIBLE_EQ_MEASURE_0]) THEN
        ASM_SIMP_TAC[MEASURABLE_UNION] THEN ASM_REAL_ARITH_TAC]] THEN
    SUBGOAL_THEN
     `!x. x IN t
          ==> ?c d u v. interval[c,d] IN D /\
                        x IN interval(c,d) /\
                        u IN interval(c,d) /\
                        v IN interval(c,d) /\
                        x IN interval(u,v) /\
                        (drop(f c) <= drop(f d)
                         ==> drop(f v) - drop(f u)
                             <= --k * (drop v - drop u)) /\
                        (drop(f d) < drop(f c)
                         ==> k * (drop v - drop u) <= drop(f v) - drop(f u))`
    MP_TAC THENL
     [EXPAND_TAC "t" THEN REWRITE_TAC[IN_DIFF] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o last o CONJUNCTS o
        GEN_REWRITE_RULE I [division_of]) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^1` o MATCH_MP (SET_RULE
       `s = t ==> !x. x IN t ==> x IN s`)) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM; IMP_CONJ] THEN FIRST_ASSUM(fun th ->
        ONCE_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
      MAP_EVERY X_GEN_TAC [`c:real^1`; `d:real^1`] THEN
      REPEAT STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`c:real^1`; `d:real^1`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `interval[c:real^1,d]` o MATCH_MP
       (SET_RULE `~(x IN UNIONS {f y | y IN s})
                  ==> !a. a IN s ==> ~(x IN f a)`)) THEN
      ASM_REWRITE_TAC[FRONTIER_CLOSED_INTERVAL; IN_DIFF] THEN
      DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^1) IN t'` THEN EXPAND_TAC "t'" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
       (MP_TAC o SPEC `interval(c:real^1,d)`)) THEN
      ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
      DISJ_CASES_TAC(SPECL [`drop(f(c:real^1))`; `drop(f(d:real^1))`]
          REAL_LET_TOTAL) THEN
      ASM_REWRITE_TAC[] THENL
       [DISCH_THEN(MP_TAC o CONJUNCT2); DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^1` THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `v:real^1` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN TRY(DISCH_TAC THEN ASM_REAL_ARITH_TAC) THEN
      (SUBGOAL_THEN `drop u < drop v` ASSUME_TAC THENL
        [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
         ALL_TAC]) THEN
      ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_SUB_LT; GSYM REAL_LE_RDIV_EQ];
      ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC
     [`c:real^1->real^1`; `d:real^1->real^1`;
      `u:real^1->real^1`; `v:real^1->real^1`] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `IMAGE (\x:real^1. interval(u x:real^1,v x)) t`
          LINDELOF) THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_INTERVAL] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[EXISTS_COUNTABLE_SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^1->bool` STRIP_ASSUME_TAC) THEN
    ONCE_REWRITE_TAC[MESON[]
       `(?x. P x /\ Q x /\ R x) <=> ~(!x. Q x /\ P x ==> ~R x)`] THEN
    REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `?p. FINITE p /\
          p SUBSET IMAGE (\x:real^1. interval[u x:real^1,v x]) c /\
          e < measure(UNIONS p)`
    MP_TAC THENL
     [ONCE_REWRITE_TAC[MESON[]
       `(?x. P x /\ Q x /\ R x) <=> ~(!x. Q x /\ P x ==> ~R x)`] THEN
      REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       (REWRITE_RULE[CONJ_ASSOC] MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN))) THEN
      ASM_SIMP_TAC[COUNTABLE_IMAGE; FORALL_IN_IMAGE; MEASURABLE_INTERVAL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      MATCH_MP_TAC(REAL_ARITH `&0 < e /\ e < x ==> x <= e ==> F`) THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `UNIONS(IMAGE f c) = u
        ==> t SUBSET u /\ (!x. x IN c ==> f x SUBSET g x)
            ==> t SUBSET UNIONS(IMAGE g c)`)) THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN ASM SET_TAC[];
      REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^1->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPEC `IMAGE (\x:real^1. interval[u x:real^1,v x]) p`
          AUSTIN_LEMMA) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^1->bool)->bool` MP_TAC) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `e < m ==> a < e / &3  ==> a >= m / &3 pow 1 ==> F`)) THEN
    SUBGOAL_THEN
     `UNIONS d =
      UNIONS {UNIONS {i:real^1->bool | i IN d /\ i SUBSET j} | j IN D}`
    SUBST1_TAC THENL
     [REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN
      REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
      SUBGOAL_THEN `!i:real^1->bool. i IN d ==> ?j. j IN D /\ i SUBSET j`
      MP_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
        `s SUBSET IMAGE f t
         ==> (!x. x IN t ==> P(f x)) ==> !y. y IN s ==> P y`)) THEN
      X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      EXISTS_TAC `interval[(c:real^1->real^1) x,d x]` THEN
      ASM_REWRITE_TAC[] THEN
      TRANS_TAC SUBSET_TRANS `interval((c:real^1->real^1) x,d x)` THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `i:real^1->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MEASURABLE_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE];
        REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !y. y IN s ==> P y`)) THEN
        REWRITE_TAC[MEASURABLE_INTERVAL]];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS)] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE_LE o lhand o snd) THEN
    ASM_REWRITE_TAC[o_DEF] THEN ANTS_TAC THENL
     [X_GEN_TAC `i:real^1->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MEASURE_POS_LE THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE];
        REWRITE_TAC[FORALL_IN_GSPEC; IMP_CONJ] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !y. y IN s ==> P y`)) THEN
        REWRITE_TAC[MEASURABLE_INTERVAL]];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LET_TRANS)] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
      `v - e < s ==> v - s < e`)) THEN
    MP_TAC(ISPECL [`f:real^1->real^1`; `a:real^1`; `b:real^1`;
                   `D:(real^1->bool)->bool`] VECTOR_VARIATION_ON_DIVISION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_SIMP_TAC[GSYM SUM_SUB] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LET_TRANS) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th ->
       ONCE_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
    SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY] THEN
    MAP_EVERY X_GEN_TAC [`l:real^1`; `r:real^1`] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[GSYM REAL_LE_RDIV_EQ] THEN
    SUBGOAL_THEN `FINITE(d:(real^1->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; FINITE_IMAGE]; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE o lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; FORALL_IN_GSPEC] THEN ANTS_TAC THENL
     [REWRITE_TAC[IMP_CONJ] THEN FIRST_X_ASSUM(MATCH_MP_TAC o
        MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !y. y IN s ==> P y`)) THEN
      REWRITE_TAC[MEASURABLE_INTERVAL];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ; GSYM SUM_RMUL] THEN
    ABBREV_TAC `d' = {i | i IN d /\ i SUBSET interval[l:real^1,r]}` THEN
    SUBGOAL_THEN `FINITE(d':(real^1->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "d'" THEN ASM_SIMP_TAC[FINITE_RESTRICT];
      ALL_TAC] THEN
    SUBGOAL_THEN `pairwise DISJOINT (d':(real^1->bool)->bool)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          PAIRWISE_MONO)) THEN
      EXPAND_TAC "d'" THEN REWRITE_TAC[SUBSET_RESTRICT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d':(real^1->bool)->bool`; `l:real^1`; `r:real^1`]
          PARTIAL_DIVISION_EXTEND_INTERVAL) THEN
    ANTS_TAC THENL
     [EXPAND_TAC "d'" THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[division_of] THEN ASM_SIMP_TAC[FINITE_RESTRICT] THEN
      REWRITE_TAC[FORALL_AND_THM; TAUT
       `p ==> q /\ r <=> (p ==> q) /\ (p ==> r)`] THEN
      REPEAT CONJ_TAC THENL
       [SET_TAC[];
        EXPAND_TAC "d'" THEN REWRITE_TAC[IN_ELIM_THM; IMP_CONJ] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET IMAGE f t
          ==> (!x. x IN t ==> P(f x)) ==> !y. y IN s ==> P y`)) THEN
        X_GEN_TAC `x:real^1` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        REPEAT DISCH_TAC THEN EXISTS_TAC `x:real^1` THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERVAL_OPEN_SUBSET_CLOSED) THEN
        ASM SET_TAC[];
        ASM SET_TAC[];
        REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
         `interior s SUBSET s /\ interior t SUBSET t /\ DISJOINT s t
          ==> interior s INTER interior t = {}`) THEN
        REWRITE_TAC[INTERIOR_SUBSET] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pairwise]) THEN ASM_MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `d'':(real^1->bool)->bool`
        STRIP_ASSUME_TAC)] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP DIVISION_OF_FINITE) THEN
    REWRITE_TAC[NORM_1; DROP_SUB] THEN
    REWRITE_TAC[REAL_ARITH `abs(r - l) = if l <= r then r - l else l - r`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [TRANS_TAC REAL_LE_TRANS
       `sum d'' (\i. abs(drop(f(interval_upperbound i)) -
                         drop(f(interval_lowerbound i))) -
                     (drop((f:real^1->real^1)(interval_upperbound i)) -
                      drop(f(interval_lowerbound i))))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_INCLUDED THEN
        ASM_REWRITE_TAC[REAL_ARITH `&0 <= abs x - x`] THEN
        EXISTS_TAC `\x:real^1->bool. x` THEN
        REWRITE_TAC[TAUT `p /\ a = b /\ q <=> a = b /\ p /\ q`] THEN
        REWRITE_TAC[UNWIND_THM2] THEN MATCH_MP_TAC(SET_RULE
          `d' SUBSET d'' /\ (!x. x IN d'' ==> x IN d' ==> P x)
           ==> !x. x IN d' ==> x IN d'' /\ P x`) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
          ONCE_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
        SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY;
                 INTERVAL_UPPERBOUND_NONEMPTY] THEN
        MAP_EVERY X_GEN_TAC [`w:real^1`;`z:real^1`] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN
         `?x:real^1. x IN p /\ interval[w:real^1,z] = interval[u x,v x]`
        MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[EQ_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^1` (CONJUNCTS_THEN2 MP_TAC
         (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
        DISCH_TAC THEN
        ASM_SIMP_TAC[MEASURE_INTERVAL_1; GSYM INTERVAL_NE_EMPTY_1] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH
         `&0 <= k * a /\ x <= --k * a ==> a * k <= abs x - x`) THEN
        ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; GSYM INTERVAL_NE_EMPTY_1;
                     REAL_LT_IMP_LE] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ASSUME `D division_of interval[a:real^1,b]`) THEN
        REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o
         SPECL [`interval[l:real^1,r]`; `interval[(c:real^1->real^1) x,d x]`] o
         el 2 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[EQ_INTERVAL] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
        ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN MATCH_MP_TAC
         (SET_RULE `!u. u SUBSET t /\ ~(u = {}) ==> ~(t = {})`) THEN
        EXISTS_TAC `interval((u:real^1->real^1) x,v x)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM(CONJUNCT1 INTERIOR_INTERVAL)] THEN
          MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
          REWRITE_TAC[INTERIOR_INTERVAL; SUBSET_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
        W(MP_TAC o PART_MATCH (lhand o rand) SUM_SUB o lhand o snd) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `x <= x' /\ y = y' ==> x - y <= x' - y'`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`f:real^1->real^1`; `interval[l:real^1,r]`]
            HAS_BOUNDED_VARIATION_WORKS) THEN
          REWRITE_TAC[NORM_1; DROP_SUB] THEN
          ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM SET_TAC[];
          ASM_SIMP_TAC[GSYM DROP_SUB; GSYM(REWRITE_RULE[o_DEF] DROP_VSUM)] THEN
          AP_TERM_TAC THEN MATCH_MP_TAC ADDITIVE_DIVISION_1 THEN
          ASM_REWRITE_TAC[GSYM INTERVAL_NE_EMPTY_1]]];
      TRANS_TAC REAL_LE_TRANS
       `sum d'' (\i. abs(drop(f(interval_upperbound i)) -
                         drop(f(interval_lowerbound i))) +
                     (drop((f:real^1->real^1)(interval_upperbound i)) -
                      drop(f(interval_lowerbound i))))` THEN
      REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE_INCLUDED THEN
        ASM_REWRITE_TAC[REAL_ARITH `&0 <= abs x + x`] THEN
        EXISTS_TAC `\x:real^1->bool. x` THEN
        REWRITE_TAC[TAUT `p /\ a = b /\ q <=> a = b /\ p /\ q`] THEN
        REWRITE_TAC[UNWIND_THM2] THEN MATCH_MP_TAC(SET_RULE
          `d' SUBSET d'' /\ (!x. x IN d'' ==> x IN d' ==> P x)
           ==> !x. x IN d' ==> x IN d'' /\ P x`) THEN
        ASM_REWRITE_TAC[] THEN FIRST_ASSUM(fun th ->
          ONCE_REWRITE_TAC[MATCH_MP FORALL_IN_DIVISION_NONEMPTY th]) THEN
        SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY;
                 INTERVAL_UPPERBOUND_NONEMPTY] THEN
        MAP_EVERY X_GEN_TAC [`w:real^1`;`z:real^1`] THEN REPEAT STRIP_TAC THEN
        SUBGOAL_THEN
         `?x:real^1. x IN p /\ interval[w:real^1,z] = interval[u x,v x]`
        MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[EQ_INTERVAL] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^1` (CONJUNCTS_THEN2 MP_TAC
         (CONJUNCTS_THEN SUBST_ALL_TAC))) THEN
        DISCH_TAC THEN
        ASM_SIMP_TAC[MEASURE_INTERVAL_1; GSYM INTERVAL_NE_EMPTY_1] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
        ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
        MATCH_MP_TAC(REAL_ARITH `k * a <= x ==> a * k <= abs x + x`) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        MP_TAC(ASSUME `D division_of interval[a:real^1,b]`) THEN
        REWRITE_TAC[division_of] THEN DISCH_THEN(MP_TAC o
         SPECL [`interval[l:real^1,r]`; `interval[(c:real^1->real^1) x,d x]`] o
         el 2 o CONJUNCTS) THEN
        ASM_REWRITE_TAC[EQ_INTERVAL; GSYM REAL_NOT_LE] THEN
        GEN_REWRITE_TAC LAND_CONV [GSYM CONTRAPOS_THM] THEN
        ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN MATCH_MP_TAC
         (SET_RULE `!u. u SUBSET t /\ ~(u = {}) ==> ~(t = {})`) THEN
        EXISTS_TAC `interval((u:real^1->real^1) x,v x)` THEN
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM(CONJUNCT1 INTERIOR_INTERVAL)] THEN
          MATCH_MP_TAC SUBSET_INTERIOR THEN ASM SET_TAC[];
          REWRITE_TAC[INTERIOR_INTERVAL; SUBSET_INTERVAL_1] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
        ASM_SIMP_TAC[SUM_ADD] THEN MATCH_MP_TAC(REAL_ARITH
         `x <= x' /\ y = --y' ==> x + y <= x' - y'`) THEN
        CONJ_TAC THENL
         [MP_TAC(ISPECL [`f:real^1->real^1`; `interval[l:real^1,r]`]
            HAS_BOUNDED_VARIATION_WORKS) THEN
          REWRITE_TAC[NORM_1; DROP_SUB] THEN
          ANTS_TAC THENL [ALL_TAC; ASM_MESON_TAC[SUBSET_REFL]] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
            HAS_BOUNDED_VARIATION_ON_SUBSET)) THEN
          RULE_ASSUM_TAC(REWRITE_RULE[division_of]) THEN ASM SET_TAC[];
          REWRITE_TAC[REAL_NEG_SUB] THEN
          ASM_SIMP_TAC[GSYM DROP_SUB; GSYM(REWRITE_RULE[o_DEF] DROP_VSUM)] THEN
          AP_TERM_TAC THEN MATCH_MP_TAC ADDITIVE_DIVISION_1 THEN
          ASM_REWRITE_TAC[GSYM INTERVAL_NE_EMPTY_1]]]]) in
  let lemma3 = prove
   (`!f a b k.
      f has_bounded_variation_on interval[a,b] /\ drop a < drop b /\ &0 < k
      ==> negligible
           {x | x IN interval[a,b] /\
                !n. ?u v. u IN ball(x,inv(&n + &1)) /\ u IN interval[a,b] /\
                          v IN ball(x,inv(&n + &1)) /\ v IN interval[a,b] /\
                          ~(u = x) /\ ~(v = x) /\
                          k <= (drop(f v) - drop(f x)) / (drop v - drop x) /\
                          (drop(f u) - drop(f x)) / (drop u - drop x) <= --k}`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `k / &2` o MATCH_MP
     (ONCE_REWRITE_RULE[IMP_CONJ] lemma2)) THEN
    ASM_REWRITE_TAC[REAL_HALF] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP NEGLIGIBLE_COUNTABLE o MATCH_MP
      HAS_BOUNDED_VARIATION_COUNTABLE_DISCONTINUITIES) THEN
    SUBGOAL_THEN `negligible {a:real^1,b}` MP_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY]; ALL_TAC] THEN
    REWRITE_TAC[GSYM NEGLIGIBLE_UNION_EQ; IMP_IMP] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[TAUT `(p \/ ~q) \/ r <=> ~p /\ q ==> r`] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `s:real^1->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?n. ball(x:real^1,inv (&n + &1)) SUBSET s INTER interval(a,b)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `s INTER interval(a:real^1,b)` OPEN_CONTAINS_BALL) THEN
      ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^1`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT;
                        IN_INTER; NOT_IN_EMPTY];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN
      STRIP_TAC THEN TRANS_TAC SUBSET_TRANS `ball(x:real^1,e)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN
      TRANS_TAC REAL_LE_TRANS `inv(&n)` THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      MATCH_MP_TAC REAL_LE_INV2 THEN
      REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [SUBSET_INTER]) THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (SET_RULE
       `s SUBSET interval(a:real^1,b)
        ==> interval(a,b) SUBSET interval[a,b]
            ==> s SUBSET interval[a,b]`)) THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN STRIP_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(SPECL [`drop v`; `drop x`] REAL_LT_TOTAL) THEN
      ASM_REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
       [EXISTS_TAC `v:real^1` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `(\y. lift((drop(f v) - drop(f y)) / (drop v - drop y)))
          continuous at x`
        MP_TAC THENL
         [REWRITE_TAC[real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
          ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV) THEN
          ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; LIFT_SUB; LIFT_DROP] THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID];
          REWRITE_TAC[continuous_at; DIST_LIFT] THEN
          DISCH_THEN(MP_TAC o SPEC `k / &2`) THEN
          ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC `d:real` THEN STRIP_TAC] THEN
        EXISTS_TAC `x + lift(min d (inv(&n + &1)) / &2)` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x + r) = norm r`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < y`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_ADD;
            REAL_LT_ADDR; LIFT_DROP] THEN
          ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_INV_EQ] THEN
          REAL_ARITH_TAC;
          ONCE_REWRITE_TAC[REAL_ARITH `x / y:real = --x * --(inv y)`] THEN
          REWRITE_TAC[GSYM REAL_INV_NEG; REAL_NEG_SUB] THEN
          REWRITE_TAC[GSYM real_div] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `k <= y ==> abs(y' - y) < k / &2 ==> --k / -- &2 <= y'`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x + y:real^N,x) = norm y`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < x`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
        GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
        EXISTS_TAC `v:real^1` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `(\y. lift((drop(f v) - drop(f y)) / (drop v - drop y)))
          continuous at x`
        MP_TAC THENL
         [REWRITE_TAC[real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
          ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV) THEN
          ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; LIFT_SUB; LIFT_DROP] THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID];
          REWRITE_TAC[continuous_at; DIST_LIFT] THEN
          DISCH_THEN(MP_TAC o SPEC `k / &2`) THEN
          ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC `d:real` THEN STRIP_TAC] THEN
        EXISTS_TAC `x - lift(min d (inv(&n + &1)) / &2)` THEN
        ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> r /\ (p /\ q) /\ s`] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x - r) = norm r`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < y`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; LIFT_DROP] THEN
          REWRITE_TAC[REAL_ARITH `x - a < x <=> &0 < a`] THEN
          ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_INV_EQ] THEN
          REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `k <= y ==> abs(y' - y) < k / &2 ==> k / &2 <= y'`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x - y:real^N,x) = norm y`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < x`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC]];
      MP_TAC(SPECL [`drop u`; `drop x`] REAL_LT_TOTAL) THEN
      ASM_REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
       [EXISTS_TAC `u:real^1` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `(\y. lift((drop(f u) - drop(f y)) / (drop u - drop y)))
          continuous at x`
        MP_TAC THENL
         [REWRITE_TAC[real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
          ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV) THEN
          ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; LIFT_SUB; LIFT_DROP] THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID];
          REWRITE_TAC[continuous_at; DIST_LIFT] THEN
          DISCH_THEN(MP_TAC o SPEC `k / &2`) THEN
          ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC `d:real` THEN STRIP_TAC] THEN
        EXISTS_TAC `x + lift(min d (inv(&n + &1)) / &2)` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ONCE_REWRITE_TAC[CONJ_ASSOC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x + r) = norm r`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < y`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_ADD;
            REAL_LT_ADDR; LIFT_DROP] THEN
          ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_INV_EQ] THEN
          REAL_ARITH_TAC;
          ONCE_REWRITE_TAC[REAL_ARITH `x / y:real = --x * --(inv y)`] THEN
          REWRITE_TAC[GSYM REAL_INV_NEG; REAL_NEG_SUB] THEN
          REWRITE_TAC[GSYM real_div] THEN
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `y <= --k ==> abs(y' - y) < k / &2 ==> y' <= --(--k / -- &2)`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x + y:real^N,x) = norm y`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < x`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC];
        GEN_REWRITE_TAC I [SWAP_EXISTS_THM] THEN
        EXISTS_TAC `u:real^1` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `(\y. lift((drop(f u) - drop(f y)) / (drop u - drop y)))
          continuous at x`
        MP_TAC THENL
         [REWRITE_TAC[real_div; LIFT_CMUL] THEN
          MATCH_MP_TAC CONTINUOUS_MUL THEN
          REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP] THEN
          ASM_SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST] THEN
          MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_AT_INV) THEN
          ASM_SIMP_TAC[REAL_SUB_0; DROP_EQ; LIFT_SUB; LIFT_DROP] THEN
          SIMP_TAC[CONTINUOUS_SUB; CONTINUOUS_CONST; CONTINUOUS_AT_ID];
          REWRITE_TAC[continuous_at; DIST_LIFT] THEN
          DISCH_THEN(MP_TAC o SPEC `k / &2`) THEN
          ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
          X_GEN_TAC `d:real` THEN STRIP_TAC] THEN
        EXISTS_TAC `x - lift(min d (inv(&n + &1)) / &2)` THEN
        ONCE_REWRITE_TAC[TAUT `p /\ q /\ r /\ s <=> r /\ (p /\ q) /\ s`] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^N,x - r) = norm r`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < y`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
          ALL_TAC] THEN
        CONJ_TAC THENL
         [ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_SUB; LIFT_DROP] THEN
          REWRITE_TAC[REAL_ARITH `x - a < x <=> &0 < a`] THEN
          ASM_REWRITE_TAC[REAL_LT_MIN; REAL_HALF; REAL_LT_INV_EQ] THEN
          REAL_ARITH_TAC;
          FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
           `y <= --k ==> abs(y' - y) < k / &2 ==> y' <= --(k / &2)`)) THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN
          REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x - y:real^N,x) = norm y`] THEN
          REWRITE_TAC[NORM_LIFT] THEN MATCH_MP_TAC(REAL_ARITH
           `&0 < x /\ &0 < y ==> abs(min x y / &2) < x`) THEN
          ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC]]]) in
  let lemma4 = prove
   (`!f a b k.
      f has_bounded_variation_on interval[a,b] /\ drop a < drop b /\ &0 < k
      ==> negligible
           {x | x IN interval[a,b] /\
                !n. ?u v. u IN ball(x,inv(&n + &1)) /\ u IN interval[a,b] /\
                          v IN ball(x,inv(&n + &1)) /\ v IN interval[a,b] /\
                          ~(u = x) /\ ~(v = x) /\
                          k <= (drop(f v) - drop(f x)) / (drop v - drop x) -
                               (drop(f u) - drop(f x)) / (drop u - drop x)}`,
    REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP lemma1) THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC
     `u UNION
      UNIONS
       {{x | x IN interval[a,b] /\
             !n. ?u v.  u IN ball(x,inv(&n + &1)) /\ u IN interval[a,b] /\
                        v IN ball(x,inv(&n + &1)) /\ v IN interval[a,b] /\
                        ~(u = x) /\ ~(v = x) /\
                        k / &3 <= (drop(f v) - drop(f x)) /
                                  (drop v - drop x) - q /\
                        (drop(f u) - drop(f x)) / (drop u - drop x) - q
                        <= --(k / &3)} |
        q IN rational}` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
      SIMP_TAC[COUNTABLE_RATIONAL; COUNTABLE_IMAGE; SIMPLE_IMAGE] THEN
      REWRITE_TAC[FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `q:real` THEN DISCH_THEN(K ALL_TAC) THEN
      MP_TAC(ISPECL
       [`\x:real^1. f(x) - q % x`; `a:real^1`; `b:real^1`; `k / &3`]
          lemma3) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_SUB THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CMUL THEN
        SIMP_TAC[HAS_BOUNDED_VARIATION_ON_ID; BOUNDED_INTERVAL];
        REWRITE_TAC[DROP_SUB; DROP_CMUL; REAL_ARITH
         `((a - q * a') - (b - q * b')) / i:real =
          (a - b) / i - q * (a' - b') / i`] THEN
        ONCE_REWRITE_TAC[TAUT
         `p /\ q /\ r /\ s /\ t /\ u /\ v <=>
          ~(t /\ u ==> ~(p /\ q /\ r /\ s /\ v))`] THEN
        SIMP_TAC[REAL_DIV_REFL; DROP_EQ; REAL_SUB_0; REAL_MUL_RID]];
      GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      ASM_CASES_TAC `(x:real^1) IN u` THEN ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN
     `?N B. &0 < B /\
            !n u. N <= n /\ u IN ball(x,inv(&n + &1)) /\ ~(u = x)
                  ==> abs((drop(f u) - drop(f x)) / (drop u - drop x)) <= B`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
      ASM_REWRITE_TAC[IN_DIFF] THEN
      ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `B:real` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      REWRITE_TAC[EVENTUALLY_AT; GSYM DIST_NZ; IN_BALL] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `N:num` THEN STRIP_TAC THEN
      MAP_EVERY X_GEN_TAC [`n:num`; `u:real^1`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^1`) THEN ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
        TRANS_TAC REAL_LT_TRANS `inv(&n + &1)` THEN ASM_REWRITE_TAC[] THEN
        TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LT; REAL_OF_NUM_LE] THEN
        ASM_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ABS_DIV; REAL_LE_LDIV_EQ; GSYM REAL_ABS_NZ;
                     REAL_SUB_0; DROP_EQ] THEN
        REWRITE_TAC[GSYM DROP_SUB; GSYM NORM_1]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!n. ~({ u:real^1 |
              u IN ball(x,inv(&n + &1)) /\
              u IN interval[a,b] /\ ~(u = x)} = {})`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC(SET_RULE
       `interval(a,b) SUBSET interval[a,b] /\
        ~(s INTER interval(a,b) SUBSET {c})
        ==> ~({x | x IN s /\ x IN interval[a,b] /\ ~(x = c)} = {})`) THEN
      REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED; BALL_1] THEN
      REWRITE_TAC[GSYM(CONJUNCT1 INTERIOR_INTERVAL)] THEN
      REWRITE_TAC[GSYM INTERIOR_INTER; INTER_INTERVAL_1] THEN
      DISCH_THEN(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
      REWRITE_TAC[GSYM INTERVAL_SING; CLOSURE_INTERVAL] THEN
      MATCH_MP_TAC(MESON[CONVEX_CLOSURE_INTERIOR]
       `convex s /\ ~(interior s = {}) /\ closure s = s /\ ~(s SUBSET t)
        ==> ~(closure(interior s) SUBSET t)`) THEN
      REWRITE_TAC[CONVEX_INTERVAL; CLOSURE_INTERVAL] THEN
      REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_EQ_EMPTY_1; SUBSET_INTERVAL_1;
                  LIFT_DROP; DROP_ADD; DROP_SUB] THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERVAL_1]) THEN
      MP_TAC(ISPEC `&n + &1` REAL_LT_INV_EQ) THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?l. ((\n. lift(inf {(drop (f u) - drop (f x)) / (drop u - drop x) |u|
                          u IN ball (x,inv (&n + &1)) /\ u IN interval[a,b] /\
                          ~(u = x)}))
           --> l) sequentially`
    (CHOOSE_THEN (LABEL_TAC "l")) THENL
     [MATCH_MP_TAC(MATCH_MP MONO_EXISTS (GEN `l:real^1`
       (ISPECL [`f:num->real^1`; `l:real^1`; `N:num`] SEQ_OFFSET_REV))) THEN
      MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE_1 THEN
      REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
        EXISTS_TAC `B:real` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_LIFT; REAL_ABS_BOUNDS] THEN
        MATCH_MP_TAC REAL_INF_BOUNDS THEN
        REWRITE_TAC[GSYM REAL_ABS_BOUNDS; FORALL_IN_GSPEC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[ARITH_RULE `N:num <= n + N`];
        DISJ1_TAC THEN X_GEN_TAC `n:num` THEN
        MATCH_MP_TAC REAL_LE_INF_SUBSET THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `b SUBSET c
            ==> {f x | x IN b /\ P x} SUBSET {f x | x IN c /\ P x}`) THEN
          MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
          ARITH_TAC;
          EXISTS_TAC `--B:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
          ASM_MESON_TAC[ARITH_RULE `N:num <= n + N`;
                        REAL_ARITH `abs x <= B ==> --B <= x`]]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?m. ((\n. lift(sup {(drop (f u) - drop (f x)) / (drop u - drop x) |u|
                          u IN ball (x,inv (&n + &1)) /\ u IN interval[a,b] /\
                          ~(u = x)}))
           --> m) sequentially`
    (CHOOSE_THEN (LABEL_TAC "m")) THENL
     [MATCH_MP_TAC(MATCH_MP MONO_EXISTS (GEN `l:real^1`
       (ISPECL [`f:num->real^1`; `l:real^1`; `N:num`] SEQ_OFFSET_REV))) THEN
      MATCH_MP_TAC CONVERGENT_BOUNDED_MONOTONE_1 THEN
      REWRITE_TAC[LIFT_DROP] THEN CONJ_TAC THENL
       [REWRITE_TAC[bounded; FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
        EXISTS_TAC `B:real` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
        REWRITE_TAC[NORM_LIFT; REAL_ABS_BOUNDS] THEN
        MATCH_MP_TAC REAL_SUP_BOUNDS THEN
        REWRITE_TAC[GSYM REAL_ABS_BOUNDS; FORALL_IN_GSPEC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[ARITH_RULE `N:num <= n + N`];
        DISJ2_TAC THEN X_GEN_TAC `n:num` THEN
        MATCH_MP_TAC REAL_SUP_LE_SUBSET THEN REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
         [MATCH_MP_TAC(SET_RULE
           `b SUBSET c
            ==> {f x | x IN b /\ P x} SUBSET {f x | x IN c /\ P x}`) THEN
          MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_INV2 THEN
          REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
          ARITH_TAC;
          EXISTS_TAC `B:real` THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
          ASM_MESON_TAC[ARITH_RULE `N:num <= n + N`;
                        REAL_ARITH `abs x <= B ==> x <= B`]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `k <= drop m - drop l` MP_TAC THENL
     [REMOVE_THEN "l" MP_TAC THEN REMOVE_THEN "m" MP_TAC THEN
      REWRITE_TAC[IMP_IMP] THEN DISCH_THEN(MP_TAC o MATCH_MP LIM_SUB) THEN
      REWRITE_TAC[GSYM DROP_SUB] THEN
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT] LIM_DROP_LBOUND) THEN
      REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; DROP_SUB; LIFT_DROP] THEN
      REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `N:num` THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_LE_SUB_LADD] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `u:real^1` MP_TAC o SPEC `n:num`) THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^1` MP_TAC) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      MATCH_MP_TAC(REAL_ARITH
       `i <= u /\ v <= s ==> k <= v - u ==> k + i <= s`) THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INF_LE_ELEMENT; MATCH_MP_TAC ELEMENT_LE_SUP] THEN
      (CONJ_TAC THENL [REWRITE_TAC[FORALL_IN_GSPEC]; ASM SET_TAC[]]) THENL
       [EXISTS_TAC `--B:real`; EXISTS_TAC `B:real`] THEN
      ASM_MESON_TAC[ARITH_RULE `N:num <= n + N`;
                    REAL_ARITH `abs x <= B ==> --B <= x /\ x <= B`];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP lemma0) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real` THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[IN]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[TAUT
     `p1 /\ q1 /\ p2 /\ q2 /\ r1 /\ r2 /\ s2 /\ s1 <=>
      (p1 /\ q1 /\ r1 /\ s1) /\ (p2 /\ q2 /\ r2 /\ s2)`] THEN
    REWRITE_TAC[LEFT_EXISTS_AND_THM; RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THEN
    REWRITE_TAC[REAL_LE_LT; LEFT_OR_DISTRIB; EXISTS_OR_THM] THEN
    DISJ1_TAC THEN REWRITE_TAC[REAL_NOT_LT; SET_RULE
     `(?u. p u /\ q u /\ r u /\ s u) <=>
      ~(!u. p u /\ q u /\ r u ==> ~s u)`] THEN
    REWRITE_TAC[REAL_ARITH `--k <= a - b <=> b - k <= a`;
                REAL_ARITH `a - b <= k / &3 <=> a <= k / &3 + b`]
    THENL
     [REMOVE_THEN "l" MP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `(q - drop l) - k / &3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M + n:num`)) THEN
      REWRITE_TAC[LE_ADD; DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
       `abs(j - l) < q - l - k ==> ~(q - k <= j)`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
          REAL_LE_INF));
      REMOVE_THEN "m" MP_TAC THEN REWRITE_TAC[LIM_SEQUENTIALLY] THEN
      DISCH_THEN(MP_TAC o SPEC `(drop m - q) - k / &3`) THEN
      ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `M:num` (MP_TAC o SPEC `M + n:num`)) THEN
      REWRITE_TAC[LE_ADD; DIST_REAL; GSYM drop; LIFT_DROP] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (REAL_ARITH
       `abs(j - m) < m - q - k ==> ~(j <= k + q)`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[GSYM CONTRAPOS_THM]
          REAL_SUP_LE))] THEN
    MATCH_MP_TAC (TAUT `p /\ (r ==> q) ==>  ~(p /\ q) ==> ~r`) THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IMP_IMP] THEN
    MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ARITH_TAC) in
  let lemma5 = prove
   (`!f a b k.
      f has_bounded_variation_on interval[a,b] /\ drop a < drop b /\ &0 < k
      ==> negligible
           {x | x IN interval[a,b] /\
                !n. ?u v. u IN ball(x,inv(&n + &1)) /\ u IN interval[a,b] /\
                          v IN ball(x,inv(&n + &1)) /\ v IN interval[a,b] /\
                          ~(u = x) /\ ~(v = x) /\
                          k <= abs((drop(f v) - drop(f x)) /
                                   (drop v - drop x) -
                                   (drop(f u) - drop(f x)) /
                                   (drop u - drop x))}`,
    REPEAT STRIP_TAC THEN MP_TAC(ISPECL
     [`(--) o (f:real^1->real^1)`; `a:real^1`; `b:real^1`; `k:real`]
          lemma4) THEN
    MP_TAC(ISPECL
     [`f:real^1->real^1`; `a:real^1`; `b:real^1`; `k:real`] lemma4) THEN
    ASM_SIMP_TAC[HAS_BOUNDED_VARIATION_ISOMETRIC_COMPOSE;
                NORM_ARITH `dist(--x:real^N,--y) = dist(x,y)`] THEN
    REWRITE_TAC[IMP_IMP; GSYM NEGLIGIBLE_UNION_EQ] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[LEFT_OR_FORALL_THM] THEN
    REWRITE_TAC[RIGHT_OR_FORALL_THM] THEN
    MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m + n:num`) THEN
    REWRITE_TAC[REAL_ARITH `a <= abs x <=> a <= x \/ a <= --x`; o_DEF;
                TAUT `p /\ (q \/ r) <=> p /\ q \/ p /\ r`; EXISTS_OR_THM] THEN
    MATCH_MP_TAC MONO_OR THEN
    CONJ_TAC THEN REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
    REWRITE_TAC[DROP_NEG; REAL_ARITH `--x - --y:real = --(x - y)`;
                REAL_ARITH `--a / b:real = --(a / b)`] THEN
    REPEAT(MATCH_MP_TAC MONO_AND THEN CONJ_TAC) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> x IN s ==> x IN t`) THEN
    MATCH_MP_TAC SUBSET_BALL THEN REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN REAL_ARITH_TAC) in
  let lemma6 = prove
   (`!f:real^1->real^1 a b.
      f has_bounded_variation_on interval[a,b] /\ drop a < drop b
      ==> negligible {x | x IN interval[a,b] /\
                          ~(f differentiable (at x within interval[a,b]))}`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN
    REWRITE_TAC[has_vector_derivative; EXISTS_LIFT] THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_DROP; has_derivative_within] THEN
    REWRITE_TAC[EXISTS_DROP; LIFT_DROP; LINEAR_SCALING] THEN
    REWRITE_TAC[NORM_1; GSYM REAL_ABS_INV] THEN
    ONCE_REWRITE_TAC[LIM_NULL_NORM] THEN
    REWRITE_TAC[NORM_MUL; REAL_ABS_ABS] THEN REWRITE_TAC[GSYM NORM_MUL] THEN
    REWRITE_TAC[GSYM LIM_NULL_NORM] THEN ONCE_REWRITE_TAC[VECTOR_ARITH
     `a % (y - (x + d)):real^N = a % (y - x) - a % d`] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ONCE_REWRITE_TAC[MESON[LIFT_DROP] `a % x = a % lift(drop x)`] THEN
    REWRITE_TAC[GSYM LIFT_CMUL] THEN
    SIMP_TAC[DROP_EQ; DROP_SUB; REAL_FIELD
     `~(x' = x) ==> (inv(x' - x) * h) * (x' - x):real = h`] THEN
    REWRITE_TAC[LIFT_DROP;
                ONCE_REWRITE_RULE[REAL_MUL_SYM] (GSYM real_div)] THEN
    REWRITE_TAC[GSYM LIM_NULL] THEN
    REWRITE_TAC[CONVERGENT_EQ_CAUCHY_WITHIN; DIST_LIFT] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC
     `UNIONS {{x | x IN interval[a,b] /\
                  !n. ?u v. u IN ball(x,inv(&n + &1)) /\ u IN interval[a,b] /\
                            v IN ball(x,inv(&n + &1)) /\ v IN interval[a,b] /\
                            ~(u = x) /\ ~(v = x) /\
                            inv(&m + &1)
                            <= abs((drop(f v) - drop(f x)) /
                                   (drop v - drop x) -
                                   (drop(f u) - drop(f x)) /
                                   (drop u - drop x))}
              | m IN (:num)}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN GEN_TAC THEN
      MATCH_MP_TAC lemma5 THEN
      ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN REAL_ARITH_TAC;
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^1` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
      ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
      MATCH_MP_TAC FORALL_POS_MONO_1 THEN CONJ_TAC THENL
       [REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
        MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[REAL_LT_TRANS];
        X_GEN_TAC `n:num` THEN FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
        REWRITE_TAC[GSYM REAL_NOT_LT; NOT_FORALL_THM; GSYM DIST_NZ] THEN
        REWRITE_TAC[IN_BALL] THEN DISCH_THEN(X_CHOOSE_TAC `p:num`) THEN
        EXISTS_TAC `inv(&p + &1)` THEN
        REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
        ASM_MESON_TAC[DIST_SYM]]]) in
  let lemma7 = prove
   (`!f:real^1->real^1 a b k.
      f has_bounded_variation_on interval[a,b]
      ==> negligible {x | x IN interval[a,b] /\ ~(f differentiable at x)}`,
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; EMPTY_GSPEC; NEGLIGIBLE_EMPTY] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP (REAL_ARITH
     `a <= b ==> a = b \/ a < b`)) THEN
    REWRITE_TAC[DROP_EQ] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[INTERVAL_SING] THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `{b:real^1}` THEN
      REWRITE_TAC[SUBSET_RESTRICT; NEGLIGIBLE_SING];
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
      EXISTS_TAC `(a:real^1) INSERT b INSERT
                  {x | x IN interval[a,b] /\
                            ~((f:real^1->real^1) differentiable
                              (at x within interval[a,b]))}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_INSERT] THEN CONJ_TAC THENL
       [MATCH_MP_TAC lemma6 THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s /\ ~(x = a) /\ ~(x = b) ==> (Q x <=> P x))
        ==> {x | x IN s /\ P x} SUBSET
             a INSERT b INSERT {x | x IN s /\ Q x}`) THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[VECTOR_DIFFERENTIABLE] THEN AP_TERM_TAC THEN ABS_TAC THEN
      REWRITE_TAC[has_vector_derivative] THEN
      REWRITE_TAC[has_derivative_at; has_derivative_within] THEN
      AP_TERM_TAC THEN MATCH_MP_TAC LIM_WITHIN_INTERIOR THEN
      REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; INTERIOR_INTERVAL] THEN
      ASM SET_TAC[]]) in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[DIFFERENTIABLE_COMPONENTWISE_AT] THEN
  REWRITE_TAC[GSYM IN_NUMSEG; NOT_FORALL_THM; NOT_IMP] THEN
  REWRITE_TAC[SET_RULE `x IN a /\ (?i. i IN s /\ P i x) <=>
                        ?i. i IN s /\ x IN {x | x IN a /\ P i x}`] THEN
  REWRITE_TAC[SET_RULE
   `{x | ?i. i IN k /\ x IN f i} = UNIONS {f i | i IN k}`] THEN
  MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
  SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  MATCH_MP_TAC lemma7 THEN
  FIRST_ASSUM(MATCH_MP_TAC o
    ONCE_REWRITE_RULE[HAS_BOUNDED_VARIATION_ON_COMPONENTWISE]) THEN
  ASM_REWRITE_TAC[]);;

let LEBESGUE_DIFFERENTIATION_THEOREM = prove
 (`!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> negligible {x | x IN s /\ ~(f differentiable at x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `negligible {x | x IN frontier s /\ ~(f differentiable at x)} /\
    negligible {x | x IN interior s /\
                    ~((f:real^1->real^N) differentiable at x)}`
  MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM NEGLIGIBLE_UNION_EQ] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
    REWRITE_TAC[frontier] THEN
    MP_TAC(ISPEC `s:real^1->bool` CLOSURE_SUBSET) THEN SET_TAC[]] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_FINITE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_MESON_TAC[CARD_FRONTIER_INTERVAL_1];
    SUBGOAL_THEN `(f:real^1->real^N) has_bounded_variation_on interior s`
    MP_TAC THENL
     [ASM_MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET; INTERIOR_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^1->bool` OPEN_INTERIOR) THEN
    POP_ASSUM_LIST(K ALL_TAC)] THEN
  SPEC_TAC(`interior s:real^1->bool`,`s:real^1->bool`) THEN
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_COUNTABLE_UNION_CLOSED_INTERVALS) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^1->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
  REWRITE_TAC[INTER_UNIONS] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `i:real^1->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:real^1->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SET_RULE `s INTER {x | P x} = {x | x IN s /\ P x}`] THEN
  MATCH_MP_TAC LEBESGUE_DIFFERENTIATION_THEOREM_COMPACT THEN
  ASM_MESON_TAC[HAS_BOUNDED_VARIATION_ON_SUBSET]);;

let LEBESGUE_DIFFERENTIATION_THEOREM_ALT = prove
 (`!f:real^1->real^N s.
        is_interval s /\ f has_bounded_variation_on s
        ==> ?t. t SUBSET s /\ negligible t /\
                !x. x IN s DIFF t ==> f differentiable at x`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{x | x IN s /\ ~((f:real^1->real^N) differentiable at x)}` THEN
  ASM_SIMP_TAC[LEBESGUE_DIFFERENTIATION_THEOREM; SUBSET_RESTRICT] THEN
  REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN CONV_TAC TAUT);;

let LEBESGUE_DIFFERENTIATION_THEOREM_GEN = prove
 (`!f:real^1->real^N s.
        COUNTABLE(components s) /\ f has_bounded_variation_on s
        ==> negligible {x | x IN s /\ ~(f differentiable at x)}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `{x | x IN s /\ P x} = s INTER {x | P x}`] THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [UNIONS_COMPONENTS] THEN
  REWRITE_TAC[INTER_UNIONS] THEN
  MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS_GEN THEN
  ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `s INTER {x | P x} = {x | x IN s /\ P x}`] THEN
  MATCH_MP_TAC LEBESGUE_DIFFERENTIATION_THEOREM THEN
  REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN
  ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_SUBSET;
                HAS_BOUNDED_VARIATION_ON_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Forms of absolute continuity of the indefinite (absolute) integral.       *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_CONTINUOUS_INTEGRAL = prove
 (`!f:real^M->real^N s e.
        f absolutely_integrable_on s /\ &0 < e
        ==> ?d. &0 < d /\
                !t. t SUBSET s /\ measurable t /\ measure t < d
                    ==> norm(integral t f) < e`,
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x. if x IN s then (f:real^M->real^N) x else vec 0`;
    `(:real^M)`; `e / &2`]
   ABSOLUTELY_INTEGRABLE_APPROXIMATE_CONTINUOUS) THEN
  ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV; REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e / &2 / B` THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_HALF] THEN
  X_GEN_TAC `t:real^M->bool` THEN STRIP_TAC THEN
  TRANS_TAC REAL_LET_TRANS
   `drop(integral t (\x. lift(norm((if x IN s then f x else vec 0) - g x)) +
                         lift(norm((g:real^M->real^N) x))))` THEN
  SUBGOAL_THEN
   `(g:real^M->real^N) absolutely_integrable_on t /\
    (\x. if x IN s then (f:real^M->real^N) x else vec 0)
    absolutely_integrable_on t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^M)` THEN
    ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N) absolutely_integrable_on t` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        ABSOLUTELY_INTEGRABLE_EQ)) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
    ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
     [ABSOLUTELY_INTEGRABLE_NORM; ABSOLUTELY_INTEGRABLE_ADD;
      ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
    GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[LIFT_DROP; DROP_ADD] THEN
    COND_CASES_TAC THENL [CONV_TAC NORM_ARITH; ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM (CONV_TAC o GEN_SIMPLIFY_CONV TOP_DEPTH_SQCONV (basic_ss []) 5)
   [ABSOLUTELY_INTEGRABLE_NORM; INTEGRAL_ADD; DROP_ADD;
    ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
  MATCH_MP_TAC(REAL_ARITH `x < e / &2 /\ y < e / &2 ==> x + y < e`) THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
     `norm(integral s (f:real^M->real^1)) < e / &2
      ==> drop(integral t f) <= norm(integral s f)
           ==> drop(integral t f) < e / &2`)) THEN
    REWRITE_TAC[NORM_REAL; GSYM drop] THEN
    MATCH_MP_TAC(REAL_ARITH `x <= y ==> x <= abs y`) THEN
    MATCH_MP_TAC INTEGRAL_SUBSET_DROP_LE THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_NORM; IN_UNIV; SUBSET_UNIV; LIFT_DROP;
     ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; ABSOLUTELY_INTEGRABLE_SUB] THEN
    REWRITE_TAC[NORM_POS_LE];
    TRANS_TAC REAL_LET_TRANS `drop(integral t (\x:real^M. lift B))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[LIFT_DROP; ABSOLUTELY_INTEGRABLE_NORM; INTEGRABLE_ON_CONST;
                   ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE];
      ASM_SIMP_TAC[LIFT_EQ_CMUL; INTEGRAL_CMUL; INTEGRABLE_ON_CONST;
                   INTEGRAL_MEASURE] THEN
      REWRITE_TAC[DROP_CMUL; DROP_VEC; REAL_MUL_RID] THEN
     ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
     ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ]]]);;

let ABSOLUTELY_SETCONTINUOUS_INDEFINITE_INTEGRAL = prove
 (`!f:real^M->real^N s.
        f absolutely_integrable_on s /\ lebesgue_measurable s
        ==> (\k. integral k f) absolutely_setcontinuous_on s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ABSOLUTELY_SETCONTINUOUS_ON_ALT] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `e:real` o MATCH_MP
   (ONCE_REWRITE_RULE[IMP_CONJ] ABSOLUTELY_CONTINUOUS_INTEGRAL)) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`d:(real^M->bool)->bool`; `t:real^M->bool`] THEN
  STRIP_TAC THEN FIRST_ASSUM(MP_TAC o ISPEC `f:real^M->real^N` o
    MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
               INTEGRAL_COMBINE_DIVISION_TOPDOWN)) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_INTEGRABLE_ON_LEBSESGUE_MEASURABLE_SUBSET)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MEASURABLE_IMP_LEBESGUE_MEASURABLE THEN
    ASM_MESON_TAC[MEASURABLE_ELEMENTARY];
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_ELEMENTARY];
      ASM_MESON_TAC[MEASURE_ELEMENTARY]]]);;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_RIGHT = prove
 (`!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\x. integral(interval[a,x]) f)
            absolutely_continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[absolutely_continuous_on] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_SETCONTINUOUS_INDEFINITE_INTEGRAL)) THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        ABSOLUTELY_SETCONTINUOUS_COMPARISON) THEN
  SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY] THEN
  MAP_EVERY X_GEN_TAC [`c:real^1`; `d:real^1`] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY_1; SUBSET_INTERVAL_1] THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `y + z:real^N = x ==> norm(x - y) <= norm z`) THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL) o
   MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_LEFT = prove
 (`!f:real^1->real^N a b.
        f absolutely_integrable_on interval[a,b]
        ==> (\x. integral(interval[x,b]) f)
            absolutely_continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[absolutely_continuous_on] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_SETCONTINUOUS_INDEFINITE_INTEGRAL)) THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_INTERVAL] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        ABSOLUTELY_SETCONTINUOUS_COMPARISON) THEN
  SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY] THEN
  MAP_EVERY X_GEN_TAC [`c:real^1`; `d:real^1`] THEN
  REWRITE_TAC[INTERVAL_NE_EMPTY_1; SUBSET_INTERVAL_1] THEN
  STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(NORM_ARITH `z + x:real^N = y ==> norm(x - y) <= norm z`) THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ] INTEGRABLE_ON_SUBINTERVAL) o
   MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS = prove
 (`!f:real^1->real^N f' s a b.
      negligible s /\ drop a <= drop b /\
      f absolutely_continuous_on interval[a,b] /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
      ==> (f' has_integral (f(b) - f(a))) (interval[a,b])`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_BARTLE THEN
  EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_continuous_on]) THEN
  REWRITE_TAC[absolutely_setcontinuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2 / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `d:real`] MEASURABLE_OUTER_OPEN) THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; NEGLIGIBLE_IMP_MEASURABLE; REAL_ADD_LID] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x. if x IN s then u else ball(x:real^1,&1)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[gauge] THEN X_GEN_TAC `x:real^1` THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `p:(real^1#(real^1->bool))->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC VSUM_NORM_TRIANGLE THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[tagged_partial_division_of]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE SND (p:(real^1#(real^1->bool))->bool)` o
   MATCH_MP(MESON[] `(!x y. P x y) ==> !x. P x (UNIONS x)`)) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PARTIAL_DIVISION_OF_TAGGED_DIVISION];
      REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE;
                  IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_PAIR_THM] THEN
      ASM_MESON_TAC[tagged_partial_division_of; SUBSET];
      TRANS_TAC REAL_LET_TRANS `measure(u:real^1->bool)` THEN
      ASM_REWRITE_TAC[] THEN TRANS_TAC REAL_LE_TRANS
       `measure(UNIONS (IMAGE SND (p:(real^1#(real^1->bool))->bool)))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `x = y ==> y <= x`) THEN
        MATCH_MP_TAC MEASURE_ELEMENTARY THEN
        ASM_MESON_TAC[PARTIAL_DIVISION_OF_TAGGED_DIVISION];
        MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURABLE_ELEMENTARY;
                        PARTIAL_DIVISION_OF_TAGGED_DIVISION];
          REWRITE_TAC[SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE;
                      IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_PAIR_THM] THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [fine]) THEN
          FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
          REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
          REWRITE_TAC[AND_FORALL_THM; IMP_IMP] THEN
          REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN SET_TAC[]]]];
    W(MP_TAC o PART_MATCH (lhand o rand) (ISPEC `SND` SUM_IMAGE_GEN) o
        lhand o rand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `y <= &2 * x ==> x < e / &2 ==> y <= e`) THEN
    REWRITE_TAC[GSYM SUM_LMUL] THEN
    MATCH_MP_TAC SUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^1`; `k:real^1->bool`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?y z:real^1. k = interval[y,z] /\ x IN interval[y,z]`
    MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o
        GEN_REWRITE_RULE I [tagged_partial_division_of]) THEN
      ASM_MESON_TAC[];
      DISCH_THEN(REPEAT_TCL CHOOSE_THEN
       (CONJUNCTS_THEN2 SUBST_ALL_TAC MP_TAC))] THEN
    ASM_CASES_TAC `interval[y:real^1,z] = {}` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC THEN
    TRANS_TAC REAL_LE_TRANS
     `sum {x | x IN (p:(real^1#(real^1->bool))->bool) /\
               SND x = interval[y,z]}
          (\a. norm(f(z) - f(y):real^N))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; FORALL_PAIR_THM; IN_ELIM_THM] THEN
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY;
                   REAL_LE_REFL];
      ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
      ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY;
                   INTERVAL_UPPERBOUND_NONEMPTY]] THEN
    ASM_CASES_TAC `content(interval[y:real^1,z]) = &0` THENL
     [SUBGOAL_THEN `z:real^1 = y`
        (fun th -> REWRITE_TAC[th; VECTOR_SUB_REFL; NORM_0; REAL_MUL_RZERO;
                               REAL_LE_REFL]) THEN
      ASM_MESON_TAC[DROP_EQ; CONTENT_EQ_0_1; REAL_LE_ANTISYM;
                    INTERVAL_NE_EMPTY_1];
      MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE]] THEN
    REWRITE_TAC[REAL_OF_NUM_LE] THEN MP_TAC(ISPECL
     [`p:(real^1#(real^1->bool))->bool`;
      `interval[a:real^1,b]`; `x:real^1`]
     TAGGED_PARTIAL_DIVISION_COMMON_POINT_BOUND) THEN
    ASM_REWRITE_TAC[DIMINDEX_1; EXP_1] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LE_TRANS) THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[SUBSET; FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        FINITE_SUBSET)) THEN
    SET_TAC[]]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_EQ = prove
 (`!f:real^1->real^N a b.
      f absolutely_integrable_on interval[a,b] <=>
      f integrable_on interval[a,b] /\
      (\t. integral(interval[a,t]) f) has_bounded_variation_on interval[a,b]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[has_bounded_variation_on;
              ABSOLUTELY_INTEGRABLE_BOUNDED_SETVARIATION_EQ] THEN
  ASM_CASES_TAC `(f:real^1->real^N) integrable_on interval[a,b]` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THEN MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
    HAS_BOUNDED_SETVARIATION_ON_EQ) THEN
  MAP_EVERY X_GEN_TAC [`c:real^1`; `d:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[] THENL [CONV_TAC SYM_CONV; ALL_TAC] THEN
  ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY] THEN
  MATCH_MP_TAC(VECTOR_ARITH `b + c:real^N = a ==> a - b = c`) THEN
  MATCH_MP_TAC INTEGRAL_COMBINE THEN REPEAT CONJ_TAC THEN
  TRY(FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        INTEGRABLE_ON_SUBINTERVAL))) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1; SUBSET_INTERVAL_1]) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE = prove
 (`!f:real^1->real^N f' s a b.
      f absolutely_continuous_on interval[a,b] /\
      negligible s /\
      (!x. x IN interval[a,b] DIFF s
           ==> (f has_vector_derivative f'(x)) (at x within interval[a,b]))
      ==> f' absolutely_integrable_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH `drop b <= drop a \/ drop a <= drop b`) THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_ON_NULL; CONTENT_EQ_0_1] THEN
  REWRITE_TAC[ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_EQ] THEN CONJ_TAC THENL
   [REWRITE_TAC[integrable_on] THEN
    EXISTS_TAC `(f:real^1->real^N) b - f a` THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON THEN
    REWRITE_TAC[BOUNDED_INTERVAL] THEN
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (f:real^1->real^N) x - f a` THEN
    ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_SUB;
                 ABSOLUTELY_CONTINUOUS_ON_CONST] THEN
    X_GEN_TAC `c:real^1` THEN DISCH_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INTERVAL_1];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[a:real^1,b]` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC; ASM_REAL_ARITH_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]]);;

let ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ = prove
 (`!f:real^1->real^N f' a b.
      f' absolutely_integrable_on interval[a,b] /\
      (!x. x IN interval[a,b]
           ==> (f' has_integral (f x - f a)) (interval[a,x])) <=>
      f absolutely_continuous_on interval[a,b] /\
      ?s. negligible s /\
          !x. x IN interval [a,b] DIFF s
              ==> (f has_vector_derivative f' x) (at x within interval[a,b])`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\x. (f:real^1->real^N) a + integral(interval[a,x]) f'` THEN
    ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_RIGHT;
                 ABSOLUTELY_CONTINUOUS_ON_ADD;
                 ABSOLUTELY_CONTINUOUS_ON_CONST] THEN
    X_GEN_TAC `c:real^1` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `a + b:real^N = c <=> b = c - a`] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_INDEFINITE_INTEGRAL o
        MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^1->bool` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[IN_DIFF] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:real^1` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `((\x:real^1. (f:real^1->real^N) a) has_vector_derivative (vec 0))
      (at x within interval[a,b])`
    MP_TAC THENL [REWRITE_TAC[HAS_VECTOR_DERIVATIVE_CONST]; ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_VECTOR_DERIVATIVE_ADD) THEN
    REWRITE_TAC[VECTOR_ADD_LID] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN)) THEN
    EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
    X_GEN_TAC `y:real^1` THEN STRIP_TAC THEN
    ONCE_REWRITE_TAC[VECTOR_ARITH `a + b:real^N = c <=> b = c - a`] THEN
    MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INTERVAL_1];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_WITHIN_SUBSET THEN
      EXISTS_TAC `interval[a:real^1,b]` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC; ASM_REAL_ARITH_TAC] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC]]);;

let ABSOLUTELY_INTEGRABLE_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ = prove
 (`!f':real^1->real^N a b.
     f' absolutely_integrable_on interval[a,b] <=>
     ?f s. f absolutely_continuous_on interval[a,b] /\
           negligible s /\
           !x. x IN interval [a,b] DIFF s
               ==> (f has_vector_derivative f' x) (at x within interval[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[GSYM ABSOLUTE_INTEGRAL_ABSOLUTELY_CONTINUOUS_DERIVATIVE_EQ] THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[TAUT `(p <=> p /\ q) <=> p ==> q`] THEN
  DISCH_THEN(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE) THEN
  EXISTS_TAC `\t. integral(interval[a,t]) (f':real^1->real^N)` THEN
  REWRITE_TAC[INTEGRAL_REFL; VECTOR_SUB_RZERO] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ]
    INTEGRABLE_ON_SUBINTERVAL)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
  REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Characterizing absolutely continuous functions as Lebesgue integrals.     *)
(* ------------------------------------------------------------------------- *)

let ABSOLUTELY_INTEGRABLE_INCREASING_DERIVATIVE = prove
 (`!f:real^1->real^1 a b.
        (!x y. x IN interval[a,b] /\ y IN interval[a,b] /\ drop x <= drop y
               ==> drop(f x) <= drop(f y))
        ==> ?s f'. negligible s /\
                   (!x. x IN interval[a,b] DIFF s
                        ==> (f has_vector_derivative f' x) (at x)) /\
                   f' absolutely_integrable_on interval[a,b] /\
                   (!x. x IN interval[a,b]
                        ==> drop(integral(interval[a,x]) f')
                            <= drop(f x) - drop(f a))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^1->real^1`; `interval[a:real^1,b]`]
        LEBESGUE_DIFFERENTIATION_THEOREM_ALT) THEN
  ASM_SIMP_TAC[IS_INTERVAL_INTERVAL; INCREASING_BOUNDED_VARIATION] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{a:real^1,b} UNION s` THEN
  ASM_SIMP_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY] THEN
  RULE_ASSUM_TAC
   (REWRITE_RULE[VECTOR_DIFFERENTIABLE; RIGHT_IMP_EXISTS_THM]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC`f':real^1->real^1` o
        GEN_REWRITE_RULE I [SKOLEM_THM]) THEN
  EXISTS_TAC `f':real^1->real^1` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `interval[a:real^1,b] = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY; ABSOLUTELY_INTEGRABLE_ON_EMPTY] THEN
  SUBGOAL_THEN
   `!c. c IN interval[a,b]
        ==> (f':real^1->real^1) absolutely_integrable_on interval[a,c] /\
            drop(integral(interval[a,c]) f') <= drop(f c) - drop(f a)`
   (fun th -> ASM_MESON_TAC[ENDS_IN_INTERVAL; th]) THEN
  X_GEN_TAC `c:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interval[a:real^1,c] = {})` MP_TAC THENL
   [ASM_MESON_TAC[INTERVAL_NE_EMPTY_1; IN_INTERVAL_1]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[a:real^1,c] SUBSET interval[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_INTERVAL_1; IN_INTERVAL_1; REAL_LE_REFL];
    ALL_TAC] THEN
  UNDISCH_TAC `negligible(s:real^1->bool)` THEN
  SUBGOAL_THEN
   `!x. x IN interval[a,c] DIFF s
        ==> ((f:real^1->real^1) has_vector_derivative f' x) (at x)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN interval[a,c] /\ y IN interval[a,c] /\ drop x <= drop y
          ==> drop(f x) <= drop(f y)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`c:real^1`,`b:real^1`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  ABBREV_TAC `g = \x. if drop x < drop a then f(a)
                      else if drop b < drop x then f(b)
                      else (f:real^1->real^1) x` THEN
  SUBGOAL_THEN
   `(f':real^1->real^1) absolutely_integrable_on interval[a,b] /\
    drop(integral(interval[a,b]) f') <= drop(g b) - drop(g a)`
  MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "g" THEN REWRITE_TAC[REAL_LT_REFL] THEN
    ASM_REWRITE_TAC[GSYM INTERVAL_EQ_EMPTY_1]] THEN
  ABBREV_TAC `t = s UNION {a:real^1,b}` THEN
  SUBGOAL_THEN `negligible(t:real^1->bool)` MP_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_INSERT; NEGLIGIBLE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN interval[a,b] DIFF t
          ==> ((g:real^1->real^1) has_vector_derivative f' x) (at x)`
  MP_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF] THEN
    EXPAND_TAC "t" THEN REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_TRANSFORM_WITHIN_OPEN THEN
    MAP_EVERY EXISTS_TAC [`f:real^1->real^1`; `interval(a:real^1,b)`] THEN
    REWRITE_TAC[OPEN_INTERVAL; CONJ_ASSOC] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; DE_MORGAN_THM; IN_INTERVAL_1] THEN
    REPEAT STRIP_TAC THEN EXPAND_TAC "g" THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. drop b <= drop x ==> (g:real^1->real^1) x = g b`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
    EXPAND_TAC "g" THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    AP_TERM_TAC THEN REWRITE_TAC[GSYM DROP_EQ] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. drop x <= drop y ==> drop(g x) <= drop(g y)`
  MP_TAC THENL
   [REPEAT STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN
    EXPAND_TAC "g" THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[REAL_LE_REFL]) THEN
    FIRST_ASSUM(MP_TAC o SPECL [`a:real^1`; `b:real^1`]) THEN
    REWRITE_TAC[IN_INTERVAL_1; REAL_LE_REFL] THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~(interval[a:real^1,b] = {})` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`t:real^1->bool`,`s:real^1->bool`) THEN
  SPEC_TAC(`g:real^1->real^1`,`f:real^1->real^1`) THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\n x. &n % ((f:real^1->real^1)(x + lift(inv(&n))) - f(x))`;
    `f':real^1->real^1`; `interval[a:real^1,b]`; `s:real^1->bool`;
    `drop(f(b:real^1)) - drop(f a)`] FATOU_STRONG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN
    REWRITE_TAC[has_derivative_at; has_vector_derivative] THEN
    DISCH_THEN(MP_TAC o
      SPEC `\n. x + lift(inv(&n))` o
      MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       (REWRITE_RULE[CONJ_ASSOC] (ISPEC `sequentially` LIM_COMPOSE_AT))) o
      CONJUNCT2) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; o_DEF; VECTOR_ADD_SUB] THEN
    REWRITE_TAC[NORM_LIFT; REAL_ABS_INV; REAL_ABS_NUM; REAL_INV_INV] THEN
    REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_INV_0; VECTOR_MUL_LZERO] THEN
    ANTS_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM VECTOR_ADD_RID] THEN
      MATCH_MP_TAC LIM_ADD THEN REWRITE_TAC[LIM_CONST; SEQ_HARMONIC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC RAND_CONV [LIM_NULL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] LIM_TRANSFORM) THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
    EXISTS_TAC `1` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REWRITE_TAC[VECTOR_ARITH
     `n % (f' - (f + d)) - (n % (f' - f) - k):real^N = k - n % d`] THEN
    REWRITE_TAC[LIFT_DROP; VECTOR_MUL_ASSOC; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_OF_NUM_EQ; LE_1; VECTOR_MUL_LID];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC INTEGRABLE_CMUL THEN
    MATCH_MP_TAC INTEGRABLE_SUB THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[INTEGRABLE_INCREASING_1]] THEN
    SUBGOAL_THEN
     `(f:real^1->real^1) integrable_on
      interval[a + lift(inv(&n)),b + lift(inv(&n))]`
    MP_TAC THENL
     [MATCH_MP_TAC INTEGRABLE_INCREASING_1 THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`&1`; `lift(inv(&n))`] o
      MATCH_MP(REWRITE_RULE[IMP_CONJ] INTEGRABLE_AFFINITY)) THEN
    REWRITE_TAC[IMAGE_AFFINITY_INTERVAL] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; VECTOR_MUL_LID] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + x) + --x:real^1 = a`] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [INTERVAL_EQ_EMPTY_1]) THEN
    ASM_REWRITE_TAC[DROP_ADD; REAL_ARITH `x + i < y + i <=> ~(y <= x)`] THEN
    ASM_MESON_TAC[INTERVAL_NE_EMPTY_1];
    MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
    X_GEN_TAC `n:num` THEN REWRITE_TAC[DROP_CMUL; DROP_SUB] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    REWRITE_TAC[REAL_POS; REAL_SUB_LE] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[DROP_ADD; REAL_LE_ADDR; LIFT_DROP; REAL_LE_INV_EQ] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`;
    `integral (interval[a + lift(inv(&n)),b + lift(inv(&n))]) f:real^1`;
    `a + lift(inv(&n))`; `b + lift(inv(&n))`;
    `&1`; `lift(inv(&n))`] HAS_INTEGRAL_AFFINITY) THEN
  REWRITE_TAC[DIMINDEX_1] THEN
  REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRAL; IMAGE_AFFINITY_INTERVAL] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_LID; INTERVAL_EQ_EMPTY_1] THEN
  REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN
  COND_CASES_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[INTERVAL_NE_EMPTY_1]) THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH `(a + x) + --x:real^N = a`]] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[INTEGRABLE_INCREASING_1]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `&n` o MATCH_MP HAS_INTEGRAL_CMUL) THEN
  REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN STRIP_TAC THEN
  REWRITE_TAC[VECTOR_SUB_LDISTRIB] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) INTEGRAL_SUB o  rand o lhand o snd) THEN
  SUBGOAL_THEN `!u v. (f:real^1->real^1) integrable_on interval[u,v]`
  ASSUME_TAC THENL [ASM_MESON_TAC[INTEGRABLE_INCREASING_1]; ALL_TAC] THEN
  ASM_SIMP_TAC[INTEGRABLE_CMUL; INTEGRAL_CMUL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM VECTOR_SUB_LDISTRIB; DROP_CMUL] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`; `a:real^1`; `b + lift(&1 / &n)`; `a + lift(&1 / &n)`]
   INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `a + b:real^N = b <=> b = b - a`] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DROP_ADD; REAL_LE_ADDR; REAL_LE_RADD] THEN
    SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; LIFT_DROP; REAL_POS] THEN
    ASM_MESON_TAC[INTERVAL_NE_EMPTY_1];
    DISCH_THEN(SUBST1_TAC o MATCH_MP (VECTOR_ARITH
     `a + b:real^N = c ==> b = c - a`))] THEN
  MP_TAC(ISPECL
   [`f:real^1->real^1`; `a:real^1`; `b + lift(&1 / &n)`; `b:real^1`]
   INTEGRAL_COMBINE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[DROP_ADD; REAL_LE_ADDR; REAL_LE_RADD] THEN
    SIMP_TAC[real_div; REAL_MUL_LID; REAL_LE_INV_EQ; LIFT_DROP; REAL_POS] THEN
    ASM_MESON_TAC[INTERVAL_NE_EMPTY_1];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  REWRITE_TAC[VECTOR_ARITH `(i + b) - a - i:real^N = b - a`] THEN
  REWRITE_TAC[DROP_SUB; REAL_SUB_LDISTRIB] THEN
  MATCH_MP_TAC(REAL_ARITH `a <= b /\ d <= c ==> a - c <= b - d`) THEN
  CONJ_TAC THENL
   [TRANS_TAC REAL_LE_TRANS
     `&n * drop(integral (interval[b,b + lift (&1 / &n)])
                         (\x. (f:real^1->real^1) b))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_REWRITE_TAC[INTEGRABLE_CONST; IN_INTERVAL_1] THEN
      ASM_MESON_TAC[REAL_LE_REFL];
      REWRITE_TAC[INTEGRAL_CONST] THEN
      SIMP_TAC[CONTENT_1; DROP_ADD; LIFT_DROP; REAL_LE_ADDR;
               REAL_LE_DIV; REAL_POS] THEN
      REWRITE_TAC[DROP_CMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
      CONV_TAC REAL_FIELD];
    TRANS_TAC REAL_LE_TRANS
     `&n * drop(integral (interval[a,a + lift (&1 / &n)])
                         (\x. (f:real^1->real^1) a))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTEGRAL_CONST] THEN
      SIMP_TAC[CONTENT_1; DROP_ADD; LIFT_DROP; REAL_LE_ADDR;
               REAL_LE_DIV; REAL_POS] THEN
      REWRITE_TAC[DROP_CMUL] THEN MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM REAL_OF_NUM_LE]) THEN
      CONV_TAC REAL_FIELD;
      MATCH_MP_TAC REAL_LE_LMUL THEN REWRITE_TAC[REAL_POS] THEN
      MATCH_MP_TAC INTEGRAL_DROP_LE THEN
      ASM_SIMP_TAC[INTEGRABLE_CONST; IN_INTERVAL_1]]]);;

let ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_DERIVATIVE = prove
 (`!f:real^1->real^N a b.
        f has_bounded_variation_on interval[a,b]
        ==> ?f' s. negligible s /\
                   (!x. x IN interval[a,b] DIFF s
                        ==> (f has_vector_derivative f' x) (at x)) /\
                   f' absolutely_integrable_on interval[a,b]`,
  let lemma = prove
   (`!f:real^1->real^1 a b.
        f has_bounded_variation_on interval[a,b]
        ==> ?f' s. negligible s /\
                   (!x. x IN interval[a,b] DIFF s
                        ==> (f has_vector_derivative f' x) (at x)) /\
                   f' absolutely_integrable_on interval[a,b]`,
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o
      GEN_REWRITE_RULE I [HAS_BOUNDED_VARIATION_DARBOUX]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`g:real^1->real^1`; `h:real^1->real^1`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^1->real^1`; `a:real^1`; `b:real^1`]
     ABSOLUTELY_INTEGRABLE_INCREASING_DERIVATIVE) THEN
    MP_TAC(ISPECL [`g:real^1->real^1`; `a:real^1`; `b:real^1`]
     ABSOLUTELY_INTEGRABLE_INCREASING_DERIVATIVE) THEN
    ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`s:real^1->bool`; `g':real^1->real^1`] THEN
    STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`t:real^1->bool`; `h':real^1->real^1`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `\x. (g':real^1->real^1) x - h' x` THEN
    EXISTS_TAC `s UNION t:real^1->bool` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_SUB] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM FUN_EQ_THM]) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_SUB THEN
    ASM SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  MP_TAC(MATCH_MP MONO_FORALL (GEN `i:num` (MATCH_MP MONO_IMP (CONJ
    (TAUT `1 <= i /\ i <= dimindex(:N) ==> 1 <= i /\ i <= dimindex(:N)`)
    (SPECL [`\x. lift((f:real^1->real^N)x$i)`; `a:real^1`; `b:real^1`]
       lemma))))) THEN
  ASM_REWRITE_TAC[GSYM HAS_BOUNDED_VARIATION_ON_COMPONENTWISE] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`g:num->real^1->real^1`; `s:num->real^1->bool`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `(\x. lambda i. drop((g:num->real^1->real^1) i x))
              :real^1->real^N` THEN
  EXISTS_TAC `UNIONS (IMAGE (s:num->real^1->bool) (1..dimindex(:N)))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    ASM_SIMP_TAC[IN_NUMSEG; FINITE_IMAGE; FORALL_IN_IMAGE; FINITE_NUMSEG];

    X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_DIFF; UNIONS_IMAGE; IN_NUMSEG; IN_ELIM_THM] THEN
    REWRITE_TAC[MESON[] `~(?x. P x /\ Q x) <=> (!x. P x ==> ~Q x)`] THEN
    STRIP_TAC THEN
    REWRITE_TAC[has_vector_derivative] THEN
    ONCE_REWRITE_TAC[HAS_DERIVATIVE_COMPONENTWISE_AT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o SPEC `i:num`)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
    ASM_SIMP_TAC[IN_DIFF; has_vector_derivative] THEN
    ASM_SIMP_TAC[VECTOR_MUL_COMPONENT; LAMBDA_BETA] THEN
    REWRITE_TAC[LIFT_CMUL; LIFT_DROP];
    ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE] THEN
    ASM_SIMP_TAC[LAMBDA_BETA; LIFT_DROP; ETA_AX]]);;

let ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_EQ = prove
 (`!f:real^1->real^N a b.
        f absolutely_continuous_on interval[a,b] <=>
        ?f'. f' absolutely_integrable_on interval[a,b] /\
             !x. x IN interval[a,b]
                 ==> (f' has_integral (f x - f a)) (interval[a,x])`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON)) THEN
    REWRITE_TAC[BOUNDED_INTERVAL] THEN DISCH_THEN(MP_TAC o MATCH_MP
      ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_DERIVATIVE) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f':real^1->real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^1->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
    MATCH_MP_TAC FUNDAMENTAL_THEOREM_OF_CALCULUS_ABSOLUTELY_CONTINUOUS THEN
    EXISTS_TAC `s:real^1->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INTERVAL_1];
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        ABSOLUTELY_CONTINUOUS_ON_SUBSET)) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1; REAL_LE_REFL] THEN
      ASM_MESON_TAC[IN_INTERVAL_1];
      X_GEN_TAC `y:real^1` THEN REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN
      STRIP_TAC THEN MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
    FIRST_ASSUM(MP_TAC o MATCH_MP
      ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_RIGHT) THEN
    MP_TAC(ISPECL [`interval[a:real^1,b]`; `(f:real^1->real^N) a`]
      ABSOLUTELY_CONTINUOUS_ON_CONST) THEN
    REWRITE_TAC[IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP ABSOLUTELY_CONTINUOUS_ON_ADD) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ABSOLUTELY_CONTINUOUS_ON_EQ) THEN
    REWRITE_TAC[VECTOR_ARITH `a + i:real^N = x <=> i = x - a`] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Banach-Zarecki and related results.                                       *)
(* ------------------------------------------------------------------------- *)

let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE,
    LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE,
    ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY =
  let lemma1 = prove
   (`!f:real^1->real^1 s e.
          f absolutely_continuous_on s /\ is_interval s /\ closed s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [absolutely_continuous_on]) THEN
    REWRITE_TAC[absolutely_setcontinuous_on] THEN
    DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
    X_GEN_TAC `t:real^1->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:real^1->bool`; `r / &2`]
      MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
    ASM_REWRITE_TAC[REAL_HALF; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `ds:(real^1->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `!k. k IN ds
          ==> ~(k INTER s = {})
          ==> ?u v. u IN k /\ v IN k /\ u IN s /\ v IN s /\
                    IMAGE (f:real^1->real^1) (k INTER s) SUBSET
                    interval[f u,f v]`
    MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (MESON[]
       `(!k. k IN d ==> ~(k = {}) /\ ?a b. k = interval[a,b])
        ==> (!a b. interval[a,b] IN d /\ ~(interval[a,b] = {})
                   ==> P(interval[a,b]))
            ==> !k. k IN d ==> P k`)) THEN
      MAP_EVERY X_GEN_TAC [`a:real^1`; `b:real^1`] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN
       `?u v. IMAGE (f:real^1->real^1) (interval[a,b] INTER s) = interval[u,v]`
      MP_TAC THENL
       [REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE;
          MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE] THEN
        ASM_SIMP_TAC[COMPACT_INTERVAL; COMPACT_INTER_CLOSED;
                     GSYM IS_INTERVAL_CONNECTED_1;
                     IS_INTERVAL_INTER; IS_INTERVAL_INTERVAL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `s:real^1->bool` THEN REWRITE_TAC[INTER_SUBSET] THEN
        MATCH_MP_TAC UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS THEN
        ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_IMP_UNIFORMLY_CONTINUOUS];
        REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`u:real^1`; `v:real^1`] THEN
        DISCH_TAC THEN SUBGOAL_THEN
         `u IN IMAGE (f:real^1->real^1) (interval[a,b] INTER s) /\
          v IN IMAGE (f:real^1->real^1) (interval[a,b] INTER s)`
        MP_TAC THENL
         [ASM_REWRITE_TAC[ENDS_IN_INTERVAL] THEN ASM SET_TAC[];
          REWRITE_TAC[IN_IMAGE; LEFT_AND_EXISTS_THM] THEN
          REWRITE_TAC[RIGHT_AND_EXISTS_THM]] THEN
        REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM SET_TAC[]];
        ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
     [IMP_IMP; RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`u:(real^1->bool)->real^1`; `v:(real^1->bool)->real^1`] THEN
    DISCH_TAC THEN EXISTS_TAC
     `UNIONS (IMAGE (\k. interval[(f:real^1->real^1)(u k),f(v k)])
                    {k:real^1->bool | k IN ds /\ ~(k INTER s = {})})` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(MESON[REAL_ARITH `&0 < e /\ x <= e / &2 ==> x < e`]
      `&0 < e /\ measurable s /\ measure s <= e / &2
       ==> measurable s /\ measure s < e`) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_SIMP_TAC[COUNTABLE_IMAGE; COUNTABLE_RESTRICT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; MEASURABLE_INTERVAL] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `dd:(real^1->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE (\k:real^1->bool. interval[(f:real^1->real^1) (u k),f(v k)]) dd =
      IMAGE (\k. interval[lift(min (drop(f(interval_lowerbound k)))
                                   (drop(f(interval_upperbound k)))),
                          lift(max (drop(f(interval_lowerbound k)))
                                   (drop(f(interval_upperbound k))))])
            (IMAGE (\k. interval[lift(min (drop(u k)) (drop(v k))),
                                 lift(max (drop(u k)) (drop(v k)))])
                   dd)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> g x = f x) ==> IMAGE f s = IMAGE g s`) THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1; LIFT_DROP;
               REAL_ARITH `min a b <= max a b`] THEN
      X_GEN_TAC `k:real^1->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `~(s = {}) /\ (~(s = {}) ==> t = s) ==> t = s`) THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[EQ_INTERVAL_1; INTERVAL_NE_EMPTY_1] THEN
      ASM_CASES_TAC `drop(u(k:real^1->bool)) <= drop(v k)` THEN
      ASM_SIMP_TAC[REAL_ARITH `a <= b ==> min a b = a /\ max a b = b`;
                   REAL_ARITH `~(a <= b) ==> min a b = b /\ max a b = a`;
                   LIFT_DROP] THEN
      SIMP_TAC[real_max; real_min; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhand o rand)
      MEASURE_UNIONS_LE_IMAGE o lhand o snd) THEN
    ASM_SIMP_TAC[MEASURABLE_INTERVAL; FINITE_IMAGE] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS) THEN
    FIRST_X_ASSUM(MP_TAC o ISPECL
     [`IMAGE (\k:real^1->bool. interval[lift(min (drop(u k)) (drop(v k))),
                                 lift(max (drop(u k)) (drop(v k)))])
             dd`;
      `UNIONS(IMAGE (\k:real^1->bool.
         interval[lift(min (drop(u k)) (drop(v k))),
                  lift(max (drop(u k)) (drop(v k)))])
             dd)`]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[division_of];
      MATCH_MP_TAC(REAL_ARITH `x <= y ==> y < e ==> x <= e`) THEN
      MATCH_MP_TAC SUM_LE THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      SIMP_TAC[INTERVAL_LOWERBOUND_1; INTERVAL_UPPERBOUND_1; LIFT_DROP;
               REAL_ARITH `min a b <= max a b`; MEASURE_INTERVAL_1] THEN
      REWRITE_TAC[NORM_1; DROP_SUB] THEN REAL_ARITH_TAC] THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        REWRITE_TAC[INTERVAL_NE_EMPTY_1; LIFT_DROP] THEN REAL_ARITH_TAC;
        MESON_TAC[]];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `k:real^1->bool` THEN DISCH_TAC THEN
      X_GEN_TAC `l:real^1->bool` THEN DISCH_TAC THEN
      ASM_CASES_TAC `l:real^1->bool = k` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(K ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^1->bool`; `l:real^1->bool`]) THEN
      ASM_REWRITE_TAC[GSYM INTERIOR_INTER] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = {} ==> s = {}`) THEN
      MATCH_MP_TAC SUBSET_INTERIOR THEN
      MATCH_MP_TAC(SET_RULE
       `s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'`) THEN
      CONJ_TAC THEN W(MP_TAC o PART_MATCH (lhand o rand)
        INTERVAL_SUBSET_IS_INTERVAL o snd) THEN
      (ANTS_TAC THENL
        [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
         ASM_MESON_TAC[IS_INTERVAL_INTERVAL];
         DISCH_THEN SUBST1_TAC THEN DISJ2_TAC]) THEN
      REWRITE_TAC[real_min; real_max] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP]) THEN
      ASM SET_TAC[];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL] THEN DISJ2_TAC THEN
      REWRITE_TAC[real_min; real_max] THEN
      REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP]) THEN
      ASM SET_TAC[];
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (REAL_ARITH
       `m <= t + r / &2 ==> t < r / &2 /\ x <= m ==> x < r`)) THEN
      ASM_REWRITE_TAC[] THEN
      W(MP_TAC o PART_MATCH (lhs o rand) SUM_IMAGE_NONZERO o lhand o snd) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MAP_EVERY X_GEN_TAC [`k:real^1->bool`; `l:real^1->bool`] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`k:real^1->bool`; `l:real^1->bool`]) THEN
        ASM_REWRITE_TAC[CONTENT_EQ_0_INTERIOR; GSYM INTERIOR_INTER] THEN
        ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = {} ==> s = {}`) THEN
        MATCH_MP_TAC SUBSET_INTERIOR THEN REWRITE_TAC[SUBSET_INTER] THEN
        CONJ_TAC THENL [FIRST_ASSUM(SUBST1_TAC o SYM); ALL_TAC] THEN
        W(MP_TAC o PART_MATCH (lhand o rand)
          INTERVAL_SUBSET_IS_INTERVAL o snd) THEN
        (ANTS_TAC THENL
         [RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
          ASM_MESON_TAC[IS_INTERVAL_INTERVAL];
          DISCH_THEN SUBST1_TAC THEN DISJ2_TAC]) THEN
        REWRITE_TAC[real_min; real_max] THEN
        REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP]) THEN
        ASM SET_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      TRANS_TAC REAL_LE_TRANS `sum (dd:(real^1->bool)->bool) content` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[o_DEF] THEN
        X_GEN_TAC `k:real^1->bool` THEN
        ASM_CASES_TAC `?a b:real^1. k = interval[a,b]` THENL
         [FIRST_X_ASSUM(CHOOSE_THEN STRIP_ASSUME_TAC); ASM SET_TAC[]] THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MATCH_MP_TAC CONTENT_SUBSET THEN
        SIMP_TAC[INTERVAL_SUBSET_IS_INTERVAL; IS_INTERVAL_INTERVAL] THEN
        DISJ2_TAC THEN REWRITE_TAC[real_min; real_max] THEN
        REPEAT(COND_CASES_TAC THEN REWRITE_TAC[LIFT_DROP]) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`dd:(real^1->bool)->bool`; `UNIONS dd:real^1->bool`]
          HAS_MEASURE_ELEMENTARY) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[division_of] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM o MATCH_MP MEASURE_UNIQUE) THEN
      MATCH_MP_TAC MEASURE_SUBSET THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
      MATCH_MP_TAC MEASURABLE_UNIONS THEN
      RULE_ASSUM_TAC(REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
      ASM_MESON_TAC[MEASURABLE_INTERVAL]]) in
  let lemma2 = prove
   (`!f:real^1->real^1 s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          ABSOLUTELY_CONTINUOUS_EXTENDS_TO_CLOSURE)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^1` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`g:real^1->real^1`; `closure s:real^1->bool`; `e:real`] lemma1) THEN
    ASM_REWRITE_TAC[CLOSED_CLOSURE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[IS_INTERVAL_CONVEX_1; CONVEX_CLOSURE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `r:real` THEN MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1->bool` THEN
    MP_TAC(ISPEC `s:real^1->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]) in
  let lemma3 = prove
   (`!f:real^1->real^N s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?r. &0 < r /\
                  !t. t SUBSET s /\ measurable t /\ measure t < r
                      ==> ?u. IMAGE f t SUBSET u /\
                              measurable u /\ measure u < e`,
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `1 <= dimindex(:N)` MP_TAC THENL
     [REWRITE_TAC[DIMINDEX_GE_1];
      REWRITE_TAC[ARITH_RULE `1 <= n <=> 2 <= n \/ n = 1`]] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN
      X_GEN_TAC `t:real^1->bool` THEN STRIP_TAC THEN
      EXISTS_TAC `IMAGE (f:real^1->real^N) s` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN
      MP_TAC(ISPECL [`f:real^1->real^N`; `s:real^1->bool`]
        NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE_LOWDIM) THEN
      ASM_SIMP_TAC[NEGLIGIBLE_EQ_MEASURE_0];
      ALL_TAC]  THEN
    MP_TAC(ISPECL [`(:real^N)`; `(:real^1)`] ISOMETRIES_SUBSPACES) THEN
    ASM_SIMP_TAC[SUBSPACE_UNIV; DIM_UNIV; DIMINDEX_1] THEN
    REWRITE_TAC[IN_UNIV; LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`h:real^N->real^1`; `k:real^1->real^N`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`(h:real^N->real^1) o (f:real^1->real^N)`;
                   `s:real^1->bool`; `e:real`] lemma2) THEN
    ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_COMPOSE_LINEAR] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1->bool` THEN
    MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^1->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (k:real^1->real^N) u` THEN REPEAT CONJ_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[IMAGE_o]) THEN ASM SET_TAC[];
      MATCH_MP_TAC MEASURABLE_LINEAR_IMAGE_GEN THEN
      ASM_REWRITE_TAC[DIMINDEX_1; LE_REFL];
      ASM_SIMP_TAC[MEASURE_ISOMETRY; DIMINDEX_1]]) in
  let NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE = prove
   (`!f:real^1->real^N s t.
          f absolutely_continuous_on s /\ is_interval s /\
          negligible t /\ t SUBSET s
          ==> negligible(IMAGE f t)`,
    REPEAT STRIP_TAC THEN REWRITE_TAC[NEGLIGIBLE_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`f:real^1->real^N`; `s:real^1->bool`; `e:real`]
          lemma3) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[NEGLIGIBLE_EQ_MEASURE_0]) in
  let LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE = prove
   (`!f:real^1->real^N s t.
          f absolutely_continuous_on s /\ is_interval s /\
          lebesgue_measurable t /\ t SUBSET s
          ==> lebesgue_measurable(IMAGE f t)`,
    MESON_TAC[PRESERVES_LEBESGUE_MEASURABLE_IFF_PRESERVES_NEGLIGIBLE;
              NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE;
              ABSOLUTELY_CONTINUOUS_ON_IMP_UNIFORMLY_CONTINUOUS;
              UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS]) in
  let ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY = prove
   (`!f:real^1->real^N s e.
          f absolutely_continuous_on s /\ is_interval s /\ &0 < e
          ==> ?d. &0 < d /\
                  !t. t SUBSET s /\ measurable t /\ measure t < d
                      ==> measurable(IMAGE f t) /\ measure(IMAGE f t) < e`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP lemma3) THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN
    MATCH_MP_TAC MONO_AND THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `t:real^1->bool` THEN
    DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `u:real^N->bool` THEN
      ASM_MESON_TAC[LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE;
                    MEASURABLE_IMP_LEBESGUE_MEASURABLE];
      DISCH_TAC THEN
      TRANS_TAC REAL_LET_TRANS `measure(u:real^N->bool)` THEN
      ASM_SIMP_TAC[MEASURE_SUBSET]]) in
  NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE,
  LEBESGUE_MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE,
  ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY;;

let MEASURABLE_ABSOLUTELY_CONTINUOUS_IMAGE = prove
 (`!f:real^1->real^N s t.
        f absolutely_continuous_on s /\ is_interval s /\
        measurable t /\ t SUBSET s
        ==> measurable(IMAGE f t)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  MP_TAC(ISPECL [`f:real^1->real^N`; `s:real^1->bool`; `&1`]
        ABSOLUTELY_CONTINUOUS_IMP_BANACH_SPROPERTY) THEN
  ASM_REWRITE_TAC[REAL_LT_01; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  X_GEN_TAC `t:real^1->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. measure(t:real^1->bool) < &2 pow n * d` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ] THEN MATCH_MP_TAC REAL_ARCH_POW THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    FIRST_X_ASSUM(MP_TAC o check (is_conj o concl)) THEN
    FIRST_X_ASSUM(MP_TAC o check (is_exists o concl)) THEN
    SPEC_TAC(`t:real^1->bool`,`t:real^1->bool`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM]] THEN
  MATCH_MP_TAC num_INDUCTION THEN ASM_SIMP_TAC[real_pow; REAL_MUL_LID] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_forall o concl)) THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[IMP_IMP] THEN DISCH_TAC THEN
  X_GEN_TAC `t:real^1->bool` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HALF_MEASURES) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1->bool`; `v:real^1->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(fun th ->
   MP_TAC(SPEC `v:real^1->bool` th) THEN
   MP_TAC(SPEC `u:real^1->bool` th)) THEN
  ASM_REWRITE_TAC[REAL_ARITH `x / &2 < p * d <=> x < (&2 * p) * d`] THEN
  REPEAT(ANTS_TAC THENL [ASM SET_TAC[]; DISCH_TAC]) THEN
  EXPAND_TAC "t" THEN REWRITE_TAC[IMAGE_UNION] THEN
  ASM_SIMP_TAC[MEASURABLE_UNION]);;

let BANACH_ZARECKI = prove
 (`!f:real^1->real^1 a b.
        f absolutely_continuous_on interval[a,b] <=>
        f continuous_on interval[a,b] /\
        f has_bounded_variation_on interval[a,b] /\
        !t. t SUBSET interval[a,b] /\ negligible t ==> negligible(IMAGE f t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON;
                 ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS;
                 IS_INTERVAL_INTERVAL; BOUNDED_INTERVAL] THEN
    ASM_MESON_TAC[NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE; IS_INTERVAL_INTERVAL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP
    ABSOLUTELY_INTEGRABLE_BOUNDED_VARIATION_DERIVATIVE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f':real^1->real^1`; `n:real^1->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
  DISCH_THEN(MP_TAC o
    MATCH_MP ABSOLUTELY_CONTINUOUS_INDEFINITE_INTEGRAL_RIGHT) THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ_ALT]
        ABSOLUTELY_CONTINUOUS_COMPARISON) THEN
  MAP_EVERY X_GEN_TAC [`s:real^1`; `t:real^1`] THEN STRIP_TAC THEN
  REWRITE_TAC[dist] THEN
  TRANS_TAC REAL_LE_TRANS
   `norm(integral(interval[s,t]) (\x. lift(norm((f':real^1->real^1) x))))` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(NORM_ARITH `a + c:real^N = b ==> norm c <= norm(a - b)`) THEN
    MATCH_MP_TAC INTEGRAL_COMBINE THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    MATCH_MP_TAC INTEGRABLE_SUBINTERVAL THEN
    MAP_EVERY EXISTS_TAC [`a:real^1`; `b:real^1`] THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE] THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `measure(IMAGE (f:real^1->real^1) (interval[s,t]))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM(CONJUNCT1 MEASURE_SEGMENT_1)] THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN REWRITE_TAC[MEASURABLE_SEGMENT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_COMPACT THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      ASM_SIMP_TAC[FUN_IN_IMAGE; ENDS_IN_INTERVAL; INTERVAL_NE_EMPTY_1;
                   REAL_LT_IMP_LE] THEN
      REWRITE_TAC[GSYM CONNECTED_CONVEX_1] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      REWRITE_TAC[CONNECTED_INTERVAL]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
      CONTINUOUS_ON_SUBSET)) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC REAL_LE_TRANS
   `measure(IMAGE (f:real^1->real^1) (interval[s,t] DIFF n))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_EQ_IMP_LE THEN
    MATCH_MP_TAC MEASURE_NEGLIGIBLE_SYMDIFF THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `n INTER interval[a:real^1,b]`) THEN ANTS_TAC
    THENL [ASM_MESON_TAC[INTER_SUBSET; NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
    SUBGOAL_THEN `interval[s:real^1,t] SUBSET interval[a,b]` MP_TAC THENL
     [ALL_TAC; SET_TAC[]] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
    REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MEASURE_DIFFERENTIABLE_IMAGE THEN
  EXISTS_TAC `\x h. drop h % (f':real^1->real^1) x` THEN
  ASM_SIMP_TAC[MEASURABLE_IMP_LEBESGUE_MEASURABLE; MEASURABLE_DIFF;
               MEASURABLE_INTERVAL; NEGLIGIBLE_IMP_MEASURABLE] THEN
  SIMP_TAC[DET_1; matrix; LAMBDA_BETA; DIMINDEX_1; ARITH;
           VECTOR_MUL_COMPONENT; BASIS_COMPONENT; drop] THEN
  REWRITE_TAC[REAL_MUL_LID; GSYM drop; GSYM NORM_1] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^1` THEN
    REWRITE_TAC[IN_DIFF; IN_INTERVAL_1] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF; IN_INTERVAL_1]) THEN
    REWRITE_TAC[GSYM has_vector_derivative] THEN
    MATCH_MP_TAC HAS_VECTOR_DERIVATIVE_AT_WITHIN THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE_SET) THEN
    EXISTS_TAC `interval[s:real^1,t]` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
      SUBGOAL_THEN `interval[s:real^1,t] SUBSET interval[a,b]` MP_TAC THENL
       [ALL_TAC; SET_TAC[]] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN
      REWRITE_TAC[SUBSET_INTERVAL_1] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_LIFT_NORM_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_ON_SUBINTERVAL THEN
      EXISTS_TAC `interval[a:real^1,b]` THEN
      ASM_REWRITE_TAC[SUBSET_INTERVAL_1] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1]) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[NORM_1] THEN
    MATCH_MP_TAC(REAL_ARITH `x = y ==> x <= abs y`) THEN
    AP_TERM_TAC THEN MATCH_MP_TAC INTEGRAL_SPIKE_SET THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
    SET_TAC[]]);;

let BANACH_ZARECKI_GEN = prove
 (`!f:real^1->real^1 s.
        is_interval s /\ bounded s
        ==> (f absolutely_continuous_on s <=>
             f continuous_on s /\
             f has_bounded_variation_on s /\
             !t. t SUBSET s /\ negligible t ==> negligible(IMAGE f t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_SIMP_TAC[ABSOLUTELY_CONTINUOUS_ON_IMP_HAS_BOUNDED_VARIATION_ON;
                 ABSOLUTELY_CONTINUOUS_ON_IMP_CONTINUOUS] THEN
    ASM_MESON_TAC[NEGLIGIBLE_ABSOLUTELY_CONTINUOUS_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a b:real^1. closure s = interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM CONNECTED_COMPACT_INTERVAL_1; COMPACT_CLOSURE] THEN
    MATCH_MP_TAC CONNECTED_CLOSURE THEN
    ASM_REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g:real^1->real^1.
        g continuous_on closure s /\
        !x. x IN s ==> g x = f x`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^1->real^1) uniformly_continuous_on s`
    MP_TAC THENL
     [ASM_SIMP_TAC[CONTINUOUS_BV_IMP_UNIFORMLY_CONTINUOUS];
      DISCH_THEN(MP_TAC o
        MATCH_MP UNIFORMLY_CONTINUOUS_EXTENDS_TO_CLOSURE) THEN
      MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[UNIFORMLY_CONTINUOUS_IMP_CONTINUOUS]];
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `g:real^1->real^1` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `interval[a:real^1,b]` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[CLOSURE_SUBSET]] THEN
    REWRITE_TAC[BANACH_ZARECKI] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_CLOSURE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_BOUNDED_VARIATION_ON_EQ THEN
      EXISTS_TAC `f:real^1->real^1` THEN ASM_MESON_TAC[];
      X_GEN_TAC `t:real^1->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC
       `IMAGE (g:real^1->real^1) (a INSERT b INSERT (t DIFF {a,b}))` THEN
      CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
      REWRITE_TAC[IMAGE_CLAUSES; NEGLIGIBLE_INSERT] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `t DIFF {a:real^1,b}`) THEN
      SUBGOAL_THEN `t DIFF {a:real^1,b} SUBSET s` ASSUME_TAC THENL
       [ALL_TAC;
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; SUBSET_DIFF]; ALL_TAC] THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]] THEN
      TRANS_TAC SUBSET_TRANS `interior(closure s):real^1->bool` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[INTERIOR_INTERVAL] THEN
        REWRITE_TAC[OPEN_CLOSED_INTERVAL_1] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> s DIFF u SUBSET t DIFF u`) THEN
        ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET_TRANS];
        ASM_MESON_TAC[CONVEX_INTERIOR_CLOSURE; IS_INTERVAL_CONVEX_1;
                      INTERIOR_SUBSET]]]]);;

let ABSOLUTELY_CONTINUOUS_DIFFERENTIABLE_BV_GEN = prove
 (`!f:real^1->real^N s t.
        is_interval s /\ bounded s /\
        f continuous_on s /\ f has_bounded_variation_on s /\
        COUNTABLE t /\
        (!x. x IN s DIFF t ==> f differentiable (at x within s))
        ==> f absolutely_continuous_on s`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `COUNTABLE(t:real^1->bool)` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[CONTINUOUS_ON_COMPONENTWISE_LIFT;
                   HAS_BOUNDED_VARIATION_ON_COMPONENTWISE;
                   DIFFERENTIABLE_COMPONENTWISE_WITHIN;
                   ABSOLUTELY_CONTINUOUS_ON_COMPONENTWISE] THEN
  REPLICATE_TAC 2 (DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [RIGHT_IMP_FORALL_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[AND_FORALL_THM] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `i:num` THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `g = \x. lift((f:real^1->real^N) x$i)` THEN
  FIRST_X_ASSUM(K ALL_TAC o SYM) THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BANACH_ZARECKI_GEN] THEN
  X_GEN_TAC `c:real^1->bool` THEN STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
  EXISTS_TAC `IMAGE (g:real^1->real^1) ((c DIFF t) UNION t)` THEN
  CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IMAGE_UNION] THEN
  ASM_SIMP_TAC[NEGLIGIBLE_COUNTABLE; COUNTABLE_IMAGE] THEN
  MATCH_MP_TAC NEGLIGIBLE_DIFFERENTIABLE_IMAGE_NEGLIGIBLE THEN
  REWRITE_TAC[LE_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[NEGLIGIBLE_SUBSET; SUBSET_DIFF]; ALL_TAC] THEN
  REWRITE_TAC[differentiable_on; IN_DIFF] THEN
  X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^1`) THEN
  ASM_MESON_TAC[DIFFERENTIABLE_WITHIN_SUBSET; SUBSET; IN_DIFF]);;

let ABSOLUTELY_CONTINUOUS_DIFFERENTIABLE_BV = prove
 (`!f:real^1->real^N a b.
        f differentiable_on interval[a,b] /\
        f has_bounded_variation_on interval[a,b]
        ==> f absolutely_continuous_on interval[a,b]`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ABSOLUTELY_CONTINUOUS_DIFFERENTIABLE_BV_GEN THEN
  EXISTS_TAC `{}:real^1->bool` THEN
  ASM_REWRITE_TAC[COUNTABLE_EMPTY; DIFF_EMPTY; GSYM differentiable_on] THEN
  ASM_SIMP_TAC[DIFFERENTIABLE_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[IS_INTERVAL_INTERVAL; BOUNDED_INTERVAL]);;

(* ------------------------------------------------------------------------- *)
(* Convergence in measure implies convergence AE of a subsequence.           *)
(* ------------------------------------------------------------------------- *)

let CONVERGENCE_IN_MEASURE = prove
 (`!f:num->real^M->real^N g s.
        (!n. f n measurable_on s) /\
        (!e. &0 < e
             ==> eventually
                  (\n. ?t. {x | x IN s /\ dist(f n x,g x) >= e} SUBSET t /\
                           measurable t /\ measure t < e)
                  sequentially)
        ==> ?r t. (!m n:num. m < n ==> r m < r n) /\
                  negligible t /\ t SUBSET s /\
                  !x. x IN s DIFF t
                      ==> ((\n. f (r n) x) --> g x) sequentially`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `?r. (!n. ?t. {x | x IN s /\ dist(f (r n) x,(g:real^M->real^N) x)
                                >= inv(&2 pow n)} SUBSET t /\
                      measurable t /\ measure t < inv(&2 pow n)) /\
        (!n. r n :num < r(SUC n))`
  MP_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `&1`);
      MAP_EVERY X_GEN_TAC [`n:num`; `p:num`] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `inv(&2 pow (SUC n))`)] THEN
    ASM_REWRITE_TAC[REAL_LT_01; REAL_LT_INV_EQ; REAL_LT_POW2] THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THENL
     [MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `m:num` THEN
      DISCH_THEN(MP_TAC o SPEC `m:num`) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[LE_REFL];
      DISCH_THEN(X_CHOOSE_THEN `m:num` (MP_TAC o SPEC `m + p + 1:num`)) THEN
      DISCH_THEN(fun th -> EXISTS_TAC `m + p + 1:num` THEN MP_TAC th) THEN
      REWRITE_TAC[LE_ADD; ARITH_RULE `p < m + p + 1`]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:num->num` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM; FORALL_AND_THM] THEN
    X_GEN_TAC `t:num->real^M->bool` THEN STRIP_TAC] THEN
  EXISTS_TAC `s INTER
       INTERS {UNIONS {(t:num->real^M->bool) k | n <= k} | n IN (:num)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
    MATCH_MP_TAC NEGLIGIBLE_INTER THEN DISJ2_TAC THEN
    SIMP_TAC[NEGLIGIBLE_OUTER_LE] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e / &2`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_POW_INV; REAL_HALF] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS {(t:num->real^M->bool) k | N <= k}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `x IN s ==> INTERS s SUBSET x`) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[LE_EXISTS; SET_RULE
     `{f n | ?d. n = N + d} = {f(N + n) | n IN (:num)}`] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `n:num` THEN
    TRANS_TAC REAL_LE_TRANS `sum(0..n) (\k. inv(&2 pow (N + k)))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_LE_NUMSEG THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_POW_ADD; REAL_INV_MUL; SUM_LMUL; GSYM REAL_POW_INV] THEN
    REWRITE_TAC[SUM_GP; CONJUNCT1 LT] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[real_div; REAL_MUL_LID; REAL_INV_INV] THEN
    REWRITE_TAC[REAL_ARITH `x * y * &2 <= e <=> y * x <= e / &2`] THEN
    REWRITE_TAC[REAL_POW_INV] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `n < e / &2 ==> &0 <= x * n ==> (&1 - x) * n <= e / &2`)) THEN
    REWRITE_TAC[GSYM REAL_INV_MUL; REAL_LE_INV_EQ; GSYM REAL_POW_ADD] THEN
    SIMP_TAC[REAL_POW_LE; REAL_POS];

    REWRITE_TAC[INTER_SUBSET];
    X_GEN_TAC `x:real^M` THEN
    REWRITE_TAC[SET_RULE `s DIFF (s INTER t) = s DIFF t`] THEN
    REWRITE_TAC[IN_DIFF; INTERS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_EXISTS_THM] THEN
    REWRITE_TAC[TAUT `~(a /\ b) <=> a ==> ~b`] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (LABEL_TAC "*")) THEN
    REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`inv(&2)`; `e:real`] REAL_ARCH_POW_INV) THEN
    ASM_REWRITE_TAC[REAL_POW_INV] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `M:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `N + M:num` THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `n:num`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [SUBSET]) THEN
    DISCH_THEN(MP_TAC o SPECL [`n:num`; `x:real^M`]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_ge; REAL_NOT_LE] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LT_TRANS) THEN
    TRANS_TAC REAL_LET_TRANS `inv(&2 pow M)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM REAL_POW_INV] THEN MATCH_MP_TAC REAL_POW_MONO_INV THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Fubini-type results for measure.                                          *)
(* ------------------------------------------------------------------------- *)

let FUBINI_MEASURE = prove
 (`!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {x | ~measurable {y | pastecart x y IN s}} /\
            ((\x. lift(measure {y | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`,
  let MEASURE_PASTECART_INTERVAL = prove
   (`!a b:real^(M,N)finite_sum.
          (!x. measurable {y | pastecart x y IN interval[a,b]}) /\
          ((\x. lift(measure {y | pastecart x y IN interval[a,b]}))
           has_integral lift(measure(interval[a,b]))) UNIV`,
    REWRITE_TAC[FORALL_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `c:real^N`; `b:real^M`; `d:real^N`] THEN
    REWRITE_TAC[GSYM PCROSS_INTERVAL; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[SET_RULE `{x | P /\ Q x} = if P then {x | Q x} else {}`] THEN
    REWRITE_TAC[COND_RAND; SET_RULE `{x | x IN s} = s`] THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; MEASURABLE_EMPTY; COND_ID] THEN
    REWRITE_TAC[MEASURE_EMPTY; LIFT_NUM; HAS_INTEGRAL_RESTRICT_UNIV] THEN
    REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART] THEN
    REWRITE_TAC[LIFT_CMUL; HAS_INTEGRAL_CONST]) in
  let MEASURE_PASTECART_ELEMENTARY = prove
   (`!s:real^(M,N)finite_sum->bool.
          (?d. d division_of s)
          ==> (!x. measurable {y | pastecart x y IN s}) /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    let lemma = prove
     (`{x | f x IN UNIONS s} = UNIONS {{x | f x IN d} | d IN s}`,
      REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
    GEN_TAC THEN REWRITE_TAC[division_of; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `d:(real^(M,N)finite_sum->bool)->bool` THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[lemma] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `s:real^M` THEN MATCH_MP_TAC MEASURABLE_UNIONS THEN
      ASM_SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `k:real^(M,N)finite_sum->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?a b:real^(M,N)finite_sum. k = interval[a,b]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[MEASURE_PASTECART_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `((\x. vsum d (\k. lift(measure {y | pastecart x y IN k}))) has_integral
       vsum d (\k:real^(M,N)finite_sum->bool. lift(measure k))) UNIV`
    MP_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_VSUM THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `k:real^(M,N)finite_sum->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?a b:real^(M,N)finite_sum. k = interval[a,b]`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[MEASURE_PASTECART_INTERVAL];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[HAS_INTEGRAL_SPIKE]
     `!t. negligible t /\ a = b /\ (!x. x IN s DIFF t ==> g x = f x)
          ==> (f has_integral a) s ==> (g has_integral b) s`) THEN
    EXISTS_TAC
     `UNIONS { {x | (x:real^M)$i =
                    fstcart(interval_lowerbound k:real^(M,N)finite_sum)$i} |
               i IN 1..dimindex(:M) /\ k IN d} UNION
      UNIONS { {x | x$i = fstcart(interval_upperbound k)$i} |
               i IN 1..dimindex(:M) /\ k IN d}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      CONJ_TAC THEN MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
      ASM_SIMP_TAC[ONCE_REWRITE_RULE[CONJ_SYM] FINITE_PRODUCT_DEPENDENT;
                   FINITE_NUMSEG] THEN
      SIMP_TAC[FORALL_IN_GSPEC; NEGLIGIBLE_STANDARD_HYPERPLANE; IN_NUMSEG];
      REWRITE_TAC[IN_DIFF; IN_UNIV]] THEN
    REWRITE_TAC[REWRITE_RULE[o_DEF] (GSYM LIFT_SUM); FUN_EQ_THM; LIFT_EQ] THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS;
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[SIMPLE_IMAGE] THEN
      MATCH_MP_TAC MEASURE_NEGLIGIBLE_UNIONS_IMAGE] THEN
    ASM_REWRITE_TAC[GSYM HAS_MEASURE_MEASURE] THEN
    (CONJ_TAC THENL
      [ASM_MESON_TAC[MEASURE_PASTECART_INTERVAL; MEASURABLE_INTERVAL];
       ALL_TAC]) THEN
    MAP_EVERY X_GEN_TAC
     [`k:real^(M,N)finite_sum->bool`; `l:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL
     [`k:real^(M,N)finite_sum->bool`; `l:real^(M,N)finite_sum->bool`]) THEN
    ASM_REWRITE_TAC[GSYM INTERIOR_INTER] THEN
    (SUBGOAL_THEN
      `?a b:real^(M,N)finite_sum c d:real^(M,N)finite_sum.
              k = interval[a,b] /\ l = interval[c,d]`
     MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    SIMP_TAC[LEFT_IMP_EXISTS_THM; NEGLIGIBLE_CONVEX_INTERIOR;
             CONVEX_INTER; CONVEX_INTERVAL] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL;
                PASTECART_IN_PCROSS] THEN
    ONCE_REWRITE_TAC[SET_RULE
     `{x | P /\ Q x} INTER {x | R /\ S x} =
      {x | P /\ R} INTER {x | Q x /\ S x}`] THEN
    REWRITE_TAC[INTER_PCROSS; INTERIOR_PCROSS; GSYM INTER] THEN
    REWRITE_TAC[SET_RULE `{x | P} = if P then UNIV else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[NEGLIGIBLE_EMPTY; INTER_EMPTY; INTER_UNIV] THEN
    SIMP_TAC[NEGLIGIBLE_CONVEX_INTERIOR; CONVEX_INTER; CONVEX_INTERVAL] THEN
    REWRITE_TAC[PCROSS_EQ_EMPTY; TAUT `(if p then q else T) <=> p ==> q`] THEN
    REWRITE_TAC[TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
    SIMP_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE RAND_CONV [IN_UNION]) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN(fun th ->
     MP_TAC(SPEC  `l:real^(M,N)finite_sum->bool` th) THEN
     MP_TAC(SPEC  `k:real^(M,N)finite_sum->bool` th))) THEN
    REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[PCROSS_INTERVAL]) THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_REWRITE_TAC[TAUT `~a \/ b <=> a ==> b`] THEN
    ASM_SIMP_TAC[INTERVAL_LOWERBOUND_NONEMPTY; INTERVAL_UPPERBOUND_NONEMPTY;
                 FSTCART_PASTECART] THEN
    REPLICATE_TAC 3 (GEN_REWRITE_TAC I [IMP_IMP]) THEN
    MATCH_MP_TAC(TAUT `(a ==> c ==> ~b) ==> a ==> b ==> c ==> d`) THEN
    REWRITE_TAC[IN_INTERVAL; INTERVAL_NE_EMPTY; AND_FORALL_THM;
                INTERIOR_INTERVAL; IMP_IMP; INTER_INTERVAL] THEN
    MATCH_MP_TAC MONO_FORALL THEN SIMP_TAC[LAMBDA_BETA] THEN
    GEN_TAC THEN ONCE_REWRITE_TAC[GSYM IMP_CONJ_ALT] THEN
    ONCE_REWRITE_TAC[IMP_CONJ] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN REAL_ARITH_TAC) in
  let MEASURE_PASTECART_OPEN_MEASURABLE = prove
   (`!s:real^(M,N)finite_sum->bool.
          open s /\ measurable s
          ==> negligible {x | ~measurable {y | pastecart x y IN s}} /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    let lemur = prove
     (`UNIONS {{y | pastecart x y IN g n} | n IN (:num)} =
       {y | pastecart x y IN UNIONS {g n | n IN (:num)}}`,
      REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
    GEN_TAC THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `g:num->real^(M,N)finite_sum->bool`
     STRIP_ASSUME_TAC o MATCH_MP OPEN_COUNTABLE_LIMIT_ELEMENTARY) THEN
    SUBGOAL_THEN `!n:num. g n SUBSET (s:real^(M,N)finite_sum->bool)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)})`;
      `(:real^M)`] BEPPO_LEVI_MONOTONE_CONVERGENCE_INCREASING) THEN
    MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->bool) n`
          MEASURE_PASTECART_ELEMENTARY)) THEN
    ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL; FORALL_AND_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; LIFT_DROP] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
        REPEAT(CONJ_TAC THENL
         [ASM_MESON_TAC[MEASURE_PASTECART_ELEMENTARY]; ALL_TAC]) THEN
        ASM SET_TAC[];
        REWRITE_TAC[bounded; FORALL_IN_GSPEC; NORM_LIFT] THEN
        EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
        GEN_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `&0 <= x /\ x <= y ==> abs x <= y`) THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MEASURE_POS_LE;
          MATCH_MP_TAC MEASURE_SUBSET] THEN
        ASM_MESON_TAC[MEASURABLE_ELEMENTARY]];
      REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->real^1`; `t:real^M->bool`] THEN
    STRIP_TAC THEN REWRITE_TAC[GSYM HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    SUBGOAL_THEN
     `!x:real^M.
         ~(x IN t) ==> {y:real^N | pastecart x y IN s} has_measure drop(f x)`
    ASSUME_TAC THENL
     [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP CONVERGENT_IMP_BOUNDED) THEN
      REWRITE_TAC[BOUNDED_POS; FORALL_IN_IMAGE; IN_UNIV; NORM_LIFT] THEN
      DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN MP_TAC(ISPECL
       [`\n. {y | pastecart x y IN (g:num->real^(M,N)finite_sum->bool) n}`;
        `B:real`]
       HAS_MEASURE_NESTED_UNIONS) THEN
      ASM_SIMP_TAC[lemur; REAL_ARITH `abs x <= B ==> x <= B`] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; GSYM LIFT_EQ] THEN
      ASM_MESON_TAC[LIM_UNIQUE; TRIVIAL_LIMIT_SEQUENTIALLY; LIFT_DROP];
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
        REWRITE_TAC[measurable] THEN ASM SET_TAC[];
        MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
        MAP_EVERY EXISTS_TAC [`f:real^M->real^1`; `t:real^M->bool`] THEN
        ASM_REWRITE_TAC[NEGLIGIBLE; IN_DIFF; IN_UNIV] THEN
        REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURE_UNIQUE]; ALL_TAC] THEN
        ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN EXISTS_TAC
          `\k. lift(measure ((g:num->real^(M,N)finite_sum->bool) k))` THEN
        ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
        MP_TAC(ISPECL [`g:num->real^(M,N)finite_sum->bool`;
                       `measure(s:real^(M,N)finite_sum->bool)`]
                  HAS_MEASURE_NESTED_UNIONS) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_MESON_TAC[MEASURABLE_ELEMENTARY; MEASURE_SUBSET]]]) in
  let MEASURE_PASTECART_COMPACT = prove
   (`!s:real^(M,N)finite_sum->bool.
          compact s
          ==> (!x. measurable {y | pastecart x y IN s}) /\
              ((\x. lift(measure {y | pastecart x y IN s}))
               has_integral lift(measure s)) UNIV`,
    GEN_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MEASURABLE_COMPACT THEN
      REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o MATCH_MP COMPACT_IMP_BOUNDED) THEN
        REWRITE_TAC[BOUNDED_POS; FORALL_IN_GSPEC] THEN
        MESON_TAC[NORM_LE_PASTECART; REAL_LE_TRANS];
        MATCH_MP_TAC CONTINUOUS_CLOSED_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CONTINUOUS_PASTECART;
                     CONTINUOUS_CONST; CONTINUOUS_AT_ID]];
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `?t:real^(M,N)finite_sum->bool.
          open t /\ measurable t /\ s SUBSET t`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[BOUNDED_SUBSET_BALL; COMPACT_IMP_BOUNDED;
                    MEASURABLE_BALL; OPEN_BALL];
      ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^(M,N)finite_sum->bool`
      MEASURE_PASTECART_OPEN_MEASURABLE) THEN
    MP_TAC(ISPEC `t DIFF s:real^(M,N)finite_sum->bool`
      MEASURE_PASTECART_OPEN_MEASURABLE) THEN
    ASM_SIMP_TAC[MEASURABLE_DIFF; MEASURABLE_COMPACT; OPEN_DIFF;
                 COMPACT_IMP_CLOSED; MEASURE_DIFF_SUBSET; IMP_IMP] THEN
    DISCH_THEN(CONJUNCTS_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[LIFT_SUB; IMP_IMP] THEN
    DISCH_THEN(MP_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN
    REWRITE_TAC[VECTOR_ARITH `t - (t - s):real^1 = s`] THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
          HAS_INTEGRAL_SPIKE)) THEN
    EXISTS_TAC
     `{x | ~measurable {y | pastecart x y IN t DIFF s}} UNION
      {x:real^M | ~measurable {y:real^N | pastecart x y IN t}}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^M` THEN
    SIMP_TAC[IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
    STRIP_TAC THEN REWRITE_TAC[LIFT_EQ; GSYM LIFT_SUB] THEN
    ONCE_REWRITE_TAC[REAL_ARITH `a:real = b - c <=> c = b - a`] THEN
    REWRITE_TAC[SET_RULE
     `{y | pastecart x y IN t /\ ~(pastecart x y IN s)} =
      {y | pastecart x y IN t} DIFF {y | pastecart x y IN s}`] THEN
    MATCH_MP_TAC MEASURE_DIFF_SUBSET THEN ASM SET_TAC[]) in
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?f. (!n. compact(f n) /\ f n SUBSET s /\ measurable(f n) /\
             measure s < measure(f n) + inv(&n + &1)) /\
        (!n. (f:num->real^(M,N)finite_sum->bool) n SUBSET f(SUC n))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_INNER_COMPACT THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `inv(&(SUC n) + &1)`]
        MEASURABLE_INNER_COMPACT) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t UNION u:real^(M,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[COMPACT_UNION; UNION_SUBSET; MEASURABLE_UNION] THEN
    REWRITE_TAC[SUBSET_UNION] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `s < a + e ==> a <= b ==> s < b + e`)) THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_UNION; SUBSET_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. (!n. open(g n) /\ s SUBSET g n /\ measurable(g n) /\
             measure(g n) < measure s + inv(&n + &1)) /\
        (!n. (g:num->real^(M,N)finite_sum->bool) (SUC n) SUBSET g n)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC DEPENDENT_CHOICE THEN CONJ_TAC THENL
     [MATCH_MP_TAC MEASURABLE_OUTER_OPEN THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`n:num`; `t:real^(M,N)finite_sum->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:real^(M,N)finite_sum->bool`; `inv(&(SUC n) + &1)`]
        MEASURABLE_OUTER_OPEN) THEN
    ASM_REWRITE_TAC[REAL_LT_INV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^(M,N)finite_sum->bool`
        STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t INTER u:real^(M,N)finite_sum->bool` THEN
    ASM_SIMP_TAC[OPEN_INTER; SUBSET_INTER; MEASURABLE_INTER] THEN
    REWRITE_TAC[INTER_SUBSET] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REAL_ARITH `a < s + e ==> b <= a ==> b < s + e`)) THEN
    MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_SIMP_TAC[MEASURABLE_INTER; INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)}) -
                      lift(measure {y:real^N | pastecart x y IN (f n)})`;
    `(:real^M)`] BEPPO_LEVI_MONOTONE_CONVERGENCE_DECREASING_AE) THEN
  MP_TAC(GEN `n:num` (ISPEC `(f:num->real^(M,N)finite_sum->bool) n`
        MEASURE_PASTECART_COMPACT)) THEN
  MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->bool) n`
        MEASURE_PASTECART_OPEN_MEASURABLE)) THEN
  ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL; FORALL_AND_THM] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; DROP_SUB; LIFT_DROP] THEN
  ASM_SIMP_TAC[INTEGRABLE_SUB; INTEGRAL_SUB] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `n:num` THEN EXISTS_TAC
       `{x:real^M | ~measurable {y:real^N | pastecart x y IN g n}} UNION
        {x:real^M | ~measurable {y | pastecart x y IN g (SUC n)}}` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_UNION; DE_MORGAN_THM] THEN
      X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH `f <= f' /\ g' <= g ==> g' - f' <= g - f`) THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
      EXISTS_TAC `measure((g:num->real^(M,N)finite_sum->bool) 0) -
                  measure((f:num->real^(M,N)finite_sum->bool) 0)` THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM LIFT_SUB; NORM_LIFT] THEN
      MATCH_MP_TAC(REAL_ARITH
       `!s. f' <= s /\ s <= g' /\ f <= f' /\ g' <= g
            ==> abs(g' - f') <= g - f`) THEN
      EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
      REPEAT CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ARITH_RULE `0 <= n`) THEN
      SPEC_TAC(`n:num`,`n:num`) THEN SPEC_TAC(`0`,`m:num`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`h:real^M->real^1`; `k:real^M->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `?t. negligible t /\
        (!n x. ~(x IN t) ==> measurable {y:real^N | pastecart x y IN g n}) /\
        (!x. ~(x IN t)
             ==> ((\k. lift(measure {y | pastecart x y IN g k}) -
                  lift(measure {y:real^N | pastecart x y IN f k})) --> vec 0)
                  sequentially) /\
        (!x. ~(x IN t) ==> (h:real^M->real^1) x = vec 0)`
  MP_TAC THENL
   [MP_TAC(ISPECL
     [`\x. if x IN UNIONS{ {x | ~measurable {y:real^N | pastecart x y IN g n}}
                           |  n IN (:num)} UNION k
           then vec 0 else (h:real^M->real^1) x`; `(:real^M)`]
     HAS_INTEGRAL_NEGLIGIBLE_EQ) THEN
    REWRITE_TAC[IN_UNIV; DIMINDEX_1; FORALL_1] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real^M` THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN
      COND_CASES_TAC THEN REWRITE_TAC[VEC_COMPONENT; REAL_LE_REFL] THEN
      FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [DE_MORGAN_THM]) THEN
      MATCH_MP_TAC(ISPEC `sequentially` LIM_COMPONENT_LBOUND) THEN
      EXISTS_TAC
       `\k:num. lift(measure {y | pastecart x y IN
                                  (g:num->real^(M,N)finite_sum->bool) k}) -
                lift(measure {y | pastecart x y IN
                                  (f:num->real^(M,N)finite_sum->bool) k})` THEN
      REWRITE_TAC[DIMINDEX_1; TRIVIAL_LIMIT_SEQUENTIALLY; LE_REFL] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC ALWAYS_EVENTUALLY THEN
      X_GEN_TAC `n:num` THEN REWRITE_TAC[GSYM drop; DROP_SUB; LIFT_DROP] THEN
      REWRITE_TAC[REAL_SUB_LE] THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[UNIONS_GSPEC]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
     [MATCH_MP_TAC HAS_INTEGRAL_SPIKE THEN
      EXISTS_TAC `h:real^M->real^1` THEN
      EXISTS_TAC `UNIONS{ {x | ~measurable {y | pastecart x y IN
                                 (g:num->real^(M,N)finite_sum->bool) n}}
                           |  n IN (:num)} UNION k` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNION; IN_UNIV] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IN_UNIV] NEGLIGIBLE_COUNTABLE_UNIONS) THEN
        ASM_REWRITE_TAC[];
        MESON_TAC[];
        ASM_REWRITE_TAC[HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
        MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN EXISTS_TAC
         `\k. lift(measure((g:num->real^(M,N)finite_sum->bool) k)) -
              lift(measure((f:num->real^(M,N)finite_sum->bool) k))` THEN
        ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
        REWRITE_TAC[LIM_SEQUENTIALLY; GSYM LIFT_SUB; DIST_0; NORM_LIFT] THEN
        X_GEN_TAC `e:real` THEN DISCH_TAC THEN
        MP_TAC(SPEC `e / &2` REAL_ARCH_INV) THEN
        ASM_REWRITE_TAC[REAL_HALF] THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
        X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
         `!s d. f <= s /\ s <= g /\ s < f + d /\ g < s + d /\ d <= e / &2
                ==> abs(g - f) < e`) THEN
        EXISTS_TAC `measure(s:real^(M,N)finite_sum->bool)` THEN
        EXISTS_TAC `inv(&n + &1)` THEN ASM_REWRITE_TAC[CONJ_ASSOC] THEN
        CONJ_TAC THENL [ASM_MESON_TAC[MEASURE_SUBSET]; ALL_TAC] THEN
        TRANS_TAC REAL_LE_TRANS `inv(&N)` THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
        REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
        ASM_ARITH_TAC];
      DISCH_TAC THEN EXISTS_TAC
       `{x | ~((if x IN
         UNIONS {{x | ~measurable {y | pastecart x y IN g n}} | n | T} UNION k
                then vec 0 else (h:real^M->real^1) x) = vec 0)} UNION
        UNIONS {{x | ~measurable {y | pastecart x y IN
                     (g:num->real^(M,N)finite_sum->bool) n}} | n | T} UNION
        k` THEN
      ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN
      ASM_SIMP_TAC[IN_UNION; DE_MORGAN_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[IN_UNIV] NEGLIGIBLE_COUNTABLE_UNIONS) THEN
        ASM_REWRITE_TAC[];
        CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
        REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]]];
    FIRST_X_ASSUM(K ALL_TAC o SPEC `x:real^M`) THEN STRIP_TAC] THEN
  SUBGOAL_THEN
   `!x:real^M. ~(x IN t) ==> measurable {y:real^N | pastecart x y IN s}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[MEASURABLE_INNER_OUTER] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPEC `x:real^M` th) THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [LIM_SEQUENTIALLY]) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[DIST_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `N:num` (MP_TAC o SPEC `N:num`)) THEN
    REWRITE_TAC[LE_REFL; GSYM LIFT_SUB; NORM_LIFT] THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`{y | pastecart x y IN (f:num->real^(M,N)finite_sum->bool) N}`;
      `{y | pastecart x y IN (g:num->real^(M,N)finite_sum->bool) N}`] THEN
    ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[REAL_ABS_SUB] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN EXISTS_TAC `t:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\n:num x:real^M. lift(measure {y:real^N | pastecart x y IN (g n)})`;
    `\x:real^M. lift(measure {y:real^N | pastecart x y IN s})`;
    `(:real^M)`; `t:real^M->bool`] MONOTONE_CONVERGENCE_DECREASING_AE) THEN
  ASM_REWRITE_TAC[LIFT_DROP; IN_UNIV; IN_DIFF] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[IN_DIFF] THEN ASM SET_TAC[];
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
      REWRITE_TAC[LIM_SEQUENTIALLY] THEN X_GEN_TAC `e:real` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(fun th ->
        MP_TAC(SPEC `x:real^M` th) THEN ASM_REWRITE_TAC[] THEN
        GEN_REWRITE_TAC LAND_CONV [LIM_SEQUENTIALLY]) THEN
      DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_SIMP_TAC[DIST_0] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
      MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[DIST_LIFT; GSYM dist] THEN
      MATCH_MP_TAC(REAL_ARITH
       `f <= s /\ s <= g ==> abs(g - f) < e ==> abs(g - s) < e`) THEN
      CONJ_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[IN_DIFF] THEN ASM SET_TAC[];
      REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
      EXISTS_TAC `measure((g:num->real^(M,N)finite_sum->bool) 0)` THEN
      ASM_SIMP_TAC[NORM_LIFT; real_abs; MEASURE_POS_LE] THEN
      X_GEN_TAC `m:num` THEN MP_TAC(ARITH_RULE `0 <= m`) THEN
      SPEC_TAC(`m:num`,`m:num`) THEN SPEC_TAC(`0`,`n:num`) THEN
      MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
      REPEAT(CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC]) THEN
      GEN_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ISPEC `sequentially` LIM_UNIQUE) THEN
    EXISTS_TAC `\k. lift(measure((g:num->real^(M,N)finite_sum->bool) k))` THEN
    ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
    REWRITE_TAC[LIM_SEQUENTIALLY; DIST_LIFT] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MP_TAC(SPEC `e:real` REAL_ARCH_INV) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN STRIP_TAC THEN
    X_GEN_TAC `n:num` THEN DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH
     `!d. g < s + d /\ s <= g /\ d < e ==> abs(g - s) < e`) THEN
    EXISTS_TAC `inv(&n + &1)` THEN ASM_SIMP_TAC[MEASURE_SUBSET] THEN
    TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT; REAL_OF_NUM_ADD] THEN
    ASM_ARITH_TAC]);;

let FUBINI_MEASURE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        measurable s
        ==> negligible {y | ~measurable {x | pastecart x y IN s}} /\
            ((\y. lift(measure {x | pastecart x y IN s}))
             has_integral lift(measure s)) UNIV`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_MEASURE) THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[measurable; measure] THEN
    ASM_REWRITE_TAC[GSYM measurable; GSYM measure] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let FUBINI_LEBESGUE_MEASURABLE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {x | ~lebesgue_measurable {y | pastecart x y IN s}}`,
  let lemma = prove
   (`{x | ?n. P n x} = UNIONS {{x | P n x} | n IN (:num)}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_COUNTABLE_INTERVALS] THEN
  X_GEN_TAC `m:num` THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS] THEN
  REWRITE_TAC[INTER; IN_ELIM_THM; NOT_FORALL_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `n:num` THEN
  MP_TAC(ISPEC `(s:real^(M,N)finite_sum->bool) INTER
                (interval[--vec m,vec m] PCROSS interval[--vec n,vec n])`
        FUBINI_MEASURE) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PCROSS_INTERVAL] THEN
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^M` THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN
  ASM_CASES_TAC `(x:real^M) IN interval[--vec m,vec m]` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; MEASURABLE_EMPTY]);;

let FUBINI_LEBESGUE_MEASURABLE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> negligible {y | ~lebesgue_measurable {x | pastecart x y IN s}}`,
  let lemma = prove
   (`{x | ?n. P n x} = UNIONS {{x | P n x} | n IN (:num)}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[NEGLIGIBLE_ON_COUNTABLE_INTERVALS] THEN
  X_GEN_TAC `n:num` THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_COUNTABLE_SUBINTERVALS] THEN
  REWRITE_TAC[INTER; IN_ELIM_THM; NOT_FORALL_THM; LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[lemma] THEN MATCH_MP_TAC NEGLIGIBLE_COUNTABLE_UNIONS THEN
  X_GEN_TAC `m:num` THEN
  MP_TAC(ISPEC `(s:real^(M,N)finite_sum->bool) INTER
                (interval[--vec m,vec m] PCROSS interval[--vec n,vec n])`
        FUBINI_MEASURE_ALT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PCROSS_INTERVAL] THEN
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_MEASURABLE_ON_SUBINTERVALS];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_INTER; PASTECART_IN_PCROSS] THEN
  ASM_CASES_TAC `(y:real^N) IN interval[--vec n,vec n]` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; MEASURABLE_EMPTY]);;

let FUBINI_NEGLIGIBLE = prove
 (`!s. negligible s
       ==> negligible
            {x:real^M | ~negligible {y:real^N | pastecart x y IN s}}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE o MATCH_MP
    NEGLIGIBLE_IMP_MEASURABLE) THEN
  ASM_SIMP_TAC[MEASURE_EQ_0; LIFT_NUM; IMP_CONJ] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`\x:real^M. lift (measure {y:real^N | pastecart x y IN s})`;
    `(:real^M)`;
    `{x:real^M | ~measurable {y:real^N | pastecart x y IN s}}`]
   HAS_INTEGRAL_NEGLIGIBLE_EQ_AE) THEN
  ASM_REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_DIFF; IN_ELIM_THM] THEN
  SIMP_TAC[IMP_IMP; FORALL_1; DIMINDEX_1; GSYM drop; LIFT_DROP; IN_UNIV] THEN
  ASM_SIMP_TAC[MEASURE_POS_LE; IMP_CONJ] THEN DISCH_THEN(K ALL_TAC) THEN
  UNDISCH_TAC
   `negligible {x:real^M | ~measurable {y:real^N | pastecart x y IN s}}` THEN
  REWRITE_TAC[IMP_IMP; GSYM NEGLIGIBLE_UNION_EQ] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] NEGLIGIBLE_SUBSET) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; GSYM DROP_EQ] THEN
  REWRITE_TAC[LIFT_DROP; DROP_VEC] THEN
  REWRITE_TAC[HAS_MEASURE_MEASURE; GSYM HAS_MEASURE_0] THEN
  SET_TAC[]);;

let FUBINI_NEGLIGIBLE_ALT = prove
 (`!s. negligible s
       ==> negligible
            {y:real^N | ~negligible {x:real^M | pastecart x y IN s}}`,
  let lemma = prove
   (`!s:real^(M,N)finite_sum->bool.
        negligible s
         ==> negligible (IMAGE (\z. pastecart (sndcart z) (fstcart z)) s)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_GEN THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM; LE_REFL] THEN
    REWRITE_TAC[linear; FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL;
                GSYM PASTECART_ADD; GSYM PASTECART_CMUL]) in
  GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP lemma) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_NEGLIGIBLE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; PASTECART_INJ;
                FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM] THEN
  REWRITE_TAC[UNWIND_THM1; UNWIND_THM2]);;

let NEGLIGIBLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        negligible(s PCROSS t) <=> negligible s \/ negligible t`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_NEGLIGIBLE) THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[SET_RULE `{y | P /\ Q y} = if P then {y | Q y} else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
    ASM_CASES_TAC `negligible(t:real^N->bool)` THEN
    ASM_REWRITE_TAC[SET_RULE `~(if P then F else T) = P`;
                    SET_RULE `{x | x IN s} = s`];
    ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; INTER_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`aa:real^M`; `a:real^N`; `bb:real^M`; `b:real^N`] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `(s:real^M->bool) PCROSS interval[a:real^N,b]` THEN
    REWRITE_TAC[SUBSET_PCROSS; INTER_SUBSET] THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
     [`s:real^M->bool`; `e / (content(interval[a:real^N,b]) + &1)`]
     MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_LT_DIV; CONTENT_POS_LE;
      MEASURE_EQ_0; REAL_ADD_LID; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS { (k:real^M->bool) PCROSS interval[a:real^N,b] |
                         k IN d}` THEN
    ASM_REWRITE_TAC[GSYM PCROSS_UNIONS; SUBSET_PCROSS; SUBSET_REFL] THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D:(real^M->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL; SUBSET];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum D (\k:real^M->bool. measure k * content(interval[a:real^N,b]))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^M. k = interval[u,v]` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART];
      REWRITE_TAC[SUM_RMUL]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x * (y + &1) <= e ==> x * y <= e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      ASM_MESON_TAC[MEASURE_POS_LE; SUBSET; MEASURABLE_INTERVAL];
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               CONTENT_POS_LE]] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
    TRANS_TAC REAL_LE_TRANS `measure(UNIONS D:real^M->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE;
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[SUBSET_UNIONS] THEN
      ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_INTERVAL; SUBSET]] THEN
    TRANS_TAC EQ_TRANS `sum (D:(real^M->bool)->bool) content` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_ELEMENTARY THEN
      REWRITE_TAC[division_of] THEN ASM SET_TAC[]];
    ONCE_REWRITE_TAC[NEGLIGIBLE_ON_INTERVALS] THEN
    REWRITE_TAC[FORALL_PASTECART; GSYM PCROSS_INTERVAL; INTER_PCROSS] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `aa:real^N`; `b:real^M`; `bb:real^N`] THEN
    MATCH_MP_TAC NEGLIGIBLE_SUBSET THEN
    EXISTS_TAC `interval[a:real^M,b] PCROSS (t:real^N->bool)` THEN
    REWRITE_TAC[SUBSET_PCROSS; INTER_SUBSET] THEN
    REWRITE_TAC[NEGLIGIBLE_OUTER_LE] THEN
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN MP_TAC(ISPECL
     [`t:real^N->bool`; `e / (content(interval[a:real^M,b]) + &1)`]
     MEASURABLE_OUTER_CLOSED_INTERVALS) THEN
    ASM_SIMP_TAC[NEGLIGIBLE_IMP_MEASURABLE; REAL_LT_DIV; CONTENT_POS_LE;
      MEASURE_EQ_0; REAL_ADD_LID; REAL_ARITH `&0 <= x ==> &0 < x + &1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `UNIONS { interval[a:real^M,b] PCROSS (k:real^N->bool) |
                         k IN d}` THEN
    ASM_REWRITE_TAC[GSYM PCROSS_UNIONS; SUBSET_PCROSS; SUBSET_REFL] THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN
    MATCH_MP_TAC MEASURE_COUNTABLE_UNIONS_LE_STRONG_GEN THEN
    ASM_SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; FORALL_IN_IMAGE] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[CONJ_SYM] THEN
    REWRITE_TAC[FORALL_FINITE_SUBSET_IMAGE] THEN
    X_GEN_TAC `D:(real^N->bool)->bool` THEN STRIP_TAC THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MEASURE_UNIONS_LE_IMAGE o
      lhand o snd) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[MEASURABLE_INTERVAL; PCROSS_INTERVAL; SUBSET];
      MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)] THEN
    TRANS_TAC REAL_LE_TRANS
     `sum D (\k:real^N->bool. content(interval[a:real^M,b]) * measure k)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE THEN MATCH_MP_TAC SUM_EQ THEN
      X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?u v:real^N. k = interval[u,v]` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]] THEN
      ASM_REWRITE_TAC[PCROSS_INTERVAL; MEASURE_INTERVAL; CONTENT_PASTECART];
      REWRITE_TAC[SUM_LMUL]] THEN
    MATCH_MP_TAC(REAL_ARITH
     `&0 <= x /\ x * (y + &1) <= e ==> y * x <= e`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN
      ASM_MESON_TAC[MEASURE_POS_LE; SUBSET; MEASURABLE_INTERVAL];
      SIMP_TAC[GSYM REAL_LE_RDIV_EQ; REAL_ARITH `&0 <= x ==> &0 < x + &1`;
               CONTENT_POS_LE]] THEN
    FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] REAL_LE_TRANS)) THEN
    TRANS_TAC REAL_LE_TRANS `measure(UNIONS D:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_EQ_IMP_LE;
      MATCH_MP_TAC MEASURE_SUBSET THEN
      ASM_SIMP_TAC[SUBSET_UNIONS] THEN
      ASM_MESON_TAC[MEASURABLE_UNIONS; MEASURABLE_INTERVAL; SUBSET]] THEN
    TRANS_TAC EQ_TRANS `sum (D:(real^N->bool)->bool) content` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN ASM_MESON_TAC[MEASURE_INTERVAL; SUBSET];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_ELEMENTARY THEN
      REWRITE_TAC[division_of] THEN ASM SET_TAC[]]]);;

let FUBINI_TONELLI_MEASURE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {x | ~measurable {y | pastecart x y IN s}} /\
             (\x. lift(measure {y | pastecart x y IN s})) integrable_on UNIV)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ASM_MESON_TAC[FUBINI_MEASURE; integrable_on]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`\n. s INTER ball(vec 0:real^(M,N)finite_sum,&n)`;
    `drop(integral (:real^M)
       (\x. lift (measure {y:real^N | pastecart x y IN s})))`]
       MEASURABLE_NESTED_UNIONS) THEN
  ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
               MEASURABLE_BALL; GSYM REAL_OF_NUM_SUC; SUBSET_BALL;
               REAL_ARITH `x <= x + &1`;
               SET_RULE `t SUBSET u ==> s INTER t SUBSET s INTER u`] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `n:num` THEN
    MP_TAC(SPEC `s INTER ball(vec 0:real^(M,N)finite_sum,&n)`
        FUBINI_MEASURE) THEN
    ASM_SIMP_TAC[MEASURABLE_LEGESGUE_MEASURABLE_INTER_MEASURABLE;
                 MEASURABLE_BALL; HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC INTEGRAL_DROP_LE_AE THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{x:real^M | ~measurable {y:real^N | pastecart x y IN s}} UNION
                {x:real^M | ~measurable {y:real^N | pastecart x y IN s INTER
                                                    ball (vec 0,&n)}}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; IN_DIFF; IN_UNIV; DE_MORGAN_THM;
                    IN_UNION; IN_ELIM_THM; LIFT_DROP] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MEASURE_SUBSET THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_INTER; IN_BALL_0; IN_UNIV] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[REAL_ARCH_LT]]);;

let FUBINI_TONELLI_MEASURE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (measurable s <=>
             negligible {y | ~measurable {x | pastecart x y IN s}} /\
             (\y. lift(measure {x | pastecart x y IN s})) integrable_on UNIV)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_TONELLI_MEASURE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LINEAR_PASTECART;
               LINEAR_FSTCART; LINEAR_SNDCART; DIMINDEX_FINITE_SUM;
               ARITH_RULE `m + n:num <= n + m`] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[measurable; measure] THEN
    ASM_REWRITE_TAC[GSYM measurable; GSYM measure] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let FUBINI_TONELLI_NEGLIGIBLE = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {x | ~negligible {y | pastecart x y IN s}})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  ASM_SIMP_TAC[FUBINI_NEGLIGIBLE] THEN DISCH_TAC THEN
  REWRITE_TAC[NEGLIGIBLE_EQ_MEASURE_0] THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[FUBINI_TONELLI_MEASURE] THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; CONTRAPOS_THM;
                  NEGLIGIBLE_IMP_MEASURABLE];
      MATCH_MP_TAC(REWRITE_RULE[IMP_IMP] INTEGRABLE_SPIKE)];
    DISCH_TAC THEN
    REWRITE_TAC[GSYM LIFT_EQ; LIFT_NUM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FUBINI_MEASURE) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          HAS_INTEGRAL_UNIQUE)) THEN
    MATCH_MP_TAC HAS_INTEGRAL_SPIKE] THEN
  EXISTS_TAC `(\x. vec 0):real^M->real^1` THEN
  EXISTS_TAC
   `{x:real^M | ~negligible {y:real^N | pastecart x y IN s}}` THEN
   ASM_REWRITE_TAC[INTEGRABLE_0; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  SIMP_TAC[MEASURE_EQ_0; GSYM DROP_EQ; DROP_VEC; LIFT_DROP; HAS_INTEGRAL_0]);;

let FUBINI_TONELLI_NEGLIGIBLE_ALT = prove
 (`!s:real^(M,N)finite_sum->bool.
        lebesgue_measurable s
        ==> (negligible s <=>
             negligible {y | ~negligible {x | pastecart x y IN s}})`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE (\z. pastecart (sndcart z) (fstcart z))
                      (s:real^(M,N)finite_sum->bool)`
        FUBINI_TONELLI_NEGLIGIBLE) THEN
  ASM_SIMP_TAC[LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN; LINEAR_PASTECART;
               LINEAR_FSTCART; LINEAR_SNDCART; DIMINDEX_FINITE_SUM;
               ARITH_RULE `m + n:num <= n + m`] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (sndcart z) (fstcart z)`
   HAS_MEASURE_ISOMETRY) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN
    SIMP_TAC[LINEAR_PASTECART; LINEAR_FSTCART; LINEAR_SNDCART] THEN
    SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC];
    DISCH_TAC THEN ASM_REWRITE_TAC[HAS_MEASURE_0] THEN
    ASM_REWRITE_TAC[GSYM HAS_MEASURE_0] THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PASTECART; FSTCART_PASTECART;
                SNDCART_PASTECART; PASTECART_INJ] THEN
    REWRITE_TAC[GSYM CONJ_ASSOC; RIGHT_EXISTS_AND_THM; UNWIND_THM1]]);;

let LEBESGUE_MEASURABLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        lebesgue_measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/
        (lebesgue_measurable s /\ lebesgue_measurable t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `negligible(s:real^M->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `negligible(t:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_LEBESGUE_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[lebesgue_measurable; measurable_on; IN_UNIV] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THENL
   [MAP_EVERY X_GEN_TAC
     [`k:real^(M,N)finite_sum->bool`;
      `g:num->real^(M,N)finite_sum->real^1`] THEN
    STRIP_TAC THEN FIRST_ASSUM(fun th ->
      ASSUME_TAC(MATCH_MP FUBINI_NEGLIGIBLE th) THEN
      ASSUME_TAC(MATCH_MP FUBINI_NEGLIGIBLE_ALT th)) THEN
    SUBGOAL_THEN
     `~(s SUBSET {x:real^M | ~negligible {y:real^N | pastecart x y IN k}})`
    MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `~(t SUBSET {y:real^N | ~negligible {x:real^M | pastecart x y IN k}})`
    MP_TAC THENL [ASM_MESON_TAC[NEGLIGIBLE_SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{x:real^M | pastecart x (y:real^N) IN k}` THEN
    EXISTS_TAC `\n x. (g:num->real^(M,N)finite_sum->real^1)
                      n (pastecart x y)` THEN
    EXISTS_TAC `{y:real^N | pastecart (x:real^M) y IN k}` THEN
    EXISTS_TAC `\n y. (g:num->real^(M,N)finite_sum->real^1)
                      n (pastecart x y)` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THEN
    (CONJ_TAC THENL
      [GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
       MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
       SIMP_TAC[CONTINUOUS_ON_PASTECART;
                CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
       ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
       ALL_TAC])
    THENL
     [X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (u:real^M) (y:real^N)`);
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `pastecart (x:real^M) (v:real^N)`)] THEN
    ASM_REWRITE_TAC[indicator; PASTECART_IN_PCROSS];
    MAP_EVERY X_GEN_TAC
     [`u:real^M->bool`; `f:num->real^M->real^1`;
      `v:real^N->bool`; `g:num->real^N->real^1`] THEN
    STRIP_TAC THEN
    EXISTS_TAC `u PCROSS (:real^N) UNION (:real^M) PCROSS v` THEN
    EXISTS_TAC `\n:num z:real^(M,N)finite_sum.
      lift(drop(f n (fstcart z)) * drop(g n (sndcart z)))` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ; NEGLIGIBLE_PCROSS] THEN
    CONJ_TAC THENL
     [GEN_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      REWRITE_TAC[o_DEF; LIFT_DROP] THEN
      CONJ_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
      REWRITE_TAC[FORALL_PASTECART; IN_UNION; PASTECART_IN_PCROSS] THEN
      REWRITE_TAC[IN_UNIV; DE_MORGAN_THM; LIFT_CMUL; LIFT_DROP] THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
      SUBGOAL_THEN `indicator (s PCROSS t) (pastecart x y) =
                    drop(indicator s (x:real^M)) % indicator t (y:real^N)`
      SUBST1_TAC THENL
       [REWRITE_TAC[indicator; PASTECART_IN_PCROSS] THEN
        MAP_EVERY ASM_CASES_TAC [`(x:real^M) IN s`; `(y:real^N) IN t`] THEN
        ASM_REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; DROP_VEC] THEN
        CONV_TAC REAL_RAT_REDUCE_CONV;
        MATCH_MP_TAC LIM_MUL THEN REWRITE_TAC[o_DEF; LIFT_DROP] THEN
        ASM_SIMP_TAC[]]]]);;

let MEASURABLE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        measurable(s PCROSS t) <=>
        negligible s \/ negligible t \/ (measurable s /\ measurable t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `negligible(s:real^M->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `negligible(t:real^N->bool)` THENL
   [ASM_MESON_TAC[NEGLIGIBLE_PCROSS; NEGLIGIBLE_IMP_MEASURABLE];
    ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC
   `lebesgue_measurable((s:real^M->bool) PCROSS (t:real^N->bool))`
  THENL
   [ASM_SIMP_TAC[FUBINI_TONELLI_MEASURE; PASTECART_IN_PCROSS];
    ASM_MESON_TAC[LEBESGUE_MEASURABLE_PCROSS;
    MEASURABLE_IMP_LEBESGUE_MEASURABLE]] THEN
  REWRITE_TAC[SET_RULE `{x | P /\ x IN s} = if P then s else {}`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[LIFT_NUM; INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[SET_RULE
   `{x | if x IN s then P else F} = if P then s else {}`] THEN
  ASM_CASES_TAC `measurable(s:real^M->bool)` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `measurable(t:real^N->bool)` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_EMPTY] THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN
  ASM_MESON_TAC[NEGLIGIBLE_EQ_MEASURE_0]);;

let HAS_MEASURE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool a b.
        s has_measure a /\ t has_measure b
        ==> (s PCROSS t) has_measure (a * b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `(s:real^M->bool) PCROSS (t:real^N->bool)`
        FUBINI_MEASURE) THEN
  REWRITE_TAC[MEASURABLE_PCROSS; PASTECART_IN_PCROSS] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `{y | P /\ y IN s} = if P then s else {}`] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[MEASURABLE_EMPTY; MEASURE_EMPTY] THEN
  ONCE_REWRITE_TAC[COND_RAND] THEN
  REWRITE_TAC[LIFT_NUM; INTEGRABLE_RESTRICT_UNIV; INTEGRABLE_ON_CONST] THEN
  REWRITE_TAC[SET_RULE
   `{x | if x IN s then P else F} = if P then s else {}`] THEN
  REWRITE_TAC[HAS_INTEGRAL_RESTRICT_UNIV] THEN STRIP_TAC THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE; MEASURABLE_PCROSS] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[measurable]; ALL_TAC] THEN
  REWRITE_TAC[GSYM LIFT_EQ] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          HAS_INTEGRAL_UNIQUE)) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_MEASURE_MEASURABLE_MEASURE]) THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_CMUL] THEN
  ASM_REWRITE_TAC[LIFT_EQ_CMUL] THEN MATCH_MP_TAC HAS_INTEGRAL_CMUL THEN
  REWRITE_TAC[GSYM LIFT_EQ_CMUL] THEN
  ONCE_REWRITE_TAC[GSYM HAS_INTEGRAL_RESTRICT_UNIV] THEN
  ASM_REWRITE_TAC[GSYM HAS_MEASURE; HAS_MEASURE_MEASURABLE_MEASURE]);;

let MEASURE_PCROSS = prove
 (`!s:real^M->bool t:real^N->bool.
        measurable s /\ measurable t
        ==> measure(s PCROSS t) = measure s * measure t`,
  MESON_TAC[HAS_MEASURE_MEASURABLE_MEASURE; HAS_MEASURE_PCROSS]);;

(* ------------------------------------------------------------------------- *)
(* Relate the measurability of a function and of its ordinate set.           *)
(* ------------------------------------------------------------------------- *)

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE = prove
 (`!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k <= (f x)$k}`,
  let lemma = prove
   (`!x y. x <= y <=> !q. rational q /\ y < q ==> x < q`,
    REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[REAL_LET_TRANS]; ALL_TAC] THEN
    ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC[REAL_NOT_LE; NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT] THEN
    MESON_TAC[RATIONAL_BETWEEN; REAL_LT_IMP_LE]) in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{pastecart (x:real^M) (y:real^N) | y$k <= (f x:real^N)$k} =
    INTERS {{pastecart x y | (f x)$k < q ==> y$k < q} | q IN rational}`
  SUBST1_TAC THENL
   [REWRITE_TAC[INTERS_GSPEC; EXTENSION; FORALL_PASTECART] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN MESON_TAC[lemma; IN];
    ALL_TAC] THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_COUNTABLE_INTERS THEN
  SIMP_TAC[SIMPLE_IMAGE; COUNTABLE_IMAGE; COUNTABLE_RATIONAL] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN ONCE_REWRITE_TAC[SET_RULE
   `{f x y | P x y ==> Q x y} = {f x y | Q x y} UNION {f x y | ~(P x y)}`] THEN
  X_GEN_TAC `q:real` THEN REWRITE_TAC[IN] THEN DISCH_TAC THEN
  MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
  REWRITE_TAC[REAL_NOT_LT; GSYM PCROSS; LEBESGUE_MEASURABLE_PCROSS;
   SET_RULE `{f x y |x,y| P x} = {f x y | x IN {x | P x} /\ y IN UNIV}`;
   SET_RULE `{f x y |x,y| Q y} = {f x y | x IN UNIV /\ y IN {x | Q x}}`] THEN
  CONJ_TAC THEN REPEAT DISJ2_TAC THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THENL
   [MATCH_MP_TAC LEBESGUE_MEASURABLE_OPEN THEN
    REWRITE_TAC[drop; OPEN_HALFSPACE_COMPONENT_LT];
    ONCE_REWRITE_TAC[SET_RULE
     `{x | q <= (f x)$k} = {x | f x IN {y | q <= y$k}}`] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_PREIMAGE_CLOSED THEN
    ASM_REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT = prove
 (`!f:real^M->real^N k.
        f measurable_on (:real^M)
        ==> lebesgue_measurable {pastecart x (y:real^N) | y$k < (f x)$k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[REAL_ARITH `f < y <=> ~(--f <= --y)`] THEN
  MP_TAC(ISPECL [`(--) o (f:real^M->real^N)`; `k:num`]
    LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MEASURABLE_ON_COMPOSE_CONTINUOUS THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM ETA_AX] THEN
    SIMP_TAC[CONTINUOUS_ON_NEG; CONTINUOUS_ON_ID];
    ALL_TAC] THEN
  MP_TAC(ISPEC
   `\z:real^(M,N)finite_sum. pastecart (fstcart z) (--sndcart z)`
   LEBESGUE_MEASURABLE_LINEAR_IMAGE_EQ) THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM; PASTECART_INJ; VECTOR_EQ_NEG2;
              GSYM PASTECART_EQ] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[linear; PASTECART_EQ; FSTCART_PASTECART; SNDCART_PASTECART;
                FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [GSYM th])] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM LEBESGUE_MEASURABLE_COMPL] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `UNIV DIFF s = t <=> s = UNIV DIFF t`] THEN
  MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_ELIM_PASTECART_THM; o_DEF;
              FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; REAL_NEG_NEG] THEN
  MESON_TAC[FSTCART_PASTECART; SNDCART_PASTECART; VECTOR_NEG_NEG]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE_EQ,
    LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LE_EQ = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k <= (f x)$k}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k <= (f x)$k})`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE];
    SUBGOAL_THEN
     `{ pastecart x y |
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> (y:real^N)$k <= (f:real^M->real^N) x$k } =
      INTERS {{ pastecart x y | (y:real^N)$k <= (f:real^M->real^N) x$k} |
                k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_INJ] THEN MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_NUMSEG]];
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `{y | lebesgue_measurable
              {x | !k. 1 <= k /\ k <= dimindex (:N)
                       ==> (y:real^N)$k <= (f:real^M->real^N) x$k}}`]
     MEASURABLE_ON_PREIMAGE_ORTHANT_GE_DENSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_ge] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_LEBESGUE_MEASURABLE_ALT) THEN
    REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV DIFF s = {}`] THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; NEGLIGIBLE_EMPTY_INTERIOR]]);;

let LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT_EQ,
    LEBESGUE_MEASURABLE_FUNCTION_ORTHANT_SET_LT_EQ = (CONJ_PAIR o prove)
 (`(!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> lebesgue_measurable
                  {pastecart x (y:real^N) | y$k < (f x)$k}) /\
   (!f:real^M->real^N.
        f measurable_on (:real^M) <=>
        lebesgue_measurable
          {pastecart x (y:real^N) | !k. 1 <= k /\ k <= dimindex(:N)
                                        ==> y$k < (f x)$k})`,
  REWRITE_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> q) /\ (q ==> r) /\ (r ==> p)
    ==> (p <=> q) /\ (p <=> r)`) THEN
  REPEAT CONJ_TAC THEN DISCH_TAC THENL
   [ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT];
    SUBGOAL_THEN
     `{ pastecart x y |
        !k. 1 <= k /\ k <= dimindex(:N)
            ==> (y:real^N)$k < (f:real^M->real^N) x$k } =
      INTERS {{ pastecart x y | (y:real^N)$k < (f:real^M->real^N) x$k} |
                k IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[INTERS_GSPEC; EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_INJ] THEN MESON_TAC[];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
      SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
      ASM_SIMP_TAC[FORALL_IN_IMAGE; IN_NUMSEG]];
    MP_TAC(ISPECL
     [`f:real^M->real^N`;
      `{y | lebesgue_measurable
              {x | !k. 1 <= k /\ k <= dimindex (:N)
                       ==> (y:real^N)$k < (f:real^M->real^N) x$k}}`]
     MEASURABLE_ON_PREIMAGE_ORTHANT_GT_DENSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; real_gt] THEN DISCH_THEN MATCH_MP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_LEBESGUE_MEASURABLE_ALT) THEN
    REWRITE_TAC[SET_RULE `{x | ~P x} = UNIV DIFF {x | P x}`] THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM] THEN
    REWRITE_TAC[SET_RULE `s = UNIV <=> UNIV DIFF s = {}`] THEN
    REWRITE_TAC[GSYM INTERIOR_COMPLEMENT; NEGLIGIBLE_EMPTY_INTERIOR]]);;

let NEGLIGIBLE_MEASURABLE_FUNCTION_GRAPH = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M) ==> negligible {pastecart x y | f x = y}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC NEGLIGIBLE_DISJOINT_TRANSLATES THEN
  EXISTS_TAC `{pastecart (vec 0:real^M) x | x IN (:real^N)}` THEN
  EXISTS_TAC `vec 0:real^(M,N)finite_sum` THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `{pastecart x y | (f:real^M->real^N) x = y} =
      INTERS {{pastecart x y | y$i <= (f x)$i} DIFF
              {pastecart x y | y$i < (f x)$i} | i IN 1..dimindex(:N)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[CART_EQ; INTERS_GSPEC; EXTENSION; FORALL_PASTECART] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_NUMSEG] THEN
      ONCE_REWRITE_TAC[IN_ELIM_THM] THEN
      REWRITE_TAC[IN_ELIM_PASTECART_THM; IN_DIFF; REAL_NOT_LT] THEN
      REWRITE_TAC[REAL_LE_ANTISYM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_INTERS THEN
    SIMP_TAC[FINITE_IMAGE; SIMPLE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
    STRIP_TAC THEN MATCH_MP_TAC LEBESGUE_MEASURABLE_DIFF THEN
    ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE;
                 LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LT];
    MATCH_MP_TAC CONNECTED_IMP_PERFECT THEN
    REWRITE_TAC[GSYM PCROSS; SET_RULE
     `{f a x | x IN s} = {f w x | w IN {a} /\ x IN s}`] THEN
    REWRITE_TAC[GSYM PASTECART_VEC; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[CONNECTED_SING; CONNECTED_PCROSS_EQ; CONNECTED_UNIV] THEN
    REWRITE_TAC[IN_SING; IN_UNIV] THEN MATCH_MP_TAC(SET_RULE
     `!a b. a IN s /\ b IN s /\ ~(a = b) ==> ~(?a. s = {a})`) THEN
    EXISTS_TAC `pastecart (vec 0:real^M) (vec 0:real^N)` THEN
    EXISTS_TAC `pastecart (vec 0:real^M) (vec 1:real^N)` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_SING; IN_UNIV] THEN
    REWRITE_TAC[PASTECART_INJ; VEC_EQ; ARITH_EQ];

    REWRITE_TAC[pairwise; IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; PASTECART_INJ] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_UNIV; PASTECART_INJ; FORALL_IN_IMAGE;
      SET_RULE `DISJOINT s t <=> !x. x IN s ==> !y. y IN t ==> ~(x = y)`] THEN
    REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; PASTECART_INJ] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^N`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`x':real^M`; `y':real^N`] THEN DISCH_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM)) THEN
    ASM_CASES_TAC `x':real^M = x` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[CONTRAPOS_THM] THEN
    CONV_TAC VECTOR_ARITH]);;

(* ------------------------------------------------------------------------- *)
(* Hence relate integrals and "area under curve" for functions into R^+.     *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_IFF_LEBESGUE_MEASURABLE_UNDER_CURVE = prove
 (`!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f measurable_on (:real^N) <=>
             lebesgue_measurable { pastecart x y | y IN interval[vec 0,f x]})`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE_EQ] THEN
  REWRITE_TAC[DIMINDEX_1; FORALL_1; IN_INTERVAL_1; GSYM drop; DROP_VEC] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN
     `{pastecart x y | &0 <= drop y /\ drop y <= drop (f x)} =
      (:real^N) PCROSS {y | &0 <= drop y} INTER
      {pastecart (x:real^N) y | drop y <= drop (f x)}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_INTER; IN_ELIM_PASTECART_THM] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_CLOSED; GSYM real_ge; drop;
               CLOSED_HALFSPACE_COMPONENT_GE]];
    SUBGOAL_THEN
     `{pastecart (x:real^N) y | drop y <= drop (f x)} =
      {pastecart x y | &0 <= drop y /\ drop y <= drop (f x)} UNION
       (:real^N) PCROSS {y | drop y < &0}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNION; IN_ELIM_PASTECART_THM] THEN
      REWRITE_TAC[IN_UNIV; IN_ELIM_THM] THEN
      ASM_MESON_TAC[REAL_NOT_LE; REAL_LT_IMP_LE; REAL_LE_TRANS];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_UNION THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
      SIMP_TAC[LEBESGUE_MEASURABLE_OPEN; drop;
               OPEN_HALFSPACE_COMPONENT_LT]]]);;

let INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE = prove
 (`!f:real^N->real^1.
        (!x. &0 <= drop(f x))
        ==> (f integrable_on (:real^N) <=>
             measurable { pastecart x y | y IN interval[vec 0,f x]})`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) FUBINI_TONELLI_MEASURE o snd) THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
    REWRITE_TAC[MEASURABLE_INTERVAL; EMPTY_GSPEC; NEGLIGIBLE_EMPTY] THEN
    ASM_REWRITE_TAC[ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    SUBGOAL_THEN
     `{pastecart x y | y IN interval [vec 0,f x]} =
      {pastecart x y | drop y <= drop(f x)} INTER
      (:real^N) PCROSS {x | &0 <= drop x}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_INTER; IN_ELIM_PASTECART_THM;
                  PASTECART_IN_PCROSS; IN_UNIV] THEN
      REWRITE_TAC[IN_INTERVAL_1; IN_ELIM_THM; DROP_VEC; CONJ_SYM];
      MATCH_MP_TAC LEBESGUE_MEASURABLE_INTER THEN REWRITE_TAC[drop] THEN
      ASM_SIMP_TAC[LEBESGUE_MEASURABLE_FUNCTION_ORDINATE_SET_LE;
                   INTEGRABLE_IMP_MEASURABLE; LEBESGUE_MEASURABLE_PCROSS] THEN
      REPEAT DISJ2_TAC THEN REWRITE_TAC[LEBESGUE_MEASURABLE_UNIV] THEN
      MATCH_MP_TAC LEBESGUE_MEASURABLE_CLOSED THEN
      REWRITE_TAC[drop; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE]];
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
    REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
    ASM_SIMP_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
    REWRITE_TAC[ETA_AX; GSYM LIFT_EQ] THEN MESON_TAC[integrable_on]]);;

let HAS_INTEGRAL_MEASURE_UNDER_CURVE = prove
 (`!f:real^N->real^1 m.
        (!x. &0 <= drop(f x))
        ==> ((f has_integral lift m) (:real^N) <=>
             { pastecart x y | y IN interval[vec 0,f x]} has_measure m)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE;
              HAS_INTEGRAL_INTEGRABLE_INTEGRAL] THEN
  MATCH_MP_TAC(TAUT
   `(p <=> p') /\ (p /\ p' ==> (q <=> q')) ==> (p /\ q <=> p' /\ q')`) THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
  REWRITE_TAC[IN_ELIM_PASTECART_THM; SET_RULE `{x | x IN s} = s`] THEN
  ASM_REWRITE_TAC[MEASURE_INTERVAL_1; DROP_VEC; REAL_SUB_RZERO; LIFT_DROP] THEN
  REWRITE_TAC[ETA_AX; GSYM LIFT_EQ] THEN
  ASM_MESON_TAC[integrable_on; INTEGRAL_UNIQUE]);;

(* ------------------------------------------------------------------------- *)
(* Some miscellanous lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let MEASURABLE_ON_COMPOSE_FSTCART = prove
 (`!f:real^M->real^P.
        f measurable_on (:real^M)
        ==> (\z:real^(M,N)finite_sum. f(fstcart z)) measurable_on
            (:real^(M,N)finite_sum)`,
  GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`k:real^M->bool`; `g:num->real^M->real^P`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(k:real^M->bool) PCROSS (:real^N)` THEN
  EXISTS_TAC `(\n z. g n (fstcart z)):num->real^(M,N)finite_sum->real^P` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNIV; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_FSTCART; LINEAR_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MEASURABLE_ON_COMPOSE_SNDCART = prove
 (`!f:real^N->real^P.
        f measurable_on (:real^N)
        ==> (\z:real^(M,N)finite_sum. f(sndcart z)) measurable_on
            (:real^(M,N)finite_sum)`,
  GEN_TAC THEN REWRITE_TAC[measurable_on; LEFT_IMP_EXISTS_THM; IN_UNIV] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `g:num->real^N->real^P`] THEN
  STRIP_TAC THEN
  EXISTS_TAC `(:real^M) PCROSS (k:real^N->bool)` THEN
  EXISTS_TAC `(\n z. g n (sndcart z)):num->real^(M,N)finite_sum->real^P` THEN
  ASM_REWRITE_TAC[NEGLIGIBLE_PCROSS; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  IN_UNIV; SNDCART_PASTECART; SNDCART_PASTECART] THEN
  GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
  MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
  SIMP_TAC[LINEAR_SNDCART; LINEAR_CONTINUOUS_ON] THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

let MEASURABLE_ON_COMPOSE_SUB = prove
 (`!f:real^M->real^N.
        f measurable_on (:real^M)
        ==> (\z. f(fstcart z - sndcart z))
            measurable_on (:real^(M,M)finite_sum)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(\z. f(fstcart z - sndcart z)):real^(M,M)finite_sum->real^N =
    (\z. f(fstcart z)) o
    (\z. pastecart (fstcart z - sndcart z) (sndcart z))`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; I_THM] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART];
    W(MP_TAC o PART_MATCH (lhs o rand) MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN o
      snd)] THEN
  REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART] THEN
  ANTS_TAC THENL
   [REWRITE_TAC[PASTECART_INJ] THEN
    CONJ_TAC THENL [MATCH_MP_TAC LINEAR_PASTECART; CONV_TAC VECTOR_ARITH] THEN
    SIMP_TAC[LINEAR_SNDCART; LINEAR_FSTCART; LINEAR_COMPOSE_SUB];
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
    EXISTS_TAC `(:real^(M,M)finite_sum)` THEN
    ASM_SIMP_TAC[MEASURABLE_ON_COMPOSE_FSTCART; SUBSET_UNIV] THEN
    MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
    REWRITE_TAC[LE_REFL; LEBESGUE_MEASURABLE_UNIV] THEN
    MATCH_MP_TAC LINEAR_PASTECART THEN
    SIMP_TAC[LINEAR_SNDCART; LINEAR_FSTCART; LINEAR_COMPOSE_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Fubini for absolute integrability.                                        *)
(* ------------------------------------------------------------------------- *)

let FUBINI_ABSOLUTELY_INTEGRABLE = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {x | ~((\y. f(pastecart x y))
                     absolutely_integrable_on (:real^N))} /\
            ((\x. integral (:real^N) (\y. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^M)`,
  let lemma = prove
   (`{x | ~(!i. i IN k ==> P i x)} = UNIONS {{x | ~P i x} | i IN k}`,
    REWRITE_TAC[UNIONS_GSPEC] THEN SET_TAC[]) in
  let assoclemma = prove
   (`!P:real^(M,N)finite_sum->real^P->bool.
          {pastecart x y | P x y} has_measure m
          ==> {pastecart x (pastecart y z) | P (pastecart x y) z}
              has_measure m`,
    GEN_TAC THEN MP_TAC(ISPECL
     [`\z. pastecart (fstcart(fstcart z):real^M)
                     (pastecart (sndcart(fstcart z):real^N)
                                (sndcart z:real^P))`;
      `{pastecart (x:real^(M,N)finite_sum) (y:real^P) | P x y}`;
      `m:real`] HAS_MEASURE_ISOMETRY) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_AC] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [REPEAT(MATCH_MP_TAC LINEAR_PASTECART THEN CONJ_TAC) THEN
        REWRITE_TAC[GSYM o_DEF] THEN
        REPEAT(MATCH_MP_TAC LINEAR_COMPOSE THEN CONJ_TAC) THEN
        REWRITE_TAC[LINEAR_FSTCART; LINEAR_SNDCART];
        SIMP_TAC[FORALL_PASTECART; NORM_EQ; GSYM NORM_POW_2; SQNORM_PASTECART;
                 FSTCART_PASTECART; SNDCART_PASTECART; REAL_ADD_AC]];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC EQ_IMP THEN
      AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
      REWRITE_TAC[FORALL_PASTECART; FSTCART_PASTECART; SNDCART_PASTECART;
                  IN_ELIM_THM; EXISTS_PASTECART; PASTECART_INJ] THEN
      MESON_TAC[]]) in
  let FUBINI_LEMMA = prove
   (`!f:real^(M,N)finite_sum->real^1.
          f integrable_on (:real^(M,N)finite_sum) /\ (!x. &0 <= drop(f x))
          ==> negligible {x | ~((f o pastecart x) integrable_on (:real^N))} /\
              ((\x. integral (:real^N) (f o pastecart x)) has_integral
               integral (:real^(M,N)finite_sum) f) (:real^M)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPEC `f:real^(M,N)finite_sum->real^1`
      INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `measurable { pastecart x (pastecart y z) |
                   z IN interval[vec 0,(f:real^(M,N)finite_sum->real^1)
                                       (pastecart x y)] }`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [measurable]) THEN
      REWRITE_TAC[measurable] THEN MATCH_MP_TAC MONO_EXISTS THEN
      REWRITE_TAC[assoclemma];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FUBINI_MEASURE) THEN
    REWRITE_TAC[IN_ELIM_THM; PASTECART_INJ] THEN
    ONCE_REWRITE_TAC[TAUT `p /\ q /\ r <=> q /\ p /\ r`] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; UNWIND_THM1] THEN
    REWRITE_TAC[SET_RULE
     `{x | ?y z. P y z /\ x = pastecart y z} =
      {pastecart y z | P y z}`] THEN
    MP_TAC(GEN `x:real^M` (ISPEC
       `(f:real^(M,N)finite_sum->real^1) o pastecart x`
          INTEGRABLE_IFF_MEASURABLE_UNDER_CURVE)) THEN
    ASM_REWRITE_TAC[o_DEF] THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `y = z /\ ((f has_integral y) s ==> (g has_integral y) s)
      ==> (f has_integral y) s ==> (g has_integral z) s`) THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_MEASURE_UNDER_CURVE] THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MEASURE_UNIQUE THEN
      MATCH_MP_TAC assoclemma THEN
      ASM_REWRITE_TAC[HAS_MEASURE_MEASURABLE_MEASURE];
      MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ]
          (REWRITE_RULE[CONJ_ASSOC] HAS_INTEGRAL_SPIKE)) THEN
      EXISTS_TAC
       `{x | ~((\y. (f:real^(M,N)finite_sum->real^1) (pastecart x y))
               integrable_on (:real^N))}` THEN
      ASM_REWRITE_TAC[IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_UNIQUE THEN
      ASM_SIMP_TAC[HAS_INTEGRAL_MEASURE_UNDER_CURVE] THEN
      ASM_SIMP_TAC[GSYM HAS_MEASURE_MEASURE]]) in
  let FUBINI_1 = prove
   (`!f:real^(M,N)finite_sum->real^1.
          f absolutely_integrable_on (:real^(M,N)finite_sum)
          ==> negligible
               {x | ~((f o pastecart x) absolutely_integrable_on (:real^N))} /\
              ((\x. integral (:real^N) (f o pastecart x)) has_integral
               integral (:real^(M,N)finite_sum) f) (:real^M)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY ABBREV_TAC
     [`g = \x:real^(M,N)finite_sum. lift (max (&0) (drop(f x)))`;
      `h = \x:real^(M,N)finite_sum. --(lift (min (&0) (drop(f x))))`] THEN
    SUBGOAL_THEN `!x:real^(M,N)finite_sum. &0 <= drop(g x) /\ &0 <= drop(h x)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN
      REWRITE_TAC[DROP_NEG; LIFT_DROP] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(g:real^(M,N)finite_sum->real^1) absolutely_integrable_on UNIV /\
      (h:real^(M,N)finite_sum->real^1) absolutely_integrable_on UNIV`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN REWRITE_TAC[] THEN CONJ_TAC THEN
      TRY(MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NEG) THENL
       [MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MAX_1;
        MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_MIN_1] THEN
      ASM_REWRITE_TAC[LIFT_DROP; ETA_AX; LIFT_NUM] THEN
      REWRITE_TAC[ABSOLUTELY_INTEGRABLE_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^(M,N)finite_sum->real^1) = \x. g x - h x`
    SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["g"; "h"] THEN
      REWRITE_TAC[FUN_EQ_THM; GSYM DROP_EQ; LIFT_DROP; DROP_SUB; DROP_NEG] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `h:real^(M,N)finite_sum->real^1` FUBINI_LEMMA) THEN
    MP_TAC(ISPEC `g:real^(M,N)finite_sum->real^1` FUBINI_LEMMA) THEN
    ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
    ONCE_REWRITE_TAC[TAUT
     `p /\ q ==> r /\ s ==> t <=> p /\ r ==> q /\ s ==> t`] THEN
    REWRITE_TAC[GSYM NEGLIGIBLE_UNION_EQ; o_DEF] THEN DISCH_TAC THEN
    DISCH_THEN(ASSUME_TAC o MATCH_MP HAS_INTEGRAL_SUB) THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
          NEGLIGIBLE_SUBSET)) THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; GSYM DE_MORGAN_THM] THEN
      REWRITE_TAC[CONTRAPOS_THM; o_DEF] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_SUB THEN
      CONJ_TAC THEN MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
      ASM_REWRITE_TAC[DIMINDEX_1; FORALL_1; GSYM drop; IN_UNIV];
      ASM_SIMP_TAC[INTEGRAL_SUB; ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[IMP_CONJ_ALT]
       (REWRITE_RULE[CONJ_ASSOC] HAS_INTEGRAL_SPIKE))) THEN
      FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
          CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; IN_ELIM_THM] THEN
      SIMP_TAC[DE_MORGAN_THM; INTEGRAL_SUB]]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_COMPONENTWISE] THEN
    REWRITE_TAC[GSYM IN_NUMSEG; lemma] THEN
    MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN
    SIMP_TAC[SIMPLE_IMAGE; FINITE_IMAGE; FINITE_NUMSEG] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_NUMSEG];
    DISCH_TAC THEN
    ONCE_REWRITE_TAC[HAS_INTEGRAL_COMPONENTWISE]] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
    [ABSOLUTELY_INTEGRABLE_COMPONENTWISE]) THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_1) THEN SIMP_TAC[o_DEF] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE] THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE[IMP_CONJ] (REWRITE_RULE[CONJ_ASSOC]
        HAS_INTEGRAL_SPIKE)) THEN
  FIRST_ASSUM(fun th -> EXISTS_TAC(rand(concl th)) THEN
    CONJ_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  REWRITE_TAC[IN_UNIV; IN_DIFF; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[LIFT_INTEGRAL_COMPONENT;
               ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE]);;

let FUBINI_ABSOLUTELY_INTEGRABLE_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on (:real^(M,N)finite_sum)
        ==> negligible
             {y | ~((\x. f(pastecart x y))
                     absolutely_integrable_on (:real^M))} /\
            ((\y. integral (:real^M) (\x. f(pastecart x y))) has_integral
             integral (:real^(M,N)finite_sum) f) (:real^N)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I
   [GSYM ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV]) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  REWRITE_TAC[INTEGRAL_PASTECART_SYM_UNIV]);;

let FUBINI_INTEGRAL = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\x. integral UNIV (\y. f(pastecart x y)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC);;

let FUBINI_INTEGRAL_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
        f absolutely_integrable_on UNIV
        ==> integral UNIV f =
            integral UNIV (\y. integral UNIV (\x. f(pastecart x y)))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
    (MP_TAC o CONJUNCT2 o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE_ALT) THEN
  DISCH_THEN(SUBST1_TAC o MATCH_MP INTEGRAL_UNIQUE) THEN REFL_TAC);;

let FUBINI_INTEGRAL_INTERVAL = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_INTEGRAL) THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; GSYM PCROSS_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_0] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]);;

let FUBINI_INTEGRAL_INTERVAL_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f absolutely_integrable_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[c,d])
                     (\y. integral (interval[a,b])
                                   (\x. f(pastecart x y)))`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM ABSOLUTELY_INTEGRABLE_RESTRICT_UNIV] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FUBINI_INTEGRAL_ALT) THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV] THEN DISCH_THEN SUBST1_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM INTEGRAL_RESTRICT_UNIV] THEN
  AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
  REWRITE_TAC[PASTECART_IN_PCROSS; GSYM PCROSS_INTERVAL] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[INTEGRAL_0] THEN
  REWRITE_TAC[INTEGRAL_RESTRICT_UNIV]);;

let INTEGRAL_PASTECART_CONTINUOUS = prove
 (`!f:real^(M,N)finite_sum->real^P a b c d.
        f continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[pastecart a c,pastecart b d]) f =
            integral (interval[a,b])
                     (\x. integral (interval[c,d])
                                   (\y. f(pastecart x y)))`,
  SIMP_TAC[FUBINI_INTEGRAL_INTERVAL; ABSOLUTELY_INTEGRABLE_CONTINUOUS]);;

let INTEGRAL_SWAP_CONTINUOUS = prove
 (`!f:real^M->real^N->real^P a b c d.
        (\z. f (fstcart z) (sndcart z))
        continuous_on interval[pastecart a c,pastecart b d]
        ==> integral (interval[a,b]) (\x. integral (interval[c,d]) (f x)) =
            integral (interval[c,d])
                     (\y. integral (interval[a,b]) (\x. f x y))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_CONTINUOUS) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP FUBINI_INTEGRAL_INTERVAL_ALT th) THEN
    MP_TAC(MATCH_MP FUBINI_INTEGRAL_INTERVAL th)) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ETA_AX]);;

let FUBINI_TONELLI = prove
 (`!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {x | ~((\y. f(pastecart x y)) absolutely_integrable_on (:real^N))} /\
        (\x. integral (:real^N) (\y. lift(norm(f(pastecart x y)))))
        integrable_on (:real^M))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN STRIP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP ABSOLUTELY_INTEGRABLE_NORM) THEN
    DISCH_THEN(MP_TAC o MATCH_MP FUBINI_ABSOLUTELY_INTEGRABLE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(ACCEPT_TAC o MATCH_MP HAS_INTEGRAL_INTEGRABLE);
    ALL_TAC] THEN
  ASM_REWRITE_TAC[ABSOLUTELY_INTEGRABLE_MEASURABLE] THEN ABBREV_TAC
    `g = \n x. if x IN interval[--vec n,vec n]
               then lift(min (norm ((f:real^(M,N)finite_sum->real^P) x)) (&n))
               else vec 0` THEN
  SUBGOAL_THEN
   `!n. (g:num->real^(M,N)finite_sum->real^1) n absolutely_integrable_on UNIV`
  ASSUME_TAC THENL
   [X_GEN_TAC `n:num` THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE THEN
    REWRITE_TAC[IN_UNIV; DIMINDEX_1; FORALL_1] THEN
    REWRITE_TAC[COND_RAND; COND_RATOR; GSYM drop; LIFT_DROP; DROP_VEC] THEN
    CONJ_TAC THENL [CONV_TAC NORM_ARITH; ALL_TAC] THEN
    MATCH_MP_TAC INTEGRABLE_CASES THEN
    REWRITE_TAC[INTEGRABLE_0; IN_UNIV; SET_RULE `{x | x IN s} = s`] THEN
    MATCH_MP_TAC MEASURABLE_BOUNDED_BY_INTEGRABLE_IMP_INTEGRABLE THEN
    EXISTS_TAC `\x:real^(M,N)finite_sum. lift(&n)` THEN
    REWRITE_TAC[INTEGRABLE_CONST; NORM_LIFT; LIFT_DROP] THEN
    SIMP_TAC[NORM_POS_LE; REAL_ARITH `&0 <= x ==> abs(min x (&n)) <= &n`] THEN
    MP_TAC(ISPECL
     [`\x. lift(norm((f:real^(M,N)finite_sum->real^P) x))`;
      `\x:real^(M,N)finite_sum. lift(&n)`;
      `interval[--vec n:real^(M,N)finite_sum,vec n]`] MEASURABLE_ON_MIN) THEN
    ANTS_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MEASURABLE_ON_LEBESGUE_MEASURABLE_SUBSET THEN
      EXISTS_TAC `(:real^(M,N)finite_sum)` THEN
      REWRITE_TAC[SUBSET_UNIV; LEBESGUE_MEASURABLE_INTERVAL] THEN
      ASM_SIMP_TAC[MEASURABLE_ON_NORM; MEASURABLE_ON_CONST];
      MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      SIMP_TAC[FUN_EQ_THM; CART_EQ; LAMBDA_BETA] THEN
      REWRITE_TAC[DIMINDEX_1; LIFT_DROP; FORALL_1; GSYM drop]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`g:num->real^(M,N)finite_sum->real^1`;
    `\x. lift(norm((f:real^(M,N)finite_sum->real^P) x))`;
    `(:real^(M,N)finite_sum)`]
   MONOTONE_CONVERGENCE_INCREASING) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE; IN_UNIV] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN EXPAND_TAC "g" THEN REWRITE_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[LIFT_DROP]) THEN
    REWRITE_TAC[REAL_LE_REFL; DROP_VEC; GSYM REAL_OF_NUM_SUC] THEN
    TRY(CONV_TAC NORM_ARITH) THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
     (TAUT `~p ==> p ==> q`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `x IN s ==> s SUBSET t ==> x IN t`)) THEN
    REWRITE_TAC[SUBSET_INTERVAL; VEC_COMPONENT; VECTOR_NEG_COMPONENT] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_SUC] THEN REPEAT STRIP_TAC THEN
    REAL_ARITH_TAC;
    X_GEN_TAC `z:real^(M,N)finite_sum` THEN
    MATCH_MP_TAC LIM_EVENTUALLY THEN
    MP_TAC(ISPEC `&1 + max (norm z) (norm((f:real^(M,N)finite_sum->real^P) z))`
        REAL_ARCH_SIMPLE) THEN
    REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN DISCH_TAC THEN X_GEN_TAC `n:num` THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    EXPAND_TAC "g" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [AP_TERM_TAC THEN REWRITE_TAC[REAL_ARITH `min a b = a <=> a <= b`] THEN
      ASM_REAL_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (TAUT `~p ==> p ==> q`)) THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
      REWRITE_TAC[GSYM REAL_ABS_BOUNDS] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(REAL_ARITH
       `abs(x$i) <= norm(x:real^N) /\ norm x <= a ==> abs(x$i) <= a`) THEN
      REWRITE_TAC[COMPONENT_LE_NORM] THEN ASM_REAL_ARITH_TAC];
    MP_TAC(GEN `n:num` (ISPEC `(g:num->real^(M,N)finite_sum->real^1) n`
      FUBINI_ABSOLUTELY_INTEGRABLE)) THEN
    ASM_REWRITE_TAC[FORALL_AND_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(fun th ->
     REWRITE_TAC[GSYM(MATCH_MP INTEGRAL_UNIQUE (SPEC `n:num` th))]) THEN
    REWRITE_TAC[bounded; FORALL_IN_GSPEC] THEN
    EXISTS_TAC
     `drop(integral (:real^M)
            (\x. lift(norm(integral (:real^N)
              (\y. lift(norm(
                (f:real^(M,N)finite_sum->real^P) (pastecart x y))))))))` THEN
    X_GEN_TAC `n:num` THEN
    MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL_AE THEN
    EXISTS_TAC
     `{x | ~((\y. (f:real^(M,N)finite_sum->real^P)(pastecart x y))
             absolutely_integrable_on (:real^N))} UNION
      {x | ~((\y. (g:num->real^(M,N)finite_sum->real^1) n (pastecart x y))
             absolutely_integrable_on (:real^N))}` THEN
    ASM_REWRITE_TAC[NEGLIGIBLE_UNION_EQ] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[integrable_on];
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_IMP_INTEGRABLE THEN
      MATCH_MP_TAC ABSOLUTELY_INTEGRABLE_NORM THEN
      MATCH_MP_TAC NONNEGATIVE_ABSOLUTELY_INTEGRABLE_AE THEN
      EXISTS_TAC
       `{x | ~((\y. (f:real^(M,N)finite_sum->real^P)(pastecart x y))
             absolutely_integrable_on (:real^N))}` THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
      REWRITE_TAC[IMP_IMP; DIMINDEX_1; FORALL_1; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[absolutely_integrable_on; GSYM drop] THEN
      STRIP_TAC THEN MATCH_MP_TAC INTEGRAL_DROP_POS THEN
      ASM_REWRITE_TAC[LIFT_DROP; NORM_POS_LE];
      X_GEN_TAC `x:real^M` THEN
      REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNION; IN_ELIM_THM; DE_MORGAN_THM] THEN
      STRIP_TAC THEN REWRITE_TAC[LIFT_DROP] THEN
      MATCH_MP_TAC(REAL_ARITH
        `drop a <= norm a /\ x <= drop a==> x <= norm a`) THEN CONJ_TAC
      THENL [REWRITE_TAC[drop; NORM_REAL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC INTEGRAL_NORM_BOUND_INTEGRAL THEN
      RULE_ASSUM_TAC(REWRITE_RULE[absolutely_integrable_on]) THEN
      ASM_REWRITE_TAC[LIFT_DROP; REAL_LE_REFL; IN_UNIV] THEN
      X_GEN_TAC `y:real^N` THEN EXPAND_TAC "g" THEN
      COND_CASES_TAC THEN REWRITE_TAC[NORM_0; NORM_POS_LE] THEN
      REWRITE_TAC[NORM_LIFT] THEN CONV_TAC NORM_ARITH]]);;

let FUBINI_TONELLI_ALT = prove
 (`!f:real^(M,N)finite_sum->real^P.
   f measurable_on (:real^(M,N)finite_sum)
   ==> (f absolutely_integrable_on (:real^(M,N)finite_sum) <=>
        negligible
          {y | ~((\x. f(pastecart x y)) absolutely_integrable_on (:real^M))} /\
        (\y. integral (:real^M) (\x. lift(norm(f(pastecart x y)))))
        integrable_on (:real^N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC
   `(f:real^(M,N)finite_sum->real^P) o (\z. pastecart (sndcart z) (fstcart z))`
   FUBINI_TONELLI) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) MEASURABLE_ON_LINEAR_IMAGE_EQ_GEN o
        snd) THEN
    ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; ADD_SYM] THEN ANTS_TAC THENL
     [SIMP_TAC[linear; FORALL_PASTECART; FSTCART_PASTECART;
               SNDCART_PASTECART; PASTECART_INJ;
               FSTCART_ADD; SNDCART_ADD; FSTCART_CMUL; SNDCART_CMUL] THEN
      REWRITE_TAC[GSYM PASTECART_ADD; GSYM PASTECART_CMUL];
      DISCH_THEN SUBST1_TAC THEN POP_ASSUM MP_TAC THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN REWRITE_TAC[IN_UNIV] THEN
      REWRITE_TAC[EXISTS_PASTECART; FORALL_PASTECART] THEN
      REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN MESON_TAC[]];
    REWRITE_TAC[ABSOLUTELY_INTEGRABLE_PASTECART_SYM_UNIV; o_DEF;
                FSTCART_PASTECART; SNDCART_PASTECART]]);;

(* ------------------------------------------------------------------------- *)
(* Some versions of Fubini where we stay in a fixed space R^n.               *)
(* ------------------------------------------------------------------------- *)

let FUBINI_NEGLIGIBLE_REPLACEMENTS = prove
 (`!k s:real^N->bool.
    lebesgue_measurable s
    ==> (negligible s <=>
         negligible { lift a |
                      ~negligible { x:real^N |
                                (lambda i. if i = k then a else x$i) IN s}})`,
  let lemma0 = prove
   (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> linear((\x. lambda k. x$swap(i,j)k):real^N->real^N)`,
    SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA]) in
  let lemma1 = prove
   (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> ((\x. lambda k. x$swap(i,j)k):real^N->real^N) o
               ((\x. lambda k. x$swap(i,j)k):real^N->real^N) = I`,
    SIMP_TAC[CART_EQ; FUN_EQ_THM; o_THM; I_THM; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA])) in
  let lemma2 = prove
   (`!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (negligible
                   (IMAGE ((\x. lambda k. x$swap(i,j)k):real^N->real^N) s) <=>
                  negligible s)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_EQ THEN
    ASM_SIMP_TAC[lemma0] THEN
    MATCH_MP_TAC(MESON[] `(!x. n(n x) = x) ==> !x y. n x = n y ==> x = y`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[o_DEF; FUN_EQ_THM; I_DEF] lemma1]) in
  let lemma3 = prove
   (`!s. negligible s <=> negligible(s PCROSS (:real^1))`,
    REWRITE_TAC[NEGLIGIBLE_PCROSS; NOT_NEGLIGIBLE_UNIV]) in
  let lemma4 = prove
   (`!s:real^(N,1)finite_sum->bool.
      lebesgue_measurable s
      ==> (negligible s <=>
           negligible {lift a |
                        ~negligible { x:real^(N,1)finite_sum |
                                  (lambda i. if i = dimindex(:N) + 1 then a
                                             else x$i) IN s}})`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FUBINI_TONELLI_NEGLIGIBLE_ALT) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; X_GEN_TAC `y:real`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [lemma3] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^1`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; pastecart; DIMINDEX_FINITE_SUM;
             DIMINDEX_1; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `i = dimindex(:N) + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(n + 1 <= n) /\ (n + 1) - n = 1`] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC) in
  let lemma5 = prove
   (`!k s:real^(N,1)finite_sum->bool.
      lebesgue_measurable s /\ 1 <= k /\ k <= dimindex(:N)
      ==> (negligible s <=>
           negligible { lift a |
                        ~negligible { x:real^(N,1)finite_sum |
                                 (lambda i. if i = k then a else x$i) IN s}})`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `dimindex(:N) + 1`]
     (INST_TYPE [`:(N,1)finite_sum`,`:N`] lemma2)) THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) lemma4 o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
      ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC lemma0 THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:real` THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[]
       `(!x. f(f x) = x) ==> (!y. P y ==> ?x. f x = y)`) THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] lemma1) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. f(f x) = x) /\ (f a IN s <=> Q)  ==> (a IN IMAGE f s <=> Q)`) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] lemma1) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[swap] THEN
    (W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
     REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
     ANTS_TAC THENL
      [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]]) THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THENL
   [GEN_REWRITE_TAC LAND_CONV [lemma3] THEN
    MP_TAC(ISPECL [`k:num`; `(s:real^N->bool) PCROSS (:real^1)`]
        lemma5) THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:real` THEN
    AP_TERM_TAC THEN GEN_REWRITE_TAC RAND_CONV [lemma3] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; FORALL_PASTECART] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV; IN_ELIM_THM] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[fstcart; CART_EQ; LAMBDA_BETA;
             DIMINDEX_FINITE_SUM; DIMINDEX_1; pastecart;
             ARITH_RULE `i <= n ==> i <= n + 1`];
    SUBGOAL_THEN
     `!a x. (lambda i. if i = k then a else x$i):real^N = x`
     (fun th -> REWRITE_TAC[th])
    THENL [SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SET_RULE
     `{lift a | p} = if p then IMAGE lift UNIV else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[IMAGE_LIFT_UNIV; NOT_NEGLIGIBLE_UNIV; NEGLIGIBLE_EMPTY] THEN
    ASM_CASES_TAC `negligible(s:real^N->bool)` THEN
    ASM_REWRITE_TAC[SET_RULE `{x | x IN s} = s`]]);;

let FUBINI_NEGLIGIBLE_REPLACEMENTS_ALT = prove
 (`!k s:real^N->bool.
    lebesgue_measurable s
    ==> (negligible s <=>
         negligible { x:real^N |
                      ~negligible { lift a |
                                (lambda i. if i = k then a else x$i) IN s}})`,
  let lemma0 = prove
   (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> linear((\x. lambda k. x$swap(i,j)k):real^N->real^N)`,
    SIMP_TAC[linear; CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
             LAMBDA_BETA]) in
  let lemma1 = prove
   (`!i j. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
           ==> ((\x. lambda k. x$swap(i,j)k):real^N->real^N) o
               ((\x. lambda k. x$swap(i,j)k):real^N->real^N) = I`,
    SIMP_TAC[CART_EQ; FUN_EQ_THM; o_THM; I_THM; LAMBDA_BETA] THEN
    REPEAT STRIP_TAC THEN REWRITE_TAC[swap] THEN
    REPEAT(COND_CASES_TAC THEN ASM_SIMP_TAC[LAMBDA_BETA])) in
  let lemma2 = prove
   (`!i j s. 1 <= i /\ i <= dimindex(:N) /\ 1 <= j /\ j <= dimindex(:N)
             ==> (negligible
                   (IMAGE ((\x. lambda k. x$swap(i,j)k):real^N->real^N) s) <=>
                  negligible s)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC NEGLIGIBLE_LINEAR_IMAGE_EQ THEN
    ASM_SIMP_TAC[lemma0] THEN
    MATCH_MP_TAC(MESON[] `(!x. n(n x) = x) ==> !x y. n x = n y ==> x = y`) THEN
    ASM_SIMP_TAC[REWRITE_RULE[o_DEF; FUN_EQ_THM; I_DEF] lemma1]) in
  let lemma3 = prove
   (`!s. negligible s <=> negligible(s PCROSS (:real^1))`,
    REWRITE_TAC[NEGLIGIBLE_PCROSS; NOT_NEGLIGIBLE_UNIV]) in
  let lemma4 = prove
   (`!s:real^(N,1)finite_sum->bool.
      lebesgue_measurable s
      ==> (negligible s <=>
           negligible { x:real^(N,1)finite_sum |
                        ~negligible { lift a |
                                  (lambda i. if i = dimindex(:N) + 1 then a
                                             else x$i) IN s}})`,
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP FUBINI_TONELLI_NEGLIGIBLE) THEN
    GEN_REWRITE_TAC LAND_CONV [lemma3] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `z:real^1`] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [SIMPLE_IMAGE_GEN] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN
    CONJ_TAC THENL [MESON_TAC[LIFT_DROP]; X_GEN_TAC `y:real`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[CART_EQ; pastecart; DIMINDEX_FINITE_SUM;
             DIMINDEX_1; LAMBDA_BETA] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `i = dimindex(:N) + 1` THEN
    ASM_REWRITE_TAC[ARITH_RULE `~(n + 1 <= n) /\ (n + 1) - n = 1`] THEN
    REWRITE_TAC[GSYM drop; LIFT_DROP] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_ARITH_TAC) in
  let lemma5 = prove
   (`!k s:real^(N,1)finite_sum->bool.
      lebesgue_measurable s /\ 1 <= k /\ k <= dimindex(:N)
      ==> (negligible s <=>
           negligible { x:real^(N,1)finite_sum |
                        ~negligible { lift a |
                                 (lambda i. if i = k then a else x$i) IN s}})`,
    REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:num`; `dimindex(:N) + 1`]
     (INST_TYPE [`:(N,1)finite_sum`,`:N`] lemma2)) THEN
    REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN ANTS_TAC THENL
     [REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th])] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) lemma4 o lhand o snd) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC LEBESGUE_MEASURABLE_LINEAR_IMAGE_GEN THEN
      ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC lemma0 THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC SURJECTIVE_IMAGE_EQ THEN CONJ_TAC THENL
     [MATCH_MP_TAC(MESON[]
       `(!x. f(f x) = x) ==> (!y. P y ==> ?x. f x = y)`) THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] lemma1) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^(N,1)finite_sum` THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `a:real` THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. f(f x) = x) /\ (f a IN s <=> Q)  ==> (a IN IMAGE f s <=> Q)`) THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[FUN_EQ_THM; o_THM; I_THM] lemma1) THEN
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN ASM_ARITH_TAC;
      AP_THM_TAC THEN AP_TERM_TAC] THEN
    SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i:num = k` THEN ASM_REWRITE_TAC[swap] THEN
    (W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
     REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
     ANTS_TAC THENL
      [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC THEN SIMP_TAC[]]) THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) LAMBDA_BETA o lhand o snd) THEN
    REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC) in
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `1 <= k /\ k <= dimindex(:N)` THENL
   [ONCE_REWRITE_TAC[lemma3] THEN
    MP_TAC(ISPECL [`k:num`; `(s:real^N->bool) PCROSS (:real^1)`]
        lemma5) THEN
    ASM_REWRITE_TAC[LEBESGUE_MEASURABLE_PCROSS; LEBESGUE_MEASURABLE_UNIV] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV] THEN REPEAT GEN_TAC THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV o LAND_CONV)
     [GSYM PASTECART_FST_SND] THEN
    REWRITE_TAC[PASTECART_IN_PCROSS; IN_UNIV] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    SIMP_TAC[fstcart; CART_EQ; LAMBDA_BETA;
             DIMINDEX_FINITE_SUM; DIMINDEX_1; pastecart;
             ARITH_RULE `i <= n ==> i <= n + 1`];
    SUBGOAL_THEN
     `!a x. (lambda i. if i = k then a else x$i):real^N = x`
     (fun th -> REWRITE_TAC[th])
    THENL [SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[SET_RULE
     `{lift a | p} = if p then IMAGE lift UNIV else {}`] THEN
    ONCE_REWRITE_TAC[COND_RAND] THEN
    REWRITE_TAC[IMAGE_LIFT_UNIV; NOT_NEGLIGIBLE_UNIV; NEGLIGIBLE_EMPTY] THEN
    AP_TERM_TAC THEN SET_TAC[]]);;

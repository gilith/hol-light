(* ========================================================================= *)
(* The multiplicative group of integers modulo n.                            *)
(* ========================================================================= *)

needs "Library/grouptheory.ml";;
needs "Library/primitive.ml";;

(* ------------------------------------------------------------------------- *)
(* A trivial general lemma used to dispose of degnerate cases.               *)
(* ------------------------------------------------------------------------- *)

let MULT_EQ_2 = prove
 (`!m n. m * n = 2 <=> m = 1 /\ n = 2 \/ m = 2 /\ n = 1`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `m = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `2 * 2 <= p ==> ~(p = 2)`) THEN
  MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas about orders of elements in Abelian groups. These aren't      *)
(* really specific to this development, and could be put back into the       *)
(* core "Library/grouptheory.ml" file, but the proofs use a bit more         *)
(* material on prime factorization than is currently used in that file.      *)
(* ------------------------------------------------------------------------- *)

let GROUP_ELEMENT_ORDER_LCM_EXISTS = prove
 (`!G x y:A.
        x IN group_carrier G /\ y IN group_carrier G /\
        group_mul G x y = group_mul G y x
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `group_element_order G (x:A) = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  ASM_CASES_TAC `group_element_order G (y:A) = 0` THENL
   [ASM_MESON_TAC[LCM_0]; ALL_TAC] THEN
  MP_TAC(SPECL [`group_element_order G (x:A)`; `group_element_order G (y:A)`]
        LCM_COPRIME_DECOMP) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `n:num`] THEN
  REWRITE_TAC[divides; IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `m':num` THEN DISCH_TAC THEN
  X_GEN_TAC `n':num` THEN DISCH_TAC THEN DISCH_TAC THEN
  DISCH_THEN(fun th -> SUBST1_TAC(SYM th) THEN ASSUME_TAC(SYM th)) THEN
  EXISTS_TAC `group_mul G (group_pow G x m') (group_pow G y n'):A` THEN
  ASM_SIMP_TAC[GROUP_MUL; GROUP_POW] THEN
  SUBGOAL_THEN
   `group_element_order G (group_pow G (x:A) m') = m /\
    group_element_order G (group_pow G (y:A) n') = n`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_POW_GEN] THEN CONJ_TAC THEN
    (COND_CASES_TAC THENL [ASM_MESON_TAC[MULT_CLAUSES]; ALL_TAC]) THEN
    REWRITE_TAC[NUMBER_RULE `gcd(a * b:num,a) = a /\ gcd(a * b,b) = b`] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_SIMP_TAC[DIV_MULT];
    W(MP_TAC o PART_MATCH (lhand o rand) GROUP_ELEMENT_ORDER_MUL_EQ o
      lhand o snd) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[GROUP_POW] THEN MATCH_MP_TAC GROUP_COMMUTES_POW THEN
    ASM_SIMP_TAC[GROUP_POW] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC GROUP_COMMUTES_POW THEN ASM_REWRITE_TAC[]]);;

let ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS = prove
 (`!G x y:A.
        abelian_group G /\
        x IN group_carrier G /\ y IN group_carrier G
        ==> ?z. z IN group_carrier G /\
                group_element_order G z =
                lcm(group_element_order G x,group_element_order G y)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC GROUP_ELEMENT_ORDER_LCM_EXISTS THEN
  ASM_MESON_TAC[abelian_group]);;

let ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL = prove
 (`!G:A group.
      abelian_group G /\ FINITE(group_carrier G)
      ==> ?x. x IN group_carrier G /\
              !y. y IN group_carrier G
                  ==> group_element_order G y divides group_element_order G x`,
  REPEAT STRIP_TAC THEN MP_TAC(fst(EQ_IMP_RULE(ISPEC
   `IMAGE (group_element_order G) (group_carrier G:A->bool)` num_MAX))) THEN
  REWRITE_TAC[MESON[IN] `IMAGE f s x <=> x IN IMAGE f s`] THEN
  ASM_SIMP_TAC[GSYM num_FINITE; FINITE_IMAGE] THEN
  REWRITE_TAC[MEMBER_NOT_EMPTY; IMAGE_EQ_EMPTY; GROUP_CARRIER_NONEMPTY] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE; FORALL_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `z:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN DISCH_TAC THEN
  REWRITE_TAC[DIVIDES_LCM_LEFT] THEN REWRITE_TAC[GSYM LE_ANTISYM] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[ABELIAN_GROUP_ELEMENT_ORDER_LCM_EXISTS];
    ASM_MESON_TAC[DIVIDES_LE; LCM; FINITE_GROUP_ELEMENT_ORDER_NONZERO;
                  LCM_ZERO]]);;

let ABELIAN_GROUP_ELEMENT_ORDER_DIVIDES_MAXIMAL_ALT = prove
 (`!G:A group.
        abelian_group G /\ FINITE(group_carrier G)
        ==> ?x. x IN group_carrier G /\
                !y. y IN group_carrier G
                    ==> group_pow G y (group_element_order G x) = group_id G`,
  SIMP_TAC[GROUP_POW_EQ_ID] THEN
  REWRITE_TAC[ABELIAN_GROUP_ORDER_DIVIDES_MAXIMAL]);;

(* ------------------------------------------------------------------------- *)
(* Multiplicative group of integers mod n, with degenerate {1} for n <= 1.   *)
(* ------------------------------------------------------------------------- *)

let modmul_group = new_definition
 `modmul_group n =
        if n <= 1 then singleton_group 1
        else group({m | m < n /\ coprime(m,n)},
                   1,inverse_mod n,(\a b. (a * b) MOD n))`;;

let MODMUL_GROUP = prove
 (`(!n. group_carrier(modmul_group n) =
        if n <= 1 then {1} else {m | m < n /\ coprime(m,n)}) /\
   (!n. group_id(modmul_group n) = 1) /\
   (!n. group_inv(modmul_group n) = inverse_mod n) /\
   (!n. group_mul(modmul_group n) =
        if n <= 1 then (\a b. 1) else (\a b. (a * b) MOD n))`,
  REWRITE_TAC[AND_FORALL_THM] THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[modmul_group] THEN
  ASM_CASES_TAC `n <= 1` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[SINGLETON_GROUP] THEN ASM_REWRITE_TAC[FUN_EQ_THM; inverse_mod];
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE `~(n <= 1) <=> 2 <= n`])] THEN
  REWRITE_TAC[group_carrier; group_id; group_inv; group_mul] THEN
  REWRITE_TAC[GSYM PAIR_EQ; GSYM(CONJUNCT2 group_tybij)] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; ARITH_RULE `1 < n <=> 2 <= n`] THEN
  REWRITE_TAC[NUMBER_RULE `coprime(1,n)`; PAIR_EQ] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `m:num` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INVERSE_MOD_BOUND] THEN
    MATCH_MP_TAC(NUMBER_RULE `!m. (a * m == 1) (mod n) ==> coprime(a,n)`) THEN
    EXISTS_TAC `m:num` THEN REWRITE_TAC[INVERSE_MOD_LMUL_EQ] THEN
    ASM_MESON_TAC[COPRIME_SYM];
    REWRITE_TAC[COPRIME_LMOD; COPRIME_LMUL] THEN
    ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `2 <= n ==> ~(n = 0)`];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_MULT_MOD2] THEN
    REWRITE_TAC[MOD_MOD_REFL] THEN REWRITE_TAC[MOD_MULT_MOD2] THEN
    REWRITE_TAC[MULT_ASSOC];
    SIMP_TAC[MULT_CLAUSES; MOD_LT];
    REWRITE_TAC[MOD_UNIQUE; INVERSE_MOD_RMUL_EQ; INVERSE_MOD_LMUL_EQ] THEN
    ASM_SIMP_TAC[ARITH_RULE `2 <= n ==> 1 < n`] THEN
    MESON_TAC[COPRIME_SYM]]);;

let FINITE_MODMUL_GROUP = prove
 (`!n. FINITE(group_carrier(modmul_group n))`,
  GEN_TAC THEN REWRITE_TAC[MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_SING] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `0..n` THEN
  REWRITE_TAC[FINITE_NUMSEG; SUBSET; IN_ELIM_THM; IN_NUMSEG] THEN
  ARITH_TAC);;

let ORDER_MODMUL_GROUP = prove
 (`!n. CARD(group_carrier(modmul_group n)) =
       if n = 0 then 1 else phi n`,
  GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[MODMUL_GROUP; LE_0; CARD_SING] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[LE_REFL; PHI_1; CARD_SING] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[PHI_ALT]);;

let HAS_SIZE_MODMUL_GROUP = prove
 (`!n. ~(n = 0) ==> group_carrier(modmul_group n) HAS_SIZE phi n`,
  SIMP_TAC[HAS_SIZE; FINITE_MODMUL_GROUP] THEN
  SIMP_TAC[ORDER_MODMUL_GROUP]);;

let ABELIAN_MODMUL_GROUP = prove
 (`!n. abelian_group(modmul_group n)`,
  GEN_TAC THEN REWRITE_TAC[abelian_group; MODMUL_GROUP] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MULT_SYM]);;

let TRIVIAL_MODMUL_GROUP = prove
 (`!n. trivial_group(modmul_group n) <=> n <= 2`,
  GEN_TAC THEN REWRITE_TAC[TRIVIAL_GROUP_HAS_SIZE_1; HAS_SIZE] THEN
  REWRITE_TAC[FINITE_MODMUL_GROUP] THEN
  REWRITE_TAC[ORDER_MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN ASM_REWRITE_TAC[PHI_1; ARITH] THEN
  ASM_CASES_TAC `n = 2` THEN ASM_REWRITE_TAC[PHI_2; ARITH] THEN
  MATCH_MP_TAC(ARITH_RULE `~(n <= 2) /\ 2 <= p ==> (p = 1 <=> n <= 2)`) THEN
  CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC PHI_LOWERBOUND_2] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Chinese remainder theorem in group-theoretic language.                    *)
(* ------------------------------------------------------------------------- *)

let GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP = prove
 (`!m n. 2 <= m /\ 2 <= n
         ==> group_homomorphism (modmul_group(m * n),
                                 prod_group (modmul_group m)
                                            (modmul_group n))
                                (\a. (a MOD m),(a MOD n))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[GROUP_HOMOMORPHISM; PROD_GROUP; SUBSET] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; FORALL_PAIR_THM; IN_CROSS] THEN
  REWRITE_TAC[MODMUL_GROUP] THEN
  REWRITE_TAC[ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`] THEN
  ASM_SIMP_TAC[MULT_EQ_0; MULT_EQ_1; IN_ELIM_THM; MOD_LT_EQ; COPRIME_LMOD;
               PAIR_EQ; ARITH_RULE  `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  SIMP_TAC[COPRIME_RMUL; MOD_MOD; ONCE_REWRITE_RULE[MULT_SYM] MOD_MOD] THEN
  REWRITE_TAC[MOD_MULT_MOD2]);;

let GROUP_ISOMORPHISM_PROD_MODMUL_GROUP = prove
 (`!m n. 2 <= m /\ 2 <= n /\ coprime(m,n)
         ==> group_isomorphism (modmul_group(m * n),
                                prod_group (modmul_group m)
                                           (modmul_group n))
                               (\a. (a MOD m),(a MOD n))`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand)
    GROUP_ISOMORPHISM_EQ_MONOMORPHISM_FINITE o snd) THEN
  ASM_SIMP_TAC[ORDER_MODMUL_GROUP; FINITE_PROD_GROUP;
               FINITE_MODMUL_GROUP; MULT_EQ_0;
               CONJUNCT1 PROD_GROUP; CARD_CROSS; PHI_MULTIPLICATIVE;
               ARITH_RULE `2 <= n ==> ~(n = 0)`] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[group_monomorphism] THEN
  ASM_SIMP_TAC[GROUP_HOMOMORPHISM_PROD_MODMUL_GROUP] THEN
  ASM_SIMP_TAC[MODMUL_GROUP; MULT_EQ_0; MULT_EQ_1;
               ARITH_RULE `n <= 1 <=> n = 0 \/ n = 1`;
               ARITH_RULE `2 <= n ==> ~(n = 0) /\ ~(n = 1)`] THEN
  REWRITE_TAC[PAIR_EQ; IN_ELIM_THM; GSYM CONG] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONG_IMP_EQ THEN
  EXISTS_TAC `m * n:num` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[NUMBER_RULE
   `coprime(m:num,n) /\ (x == y) (mod m) /\ (x == y) (mod n)
    ==> (x == y) (mod(m * n))`]);;

let ISOMORPHIC_GROUP_MODMUL_GROUP = prove
 (`!m n. coprime(m,n)
         ==> prod_group (modmul_group m)
                        (modmul_group n)
             isomorphic_group (modmul_group (m * n))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[ISOMORPHIC_TRIVIAL_GROUPS]
   `(trivial_group G <=> trivial_group H) /\
    (~trivial_group G /\ ~trivial_group H ==> G isomorphic_group H)
    ==> G isomorphic_group H`) THEN
  REWRITE_TAC[TRIVIAL_PROD_GROUP; TRIVIAL_MODMUL_GROUP] THEN
  POP_ASSUM MP_TAC THEN
  ASM_CASES_TAC `m = 0` THEN ASM_SIMP_TAC[COPRIME_0; ARITH] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_SIMP_TAC[COPRIME_0; ARITH] THEN
  DISCH_TAC THEN
  ASM_CASES_TAC `m = 1` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ISOMORPHIC_PROD_TRIVIAL_GROUP;
              TRIVIAL_MODMUL_GROUP; ARITH] THEN
  ASM_CASES_TAC `n = 1` THEN
  ASM_SIMP_TAC[MULT_CLAUSES; ISOMORPHIC_PROD_TRIVIAL_GROUP;
               TRIVIAL_MODMUL_GROUP; ARITH] THEN
  ASM_REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  ASM_REWRITE_TAC[MULT_EQ_0; MULT_EQ_1; MULT_EQ_2] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[COPRIME_REFL]; DISCH_THEN(K ALL_TAC)] THEN
  ONCE_REWRITE_TAC[ISOMORPHIC_GROUP_SYM] THEN
  REWRITE_TAC[isomorphic_group] THEN
  EXISTS_TAC `\a. (a MOD m),(a MOD n)` THEN
  MATCH_MP_TAC GROUP_ISOMORPHISM_PROD_MODMUL_GROUP THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let GROUP_POW_MODMUL_GROUP = prove
 (`!n a k. group_pow (modmul_group n) a k =
           if n <= 1 then 1 else (a EXP k) MOD n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[group_pow; MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP] THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC;
    MESON_TAC[MOD_MULT_MOD2; MOD_MOD_REFL; MOD_EXP_MOD]]);;

let GROUP_ELEMENT_ORDER_MODMUL_GROUP = prove
 (`!n a. a IN group_carrier(modmul_group n)
         ==> group_element_order (modmul_group n) a = order n a`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[GROUP_ELEMENT_ORDER_UNIQUE] THEN
  REWRITE_TAC[GSYM ORDER_DIVIDES] THEN
  X_GEN_TAC `k:num` THEN POP_ASSUM MP_TAC THEN
  REWRITE_TAC[GROUP_POW_MODMUL_GROUP] THEN
  REWRITE_TAC[MODMUL_GROUP] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[IN_SING; EXP_ONE; CONG] THEN
  DISCH_THEN(K ALL_TAC) THEN RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE]) THEN
  ASM_SIMP_TAC[MOD_LT]);;

(* ------------------------------------------------------------------------- *)
(* Existence of primitive roots in group-theoretic language.                 *)
(* ------------------------------------------------------------------------- *)

let CYCLIC_MODMUL_GROUP = prove
 (`!n. cyclic_group(modmul_group n) <=>
       n = 0 \/ n = 1 \/ n = 2 \/ n = 4 \/
       ?p k. prime p /\ 3 <= p /\ (n = p EXP k \/ n = 2 * p EXP k)`,
  GEN_TAC THEN ASM_CASES_TAC `n <= 2` THENL
   [ASM_SIMP_TAC[TRIVIAL_MODMUL_GROUP;
                 TRIVIAL_IMP_CYCLIC_GROUP] THEN
    ASM_ARITH_TAC;
    RULE_ASSUM_TAC(REWRITE_RULE[NOT_LE])] THEN
  SIMP_TAC[CYCLIC_GROUP_ELEMENT_ORDER; FINITE_MODMUL_GROUP] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[GROUP_ELEMENT_ORDER_MODMUL_GROUP] THEN
  MP_TAC(SPEC `n:num` PRIMITIVE_ROOT_EXISTS) THEN
  ASM_SIMP_TAC[ORDER_MODMUL_GROUP; FINITE_MODMUL_GROUP;
               MODMUL_GROUP;
               ARITH_RULE `2 < n ==> ~(n = 0) /\ ~(n = 1) /\ ~(n <= 1)`] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IMP] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k MOD n` THEN
  ASM_SIMP_TAC[MOD_LT_EQ; ARITH_RULE `2 < n ==> ~(n = 0)`] THEN
  MATCH_MP_TAC(TAUT `(~p ==> ~q) /\ q ==> p /\ q`) THEN
  ONCE_REWRITE_TAC[COPRIME_SYM] THEN SIMP_TAC[GSYM ORDER_EQ_0] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  ASM_SIMP_TAC[PHI_EQ_0; ARITH_RULE `2 < n ==> ~(n = 0)`] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ORDER_CONG THEN
  REWRITE_TAC[CONG_LMOD; CONG_REFL]);;

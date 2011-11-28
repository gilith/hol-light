(* ------------------------------------------------------------------------- *)
(* Natural number primes.                                                    *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-def";;

let prime_def = new_definition
  `!p. prime p <=> ~(p = 1) /\ !n. divides n p ==> n = 1 \/ n = p`;;

export_thm prime_def;;

logfile "natural-prime-thm";;

let prime_zero = prove
  (`~prime 0`,
   REWRITE_TAC [prime_def; divides_zero; DE_MORGAN_THM; NOT_FORALL_THM] THEN
   DISJ2_TAC THEN
   EXISTS_TAC `SUC (SUC 0)` THEN
   REWRITE_TAC [NOT_SUC; ONE; SUC_INJ]);;

export_thm prime_zero;;

let prime_one = prove
  (`~prime 1`,
   REWRITE_TAC [prime_def]);;

export_thm prime_one;;

let prime_two = prove
  (`prime 2`,
   REWRITE_TAC [prime_def; divides_two] THEN
   NUM_REDUCE_TAC);;

export_thm prime_two;;

let prime_three = prove
  (`prime 3`,
   REWRITE_TAC [prime_def; divides_three] THEN
   NUM_REDUCE_TAC);;

export_thm prime_three;;

let prime_even = prove
  (`!p. prime p /\ EVEN p ==> p = 2`,
   GEN_TAC THEN
   REWRITE_TAC [prime_def; GSYM two_divides] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `2`) THEN
   ASM_REWRITE_TAC [] THEN
   NUM_REDUCE_TAC THEN
   MATCH_ACCEPT_TAC EQ_SYM);;

export_thm prime_even;;

let coprime_prime_imp = prove
  (`!p n. prime p /\ ~divides p n ==> gcd p n = 1`,
   REWRITE_TAC [prime_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_is_one THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `c : num`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `~divides p n` THEN
   ASM_REWRITE_TAC []);;

export_thm coprime_prime_imp;;

let coprime_prime = prove
  (`!p n. prime p ==> (gcd p n = 1 <=> ~divides p n)`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `gcd p n = 1` THENL
   [ASM_REWRITE_TAC [GSYM divides_gcd] THEN
    DISCH_THEN (SUBST_VAR_TAC) THEN
    MP_TAC prime_one THEN
    ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
    STRIP_TAC THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC coprime_prime_imp THEN
    ASM_REWRITE_TAC []]);;

export_thm coprime_prime;;

let prime_divides_mult_imp = prove
  (`!p m n. prime p /\ ~divides p m /\ ~divides p n ==> ~divides p (m * n)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
   MP_TAC (GSYM (SPEC `p : num` coprime_prime)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM divides_one] THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `gcd p m * gcd p n` THEN
   CONJ_TAC THENL
   [MATCH_ACCEPT_TAC divides_gcd_mult;
    ASM_REWRITE_TAC [MULT_1; divides_refl]]);;

export_thm prime_divides_mult_imp;;

let prime_divides_mult = prove
  (`!p m n. prime p ==> (divides p (m * n) <=> divides p m \/ divides p n)`,
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
    REWRITE_TAC [NOT_OR_THM] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC prime_divides_mult_imp THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_mult1 THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC divides_mult2 THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm prime_divides_mult;;

let prime_divisor = prove
  (`!n. ~(n = 1) ==> ?p. prime p /\ divides p n`,
   GEN_TAC THEN
   WF_INDUCT_TAC `n : num` THEN
   STRIP_TAC THEN
   ASM_CASES_TAC `n = 0` THENL
   [EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC [prime_two; divides_zero];
    ALL_TAC] THEN
   ASM_CASES_TAC `prime n` THENL
   [EXISTS_TAC `n : num` THEN
    ASM_REWRITE_TAC [divides_refl];
    ALL_TAC] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [prime_def]) THEN
   ASM_REWRITE_TAC [NOT_FORALL_THM; NOT_IMP; NOT_OR_THM] THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `m : num`) THEN
   ASM_REWRITE_TAC [] THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [LT_LE] THEN
    MATCH_MP_TAC divides_le THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    EXISTS_TAC `p : num` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `m : num` THEN
    ASM_REWRITE_TAC []]);;

export_thm prime_divisor;;

let large_prime = prove
  (`!n. ?p. n <= p /\ prime p`,
   GEN_TAC THEN
   MP_TAC (SPEC `FACT n + 1` prime_divisor) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [EQ_ADD_RCANCEL_0; FACT_NZ];
    ALL_TAC] THEN
   STRIP_TAC THEN
   EXISTS_TAC `p : num` THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `p : num`] LE_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`p : num`; `FACT n + 1`] coprime_prime) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC coprime_egcd THEN
   MP_TAC (SPECL [`n : num`; `p : num`] divides_factorial) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST_VAR_TAC THEN
    MP_TAC prime_zero THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `k : num` (SUBST1_TAC o SYM) o
      REWRITE_RULE [divides_def]) THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [ONE_MULT; DIST_RADD_0]);;

export_thm large_prime;;

logfile_end ();;

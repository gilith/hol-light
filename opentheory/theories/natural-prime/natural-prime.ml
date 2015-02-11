(* ========================================================================= *)
(* PRIME NATURAL NUMBERS                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for prime natural numbers.                                *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/natural-prime/natural-prime.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of prime natural numbers.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-def";;

let prime_def = new_definition
  `!p. prime p <=> ~(p = 1) /\ !n. divides n p ==> n = 1 \/ n = p`;;

export_thm prime_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of prime natural numbers.                                      *)
(* ------------------------------------------------------------------------- *)

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

let prime_divides_inj = prove
  (`!p1 p2. prime p1 /\ prime p2 /\ divides p1 p2 ==> p1 = p2`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `p2 : num` prime_def) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC o SPEC `p1 : num`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `prime p1` THEN
   ASM_REWRITE_TAC [prime_one]);;

export_thm prime_divides_inj;;

let prime_even = prove
  (`!p. prime p /\ EVEN p ==> p = 2`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC prime_divides_inj THEN
   ASM_REWRITE_TAC [prime_two; two_divides]);;

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

let prime_divisor_lt = prove
  (`!n.
      prime n <=>
      ~(n = 0) /\ ~(n = 1) /\ !p. prime p /\ p < n ==> ~divides p n`,
   GEN_TAC THEN
   ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC [prime_zero];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `n = 1` THENL
   [ASM_REWRITE_TAC [prime_one];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `p < (n : num)` THEN
    REWRITE_TAC [NOT_LT] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC prime_divides_inj THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    REWRITE_TAC [prime_def] THEN
    ASM_REWRITE_TAC [] THEN
    X_GEN_TAC `m : num` THEN
    ASM_CASES_TAC `m = 0` THENL
    [ASM_REWRITE_TAC [zero_divides];
     ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `m = 1` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPEC `m : num` prime_divisor) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `p : num`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [GSYM CONTRAPOS_THM]) THEN
    REWRITE_TAC [NOT_LT] THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `m : num` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    STRIP_TAC THEN
    REWRITE_TAC [GSYM LE_ANTISYM] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC divides_le THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `p : num` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC divides_le THEN
     ASM_REWRITE_TAC []]]);;

export_thm prime_divisor_lt;;

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

(* ------------------------------------------------------------------------- *)
(* Definition of the ordered stream of all prime numbers.                    *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-stream-def";;

let (primes_mono_le,snth_primes) =
  let def = new_specification ["primes"]
              (MATCH_MP num_stream_exists large_prime) in
  CONJ_PAIR def;;

export_thm primes_mono_le;;
export_thm snth_primes;;

let primes_def = CONJ primes_mono_le snth_primes;;

let primes_below_def = new_definition
  `!n.
     primes_below n =
     stake primes (minimal i. n <= snth primes i)`;;

export_thm primes_below_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the ordered stream of all prime numbers.                    *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-stream-thm";;

let prime_primes = prove
  (`!i. prime (snth primes i)`,
   GEN_TAC THEN
   REWRITE_TAC [snth_primes] THEN
   EXISTS_TAC `i : num` THEN
   REFL_TAC);;

export_thm prime_primes;;

let primes_nonzero = prove
  (`!i. ~(snth primes i = 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC prime_zero THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [prime_primes]);;

export_thm primes_nonzero;;

let primes_mono_lt = prove
  (`!i j. snth primes i < snth primes j <=> i < j`,
   REWRITE_TAC [GSYM MONO_LE_LT] THEN
   ACCEPT_TAC primes_mono_le);;

export_thm primes_mono_lt;;

let primes_mono_le_imp = prove
  (`!i j. i <= j ==> snth primes i <= snth primes j`,
   REWRITE_TAC [primes_mono_le]);;

export_thm primes_mono_le_imp;;

let primes_mono_lt_imp = prove
  (`!i j. i < j ==> snth primes i < snth primes j`,
   REWRITE_TAC [primes_mono_lt]);;

export_thm primes_mono_lt_imp;;

let snth_primes_zero = prove
  (`snth primes 0 = 2`,
   REWRITE_TAC [GSYM LE_ANTISYM] THEN
   CONJ_TAC THENL
   [STRIP_ASSUME_TAC (REWRITE_RULE [snth_primes] prime_two) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [primes_mono_le; LE_0];
    REWRITE_TAC [GSYM NOT_LT; TWO; ONE; LT] THEN
    MP_TAC (SPEC `0` prime_primes) THEN
    SPEC_TAC (`snth primes 0`, `n : num`) THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [GSYM ONE; prime_zero; prime_one]]);;

export_thm snth_primes_zero;;

let primes_below_prime = prove
  (`!i. primes_below (snth primes i) = stake primes i`,
   GEN_TAC THEN
   REWRITE_TAC [primes_below_def; primes_mono_le] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC MINIMAL_EQ THEN
   REWRITE_TAC [LE_REFL; NOT_LE]);;

export_thm primes_below_prime;;

let primes_below_zero = prove
  (`primes_below 0 = []`,
   REWRITE_TAC [primes_below_def; LE_0; MINIMAL_T; stake_zero]);;

export_thm primes_below_zero;;

let primes_below_suc = prove
  (`!n.
      primes_below (SUC n) =
      APPEND (primes_below n) (if prime n then [n] else [])`,
   GEN_TAC THEN
   REWRITE_TAC [primes_below_def] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [snth_primes]) THEN
    SUBGOAL_THEN
      `(minimal i. SUC n <= snth primes i) = SUC i` SUBST1_TAC THENL
    [REWRITE_TAC [LE_SUC_LT] THEN
     FIRST_X_ASSUM (fun th -> REWRITE_TAC [GSYM th; primes_mono_lt]) THEN
     MATCH_MP_TAC MINIMAL_EQ THEN
     REWRITE_TAC [SUC_LT] THEN
     REWRITE_TAC [LT_SUC_LE; NOT_LT];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `(minimal i. n <= snth primes i) = i` SUBST1_TAC THENL
    [FIRST_X_ASSUM (fun th -> REWRITE_TAC [GSYM th; primes_mono_le]) THEN
     MATCH_MP_TAC MINIMAL_EQ THEN
     REWRITE_TAC [LE_REFL; NOT_LE];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    MATCH_ACCEPT_TAC stake_suc';
    REWRITE_TAC [APPEND_NIL] THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    ABS_TAC THEN
    REWRITE_TAC [LE_SUC_LT] THEN
    CONV_TAC (LAND_CONV (REWR_CONV LT_LE)) THEN
    MATCH_MP_TAC (TAUT `!x y. y ==> (x /\ y <=> x)`) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~prime n` THEN
    ASM_REWRITE_TAC [prime_primes]]);;

export_thm primes_below_suc;;

let primes_below_one = prove
  (`primes_below 1 = []`,
   REWRITE_TAC [ONE; primes_below_suc; primes_below_zero] THEN
   REWRITE_TAC [NIL_APPEND; prime_zero]);;

export_thm primes_below_one;;

let primes_below_two = prove
  (`primes_below 2 = []`,
   REWRITE_TAC [TWO; primes_below_suc; primes_below_one] THEN
   REWRITE_TAC [NIL_APPEND; prime_one]);;

export_thm primes_below_two;;

let primes_below_three = prove
  (`primes_below 3 = [2]`,
   REWRITE_TAC [THREE; primes_below_suc; primes_below_two] THEN
   REWRITE_TAC [NIL_APPEND; prime_two]);;

export_thm primes_below_three;;

let mem_primes_below = prove
  (`!n p. MEM p (primes_below n) <=> prime p /\ p < n`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [primes_below_zero; LT; MEM];
    REWRITE_TAC [LT_SUC_LE] THEN
    REWRITE_TAC [LE_LT; LEFT_OR_DISTRIB] THEN
    REWRITE_TAC [primes_below_suc] THEN
    ASM_REWRITE_TAC [MEM_APPEND] THEN
    POP_ASSUM (K ALL_TAC) THEN
    AP_TERM_TAC THEN
    COND_CASES_TAC THENL
    [REWRITE_TAC [MEM] THEN
     ASM_CASES_TAC `p = (n : num)` THEN
     ASM_REWRITE_TAC [];
     REWRITE_TAC [MEM] THEN
     ASM_CASES_TAC `p = (n : num)` THEN
     ASM_REWRITE_TAC []]]);;

export_thm mem_primes_below;;

let primes_below_divides = prove
  (`!n.
      prime n <=>
      ~(n = 0) /\ ~(n = 1) /\ ALL (\p. ~divides p n) (primes_below n)`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [prime_divisor_lt] THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [GSYM ALL_MEM; mem_primes_below]);;

export_thm primes_below_divides;;

let primes_inj_imp = prove
  (`!n1 n2. snth primes n1 = snth primes n2 ==> n1 = n2`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM LE_ANTISYM] THEN
   ONCE_REWRITE_TAC [GSYM primes_mono_le] THEN
   REWRITE_TAC [LE_ANTISYM] THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm primes_inj_imp;;

let primes_inj = prove
  (`!n1 n2. snth primes n1 = snth primes n2 <=> n1 = n2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC primes_inj_imp;
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm primes_inj;;

let primes_divides_inj_imp = prove
  (`!n1 n2. divides (snth primes n1) (snth primes n2) ==> n1 = n2`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC primes_inj_imp THEN
   MATCH_MP_TAC prime_divides_inj THEN
   ASM_REWRITE_TAC [prime_primes]);;

export_thm primes_divides_inj_imp;;

let primes_divides_inj = prove
  (`!n1 n2. divides (snth primes n1) (snth primes n2) <=> n1 = n2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC primes_divides_inj_imp;
    DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC divides_refl]);;

export_thm primes_divides_inj;;

let primes_equiv = prove
  (`!ps.
      ps = primes <=>
      (!i j. snth ps i <= snth ps j <=> i <= j) /\
      (!p. prime p <=> ?i. snth ps i = p)`,
   GEN_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL
    [ACCEPT_TAC primes_mono_le;
     ACCEPT_TAC snth_primes];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [snth_primes_zero; GSYM LE_ANTISYM] THEN
    CONJ_TAC THENL
    [POP_ASSUM
       ((CHOOSE_THEN
          (SUBST1_TAC o SYM)) o
        (REWRITE_RULE [prime_two] o SPEC `2`)) THEN
     ASM_REWRITE_TAC [LE_0];
     MP_TAC (SPEC `snth ps 0 : num` num_CASES) THEN
     STRIP_TAC THENL
     [SUBGOAL_THEN `F` CONTR_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
      REWRITE_TAC [prime_zero] THEN
      EXISTS_TAC `0` THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
     MP_TAC (SPEC `n : num` num_CASES) THEN
     STRIP_TAC THENL
     [SUBGOAL_THEN `F` CONTR_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `1`) THEN
      REWRITE_TAC [prime_one] THEN
      EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC [ONE];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [TWO; ONE; LE_SUC; LE_0]];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM LE_ANTISYM] THEN
   CONJ_TAC THENL
   [MP_TAC (SPEC `SUC n` prime_primes) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CHOOSE_THEN (STRIP_ASSUME_TAC o SYM)) THEN
    ASM_REWRITE_TAC [LE_SUC_LT] THEN
    REWRITE_TAC [GSYM NOT_LE] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM o SPECL [`i : num`; `n : num`]) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC [primes_mono_le] THEN
    REWRITE_TAC [NOT_LE; SUC_LT];
    SUBGOAL_THEN `prime (snth ps (SUC n))`
      (CHOOSE_THEN (STRIP_ASSUME_TAC o SYM) o REWRITE_RULE [snth_primes]) THENL
    [ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `SUC n` THEN
     REFL_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [LE_SUC_LT; primes_mono_le] THEN
    REWRITE_TAC [GSYM NOT_LE] THEN
    ONCE_REWRITE_TAC [GSYM primes_mono_le] THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_LE; SUC_LT]]);;

export_thm primes_equiv;;

let snth_primes_zero_test = prove
  (`~(snth primes 0 = 0)`,
   REWRITE_TAC [snth_primes_zero; TWO; NOT_SUC]);;

export_thm snth_primes_zero_test;;

let primes_divides_inj_test = prove
  (`!i j. ~divides (snth primes i) (snth primes (i + j + 1))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [primes_divides_inj] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   REWRITE_TAC [EQ_ADD_LCANCEL_0; ADD_EQ_0; ONE; NOT_SUC]);;

export_thm primes_divides_inj_test;;

let primes_below_prime_test = prove
  (`!n i.
      EX (\p. divides p (n + 2)) (stake primes i) \/
      snth primes i <= n + 2`,
   REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC
     [GSYM primes_below_prime; GSYM EX_MEM; mem_primes_below] THEN
   ASM_CASES_TAC `snth primes i <= n + 2` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `n + 2` prime_divisor) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [TWO; ONE; ADD_SUC; SUC_INJ; NOT_SUC];
    ALL_TAC] THEN
   STRIP_TAC THEN
   EXISTS_TAC `p : num` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `n + 2` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC divides_le THEN
    ASM_REWRITE_TAC [ADD_EQ_0] THEN
    REWRITE_TAC [TWO; NOT_SUC];
    ASM_REWRITE_TAC [GSYM NOT_LE]]);;

export_thm primes_below_prime_test;;

let primes_equiv_test = prove
  (`!ps.
      ps = primes <=>
      ~(snth ps 0 = 0) /\
      (!i j. snth ps i <= snth ps j <=> i <= j) /\
      (!i j. ~divides (snth ps i) (snth ps (i + j + 1))) /\
      (!n i. EX (\p. divides p (n + 2)) (stake ps i) \/ snth ps i <= n + 2)`,
   GEN_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN
    REPEAT CONJ_TAC THENL
    [ACCEPT_TAC snth_primes_zero_test;
     ACCEPT_TAC primes_mono_le;
     ACCEPT_TAC primes_divides_inj_test;
     ACCEPT_TAC primes_below_prime_test];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [primes_equiv] THEN
   CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   GEN_TAC THEN
   WF_INDUCT_TAC `p : num` THEN
   ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC [prime_zero; NOT_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `!i j. (snth ps i : num) <= snth ps j <=> i <= j`
      (MP_TAC o SPECL [`0`; `i : num`]) THEN
    ASM_REWRITE_TAC [LE_0; LE];
    ALL_TAC] THEN
   ASM_CASES_TAC `p = 1` THENL
   [ASM_REWRITE_TAC [prime_one; NOT_EXISTS_THM] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `!i j. ~divides (snth ps i) (snth ps (i + j + 1))`
      (MP_TAC o SPECL [`i : num`; `0`]) THEN
    ASM_REWRITE_TAC [one_divides];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [prime_divisor_lt] THEN
   ASM_REWRITE_TAC [] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `?i. p <= (snth ps i : num)`
      (MP_TAC o REWRITE_RULE [MINIMAL]) THENL
    [EXISTS_TAC `p : num` THEN
     SPEC_TAC (`p : num`, `p : num`) THEN
     UNDISCH_THEN `!i j. (snth ps i : num) <= snth ps j <=> i <= j`
       (fun th -> POP_ASSUM_LIST (K ALL_TAC) THEN ASSUME_TAC th) THEN
     INDUCT_TAC THENL
     [REWRITE_TAC [LE_0];
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `SUC (snth ps p)` THEN
      ASM_REWRITE_TAC [LE_SUC] THEN
      ASM_REWRITE_TAC [LE_SUC_LT; GSYM NOT_LE; LE_REFL]];
     ALL_TAC] THEN
    SPEC_TAC (`minimal i. p <= (snth ps i : num)`, `i : num`) THEN
    REWRITE_TAC [NOT_LE] THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `i : num` THEN
    ASM_REWRITE_TAC [GSYM LE_ANTISYM] THEN
    SUBGOAL_THEN `?n. p = n + 2` (CHOOSE_THEN SUBST_VAR_TAC) THENL
    [EXISTS_TAC `p - 2` THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC SUB_ADD THEN
     MP_TAC (SPEC `p : num` num_CASES) THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [TWO; LE_SUC] THEN
     REWRITE_TAC [ONE; LE_SUC_LT; LT_NZ] THEN
     STRIP_TAC THEN
     UNDISCH_TAC `p = SUC n` THEN
     ASM_REWRITE_TAC [GSYM ONE];
     ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`n : num`; `i : num`]) THEN
    BOOL_CASES_TAC `snth ps i <= n + 2` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [NOT_EX; GSYM ALL_MEM; mem_stake] THEN
    X_GEN_TAC `q : num` THEN
    DISCH_THEN (X_CHOOSE_THEN `j : num` STRIP_ASSUME_TAC) THEN
    POP_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC (TAUT `!x y. y /\ (y ==> x) ==> x /\ y`) THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_THEN `!p'. p' < n + 2 ==> (prime p' <=> (?i. snth ps i = p'))`
      (MP_TAC o SPEC `snth ps j : num`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `j : num` THEN
    REFL_TAC;
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
   X_GEN_TAC `q : num` THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `q : num`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `j : num` SUBST_VAR_TAC) THEN
   UNDISCH_THEN `!i j. (snth ps i : num) <= snth ps j <=> i <= j`
     (MP_TAC o SPECL [`i : num`; `j : num`]) THEN
   ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   REWRITE_TAC [LT_EXISTS; ADD1] THEN
   DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC);;

export_thm primes_equiv_test;;

(* ------------------------------------------------------------------------- *)
(* Definition of the sieve of Eratosthenes.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-sieve-def";;

let (is_counters_sieve_nil,is_counters_sieve_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!n i. is_counters_sieve n i [] <=> T) /\
     (!n i pkj ps.
        is_counters_sieve n i (CONS pkj ps) <=>
        let (p,(k,j)) = pkj in
        (~(p = 0) /\
         (k + i) MOD p = n MOD p /\
         is_counters_sieve n (i + j) ps))` in
  let (nil,cons) = CONJ_PAIR def in
  let nil' = REWRITE_RULE [] nil in
  let cons' = prove
    (`!n i p k j ps.
        is_counters_sieve n i (CONS (p,(k,j)) ps) <=>
        ~(p = 0) /\
        (k + i) MOD p = n MOD p /\
        is_counters_sieve n (i + j) ps`,
     REPEAT GEN_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV cons)) THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF]) in
  (nil',cons');;

export_thm is_counters_sieve_nil;;
export_thm is_counters_sieve_cons;;

let is_counters_sieve_def =
    CONJ is_counters_sieve_nil is_counters_sieve_cons;;

let is_sieve_def = new_definition
  `!n ps.
     is_sieve (n,ps) <=>
     ~(n = 0) /\
     MAP FST ps = primes_below (n + 1) /\
     is_counters_sieve n 0 ps`;;

export_thm is_sieve_def;;

let sieve_exists = prove
  (`?n_ps. is_sieve n_ps`,
   EXISTS_TAC `(1, ([] : (num # (num # num)) list))` THEN
   REWRITE_TAC
     [is_sieve_def; is_counters_sieve_def; NOT_SUC; ONE; ADD_CLAUSES] THEN
   REWRITE_TAC [GSYM ONE; GSYM TWO; MAP; primes_below_two]);;

let (mk_dest_sieve,dest_mk_sieve) =
  let tybij =
    new_type_definition
      "sieve" ("mk_sieve","dest_sieve") sieve_exists in
  CONJ_PAIR tybij;;

export_thm mk_dest_sieve;;
export_thm dest_mk_sieve;;

let sieve_tybij = CONJ mk_dest_sieve dest_mk_sieve;;

let init_sieve_def = new_definition
    `init_sieve = mk_sieve (1,[])`;;

export_thm init_sieve_def;;

let max_sieve_def = new_definition
  `!s. max_sieve s = FST (dest_sieve s)`;;

export_thm max_sieve_def;;

let primes_sieve_def = new_definition
  `!s. primes_sieve s = MAP FST (SND (dest_sieve s))`;;

export_thm primes_sieve_def;;

let (inc_counters_sieve_nil,inc_counters_sieve_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!n i. inc_counters_sieve n i [] = (T, [(n,(0,0))])) /\
     (!n i pkj ps.
        inc_counters_sieve n i (CONS pkj ps) =
        let (p,(k,j)) = pkj in
        let k' = (k + i) MOD p in
        let j' = j + i in
        if k' = 0 then (F, CONS (p,(0,j')) ps) else
        let (b,ps') = inc_counters_sieve n j' ps in
        (b, CONS (p,(k',0)) ps'))` in
  let (nil,cons) = CONJ_PAIR def in
  let cons' = prove
    (`!n i p k j ps.
        inc_counters_sieve n i (CONS (p,(k,j)) ps) =
        let k' = (k + i) MOD p in
        let j' = j + i in
        if k' = 0 then (F, CONS (p,(0,j')) ps) else
        let (b,ps') = inc_counters_sieve n j' ps in
        (b, CONS (p,(k',0)) ps')`,
     REPEAT GEN_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV cons)) THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF]) in
  (nil,cons');;

export_thm inc_counters_sieve_nil;;
export_thm inc_counters_sieve_cons;;

let inc_sieve_def = new_definition
  `!s.
     inc_sieve s =
     let (n,ps) = dest_sieve s in
     let n' = n + 1 in
     let (b,ps') = inc_counters_sieve n' 1 ps in
     (b, mk_sieve (n',ps'))`;;

export_thm inc_sieve_def;;

let next_sieve_exists = prove
 (`?fn. !s.
     fn s =
     let (b,s') = inc_sieve s in
     if b then (max_sieve s', s')
     else fn s'`,
  MP_TAC
   (ISPECL
      [`\s : sieve.
          let (b,s') = inc_sieve s in
          ~b`;
       `\s : sieve.
          let (b,s') = inc_sieve s in
          s'`;
       `\s : sieve.
          let (b,s') = inc_sieve s in
          (max_sieve s', s')`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `fn : sieve -> num # sieve`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `fn : sieve -> num # sieve` THEN
  GEN_TAC THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [] THEN
  PAIR_CASES_TAC `inc_sieve s` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool`
        (X_CHOOSE_THEN `s' : sieve` ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC []);;

let next_sieve_def =
  new_specification ["next_sieve"] next_sieve_exists;;

export_thm next_sieve_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the sieve of Eratosthenes.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-sieve-thm";;

let inc_counters_sieve_def =
    CONJ inc_counters_sieve_nil inc_counters_sieve_cons;;

export_thm inc_counters_sieve_def;;

let inc_sieve_src = prove
 (`inc_sieve =
   \s.
     let (n,ps) = dest_sieve s in
     let n' = n + 1 in
     let (b,ps') = inc_counters_sieve n' 1 ps in
     (b, mk_sieve (n',ps'))`,
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `s : sieve` THEN
  REWRITE_TAC [inc_sieve_def]);;

export_thm inc_sieve_src;;

let sieve_cases = prove
  (`!s. ?n ps. is_sieve (n,ps) /\ s = mk_sieve (n,ps)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (dest_sieve s)` THEN
   EXISTS_TAC `SND (dest_sieve s)` THEN
   REWRITE_TAC [sieve_tybij]);;

let dest_sieve_cases = prove
  (`!s. ?n ps.
      is_sieve (n,ps) /\ s = mk_sieve (n,ps) /\
      dest_sieve s = (n,ps)`,
   GEN_TAC THEN
   MP_TAC (SPEC `s : sieve` sieve_cases) THEN
   REWRITE_TAC [sieve_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ps : (num # (num # num)) list` THEN
   ASM_REWRITE_TAC []);;

let mk_sieve_inj = prove
  (`!r r'. is_sieve r /\ is_sieve r' /\ mk_sieve r = mk_sieve r' ==> r = r'`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [sieve_tybij] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   ASM_REWRITE_TAC []);;

let dest_init_sieve = prove
  (`dest_sieve init_sieve = (1,[])`,
   REWRITE_TAC [init_sieve_def; GSYM dest_mk_sieve] THEN
   REWRITE_TAC
     [is_sieve_def; is_counters_sieve_def; NOT_SUC; ONE; ADD_CLAUSES] THEN
   REWRITE_TAC [GSYM ONE; GSYM TWO; MAP; primes_below_two]);;

let max_init_sieve = prove
  (`max_sieve init_sieve = 1`,
   REWRITE_TAC [max_sieve_def; dest_init_sieve]);;

export_thm max_init_sieve;;

let primes_sieve = prove
  (`!s. primes_sieve s = primes_below (max_sieve s + 1)`,
   GEN_TAC THEN
   MP_TAC (SPEC `s : sieve` dest_sieve_cases) THEN
   STRIP_TAC THEN
   UNDISCH_TAC `is_sieve (n,ps)` THEN
   ASM_REWRITE_TAC [primes_sieve_def; max_sieve_def; is_sieve_def] THEN
   STRIP_TAC);;

export_thm primes_sieve;;

let is_counters_sieve_suc = prove
  (`!n i ps.
      is_counters_sieve (SUC n) (SUC i) ps <=>
      is_counters_sieve n i ps`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`i : num`, `i : num`) THEN
   SPEC_TAC (`ps : (num # (num # num)) list`,
             `ps : (num # (num # num)) list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [is_counters_sieve_def];
    ALL_TAC] THEN
   GEN_TAC THEN
   PAIR_CASES_TAC `h : num # (num # num)` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num`
        (X_CHOOSE_THEN `kj : num # num` SUBST1_TAC)) THEN
   PAIR_CASES_TAC `kj : num # num` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `k : num`
        (X_CHOOSE_THEN `j : num` SUBST1_TAC)) THEN
   ASM_REWRITE_TAC [is_counters_sieve_def; ADD_CLAUSES] THEN
   POP_ASSUM (K ALL_TAC) THEN
   ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC SUC_INJ_MOD THEN
   FIRST_ASSUM ACCEPT_TAC);;

let invariant_inc_counters_sieve = prove
  (`!n i ps b ps'.
      is_counters_sieve n i ps /\
      inc_counters_sieve (SUC n) (SUC i) ps = (b,ps') ==>
      is_counters_sieve (SUC n) 0 ps' /\
      (b <=> ALL (\ (p,(k,j)). ~divides p (SUC n)) ps) /\
      (MAP FST ps' = APPEND (MAP FST ps) (if b then [SUC n] else []))`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC
      [inc_counters_sieve_def; PAIR_EQ; is_counters_sieve_def;
       ALL; MAP; APPEND] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [is_counters_sieve_def; MAP; ADD_0] THEN
    MP_TAC (SPEC `SUC n` MOD_REFL) THEN
    REWRITE_TAC [NOT_SUC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOD_0 THEN
    MATCH_ACCEPT_TAC NOT_SUC;
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   PAIR_CASES_TAC `h : num # (num # num)` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p : num`
        (X_CHOOSE_THEN `kj : num # num` SUBST1_TAC)) THEN
   PAIR_CASES_TAC `kj : num # num` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `k : num`
        (X_CHOOSE_THEN `j : num` SUBST1_TAC)) THEN
   REWRITE_TAC
     [inc_counters_sieve_def; is_counters_sieve_def;
      LET_DEF; LET_END_DEF; ALL] THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SUBGOAL_THEN `(k + SUC i) MOD p = SUC n MOD p` SUBST1_TAC THENL
   [REWRITE_TAC [ADD_CLAUSES] THEN
    REWRITE_TAC [ADD1] THEN
    MP_TAC (SPEC `p : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`p : num`; `SUC n`] divides_mod) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `j + SUC i = SUC (i + j)` SUBST1_TAC THENL
   [REWRITE_TAC [ADD_CLAUSES; SUC_INJ] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   COND_CASES_TAC THENL
   [PURE_REWRITE_TAC [PAIR_EQ] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [MAP; APPEND_NIL] THEN
    ASM_REWRITE_TAC
      [is_counters_sieve_def; ADD_CLAUSES;
       is_counters_sieve_suc] THEN
    MATCH_MP_TAC MOD_0 THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   PAIR_CASES_TAC `inc_counters_sieve (SUC n) (SUC (i + j)) t` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [PAIR_EQ] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC
     [MAP; APPEND; CONS_11; is_counters_sieve_def; ADD_0;
      CONJ_ASSOC'] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MOD_MOD_REFL THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `i + j : num` THEN
   ASM_REWRITE_TAC []);;

let inc_sieve = prove
  (`!s b s'.
      inc_sieve s = (b,s') ==>
      max_sieve s' = max_sieve s + 1 /\
      (b <=> prime (max_sieve s'))`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `s : sieve` dest_sieve_cases) THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `s' : sieve` dest_sieve_cases) THEN
   STRIP_TAC THEN
   REWRITE_TAC [inc_sieve_def; max_sieve_def] THEN
   ASM_REWRITE_TAC [GSYM ADD1; LET_DEF; LET_END_DEF] THEN
   PAIR_CASES_TAC `inc_counters_sieve (SUC n) 1 ps` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [PAIR_EQ] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   UNDISCH_TAC `is_sieve (n,ps)` THEN
   REWRITE_TAC [is_sieve_def] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`n : num`;
         `0`;
         `ps : (num # (num # num)) list`;
         `b : bool`;
         `b' : (num # (num # num)) list`]
      invariant_inc_counters_sieve) THEN
   ASM_REWRITE_TAC [GSYM ONE] THEN
   STRIP_TAC THEN
   POP_ASSUM (MP_TAC) THEN
   SUBGOAL_THEN `b <=> prime (SUC n)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC [primes_below_divides; NOT_SUC; ONE; SUC_INJ] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `ALL (\p. ~divides p (SUC n))
         (MAP FST (ps : (num # (num # num)) list))` THEN
    CONJ_TAC THENL
    [POP_ASSUM_LIST (K ALL_TAC) THEN
     REWRITE_TAC [ALL_MAP] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [FUN_EQ_THM] THEN
     X_GEN_TAC `pkj : num # (num # num)` THEN
     PAIR_CASES_TAC `pkj : num # (num # num)` THEN
     DISCH_THEN
       (X_CHOOSE_THEN `p : num`
          (X_CHOOSE_THEN `kj : num # num` SUBST1_TAC)) THEN
     PAIR_CASES_TAC `kj : num # num` THEN
     DISCH_THEN
       (X_CHOOSE_THEN `k : num`
          (X_CHOOSE_THEN `j : num` SUBST1_TAC)) THEN
     REWRITE_TAC [o_THM];
     AP_TERM_TAC THEN
     REWRITE_TAC [ADD1] THEN
     FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
   DISCH_THEN
     (ASSUME_TAC o REWRITE_RULE [GSYM ADD1; GSYM primes_below_suc]) THEN
   SUBGOAL_THEN `SUC n = n'` (fun th -> REWRITE_TAC [th]) THEN
   SUBGOAL_THEN `(SUC n, b') = (n', (ps' : (num # (num # num)) list))`
     MP_TAC THENL
   [MATCH_MP_TAC mk_sieve_inj THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [is_sieve_def; NOT_SUC; GSYM ADD1];
    ALL_TAC] THEN
   REWRITE_TAC [PAIR_EQ] THEN
   STRIP_TAC);;

export_thm inc_sieve;;

let first_sieve = prove
  (`?s.
      next_sieve init_sieve = (2,s) /\
      max_sieve s = 2`,
   EXISTS_TAC `mk_sieve (2,[(2,(0,0))])` THEN
   ONCE_REWRITE_TAC [next_sieve_def] THEN
   REWRITE_TAC
     [inc_sieve_def; dest_init_sieve; max_sieve_def; PAIR_EQ;
      inc_counters_sieve_def; LET_DEF; LET_END_DEF] THEN
   NUM_REDUCE_TAC THEN
   SUBGOAL_THEN `is_sieve (2,[(2,(0,0))])` MP_TAC THENL
   [REWRITE_TAC [is_sieve_def; is_counters_sieve_def; MAP] THEN
    NUM_REDUCE_TAC THEN
    REWRITE_TAC [primes_below_three];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [sieve_tybij] th]));;

let next_sieve = prove
  (`!s i n s'.
      max_sieve s = snth primes i /\
      next_sieve s = (n,s') ==>
      n = max_sieve s' /\
      n = snth primes (SUC i)`,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SUBGOAL_THEN `max_sieve s < snth primes (SUC i)`
     (CHOOSE_THEN MP_TAC o REWRITE_RULE [LT_EXISTS]) THENL
   [ASM_REWRITE_TAC [primes_mono_lt; SUC_LT];
    ALL_TAC] THEN
   SUBGOAL_THEN `snth primes i <= max_sieve s` MP_TAC THENL
   [ASM_REWRITE_TAC [LE_REFL];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [IMP_IMP; CONJ_ASSOC'] THEN
   SPEC_TAC (`s : sieve`, `s : sieve`) THEN
   SPEC_TAC (`d : num`, `d : num`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    STRIP_TAC THEN
    POP_ASSUM MP_TAC THEN
    ONCE_REWRITE_TAC [next_sieve_def] THEN
    PAIR_CASES_TAC `inc_sieve s` THEN
    DISCH_THEN
      (X_CHOOSE_THEN `b : bool`
         (X_CHOOSE_THEN `s'' : sieve` ASSUME_TAC)) THEN
    ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    MP_TAC
      (SPECL
         [`s : sieve`;
          `b : bool`;
          `s'' : sieve`]
         inc_sieve) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    SUBGOAL_THEN `prime (max_sieve s'') <=> T` SUBST1_TAC THENL
    [REWRITE_TAC [snth_primes] THEN
     EXISTS_TAC `SUC i` THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [GSYM ADD1; ADD_CLAUSES];
     ALL_TAC] THEN
    REWRITE_TAC [PAIR_EQ] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [GSYM ADD1; ADD_CLAUSES];
    ALL_TAC] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   PAIR_CASES_TAC `inc_sieve s` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `b : bool`
        (X_CHOOSE_THEN `s'' : sieve` ASSUME_TAC)) THEN
   EXISTS_TAC `s'' : sieve` THEN
   UNDISCH_TAC `next_sieve s = n,s'` THEN
   DISCH_THEN (MP_TAC o ONCE_REWRITE_RULE [next_sieve_def]) THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL
        [`s : sieve`;
         `b : bool`;
         `s'' : sieve`]
        inc_sieve) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   SUBGOAL_THEN `prime (max_sieve s'') <=> F` SUBST1_TAC THENL
   [ASM_REWRITE_TAC [snth_primes] THEN
    DISCH_THEN (X_CHOOSE_THEN `j : num` STRIP_ASSUME_TAC) THEN
    MP_TAC (SPEC `i < (j : num)` EXCLUDED_MIDDLE) THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    REWRITE_TAC [NOT_LT; GSYM LT_SUC_LE] THEN
    ONCE_REWRITE_TAC [GSYM primes_mono_lt] THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL] THEN
    REWRITE_TAC [ONE; LT_SUC; LT_0; ADD_CLAUSES] THEN
    ASM_REWRITE_TAC [LT_SUC_LE];
    ALL_TAC] THEN
   REWRITE_TAC [PAIR_EQ] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [GSYM ADD1; ADD_CLAUSES] THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [LT_SUC_LE]);;

let correct_sieve = prove
  (`sunfold next_sieve init_sieve = primes`,
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [sunfold] THEN
   MP_TAC first_sieve THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [GSYM snth_primes_zero] THEN
   CHOOSE_THEN SUBST1_TAC (REWRITE_RULE [LE_EXISTS] (SPEC `n : num` LE_0)) THEN
   REWRITE_TAC [IMP_IMP; CONJ_ASSOC'] THEN
   CONV_TAC (RAND_CONV (LAND_CONV (RAND_CONV (REWR_CONV ZERO_ADD)))) THEN
   SPEC_TAC (`0`, `i : num`) THEN
   SPEC_TAC (`s : sieve`, `s : sieve`) THEN
   SPEC_TAC (`d : num`, `d : num`) THEN
   INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC [snth_scons_zero; ADD_0];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [snth_scons_suc] THEN
   REWRITE_TAC [ADD_SUC; GSYM SUC_ADD] THEN
   ONCE_REWRITE_TAC [sunfold] THEN
   PAIR_CASES_TAC `next_sieve s` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n : num`
        (X_CHOOSE_THEN `s' : sieve` ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   MP_TAC
     (SPECL
        [`s : sieve`;
         `i : num`;
         `n : num`;
         `s' : sieve`]
        next_sieve) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm correct_sieve;;

let primes_src = GSYM correct_sieve;;

export_thm primes_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for prime numbers.                                         *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-haskell-src";;

export_thm mk_dest_sieve;;  (* Haskell *)
export_thm max_sieve_def;;  (* Haskell *)
export_thm init_sieve_def;;  (* Haskell *)
export_thm inc_counters_sieve_def;;  (* Haskell *)
export_thm inc_sieve_src;;  (* Haskell *)
export_thm next_sieve_def;;  (* Haskell *)
export_thm primes_src;;  (* Haskell *)

(* ------------------------------------------------------------------------- *)
(* Haskell tests for prime numbers.                                          *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-haskell-test";;

export_thm snth_primes_zero_test;;  (* Haskell *)
export_thm primes_mono_le;;  (* Haskell *)
export_thm primes_divides_inj_test;;  (* Haskell *)
export_thm primes_below_prime_test;;  (* Haskell *)

logfile_end ();;

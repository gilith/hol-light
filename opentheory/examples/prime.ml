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

(* ------------------------------------------------------------------------- *)
(* The sieve of Eratosthenes.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-prime-sieve-def";;

let (primes_mono,snth_primes) =
  let def = new_specification ["primes"]
              (MATCH_MP num_stream_exists large_prime) in
  CONJ_PAIR def;;

export_thm primes_mono;;
export_thm snth_primes;;

let primes_def = CONJ primes_mono snth_primes;;

let primes_up_to_def = new_definition
  `!n.
     primes_up_to n =
     stake primes (minimal i. n < snth primes i)`;;

export_thm primes_up_to_def;;

let (sieve_induct,sieve_recursion) =
  let (induct,recursion) = define_type
    "sieve = Sieve num ((num # (num # num)) list)" in
  let induct' = prove
    (`!p.
        (!n ps. p (Sieve n ps)) ==>
        !s. p s`,
     ACCEPT_TAC induct)
  and recursion' = prove
    (`!f.
        ?(fn : sieve -> A).
          (!n ps. fn (Sieve n ps) = f n ps)`,
     MATCH_ACCEPT_TAC recursion) in
  (induct',recursion');;

export_thm sieve_induct;;
export_thm sieve_recursion;;

let max_sieve_def = new_recursive_definition sieve_recursion
  `!n ps. max_sieve (Sieve n ps) = n`;;

export_thm max_sieve_def;;

let max_sieve_def = new_recursive_definition sieve_recursion
  `!n ps. max_sieve (Sieve n ps) = n`;;

export_thm max_sieve_def;;

let primes_sieve_def = new_recursive_definition sieve_recursion
  `!n ps. primes_sieve (Sieve n ps) = MAP FST ps`;;

export_thm primes_sieve_def;;

let (inc_counters_sieve_nil,inc_counters_sieve_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!n i. inc_counters_sieve n i [] = (T, [(n,(0,0))])) /\
     (!n i pkj ps.
        inc_counters_sieve n i (CONS pkj ps) =
        let (p,(k,j)) = pkj in
        let k' = (k + i) MOD p in
        let j' = j + i in
        if k' = 0 then (F, CONS (p,(k',j')) ps) else
        let (b,ps') = inc_counters_sieve n j' ps in
        (b, CONS (p,(k',0)) ps'))` in
  let (nil,cons) = CONJ_PAIR def in
  let cons' = prove
    (`!n i p k j ps.
        inc_counters_sieve n i (CONS (p,(k,j)) ps) =
        let k' = (k + i) MOD p in
        let j' = j + i in
        if k' = 0 then (F, CONS (p,(k',j')) ps) else
        let (b,ps') = inc_counters_sieve n j' ps in
        (b, CONS (p,(k',0)) ps')`,
     REPEAT GEN_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV cons)) THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF]) in
  (nil,cons');;

export_thm inc_counters_sieve_nil;;
export_thm inc_counters_sieve_cons;;

let inc_counters_sieve_def =
    CONJ inc_counters_sieve_nil inc_counters_sieve_cons;;

let inc_sieve_def = new_recursive_definition sieve_recursion
  `!n ps.
     inc_sieve (Sieve n ps) =
     let n' = n + 1 in
     let (b,ps') = inc_counters_sieve n' 1 ps in
     (b, Sieve n' ps')`;;

export_thm inc_sieve_def;;

let (inv_counters_sieve_nil,inv_counters_sieve_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!n i. inv_counters_sieve n i [] <=> T) /\
     (!n i pkj ps.
        inv_counters_sieve n i (CONS pkj ps) <=>
        let (p,(k,j)) = pkj in
        ((k + i) MOD p = n MOD p /\
         inv_counters_sieve n (i + j) ps))` in
  let (nil,cons) = CONJ_PAIR def in
  let nil' = REWRITE_RULE [] nil in
  let cons' = prove
    (`!n i p k j ps.
        inv_counters_sieve n i (CONS (p,(k,j)) ps) <=>
        (k + i) MOD p = n MOD p /\
        inv_counters_sieve n (i + j) ps`,
     REPEAT GEN_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV cons)) THEN
     REWRITE_TAC [LET_DEF; LET_END_DEF]) in
  (nil',cons');;

export_thm inv_counters_sieve_nil;;
export_thm inv_counters_sieve_cons;;

let inv_counters_sieve_def =
    CONJ inv_counters_sieve_nil inv_counters_sieve_cons;;

let inv_sieve_def = new_recursive_definition sieve_recursion
  `!n ps.
     inv_sieve (Sieve n ps) <=>
     ~(n = 0) /\
     MAP FST ps = primes_up_to n /\
     inv_counters_sieve n 0 ps`;;

export_thm inv_sieve_def;;

logfile "natural-prime-sieve-thm";;

let prime_primes = prove
  (`!i. prime (snth primes i)`,
   GEN_TAC THEN
   REWRITE_TAC [snth_primes] THEN
   EXISTS_TAC `i : num` THEN
   REFL_TAC);;

export_thm prime_primes;;

let snth_primes_0 = prove
  (`snth primes 0 = 2`,
   CHOOSE_THEN MP_TAC (REWRITE_RULE [snth_primes] prime_two) THEN
   NUM_CASES_TAC `i : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   MP_TAC (SPECL [`0`; `SUC n`] primes_mono) THEN
   ASM_REWRITE_TAC [LT_0; NOT_LT] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPEC `0` prime_primes) THEN
   SPEC_TAC (`snth primes 0`, `n : num`) THEN
   GEN_TAC THEN
   NUM_CASES_TAC `n : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [prime_zero];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [TWO; LE_SUC] THEN
   NUM_CASES_TAC `m : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [GSYM ONE; prime_one];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `n : num` SUBST1_TAC) THEN
   REWRITE_TAC [ONE; LE_SUC; LE_0]);;

export_thm snth_primes_0;;

let primes_up_to_0 = prove
  (`primes_up_to 0 = []`,
   REWRITE_TAC [primes_up_to_def] THEN
   SUBGOAL_THEN `(minimal i. 0 < snth primes i) = 0`
     (fun th -> REWRITE_TAC [th; stake_0]) THEN
   MATCH_MP_TAC MINIMAL_EQ THEN
   REWRITE_TAC [LT; snth_primes_0] THEN
   NUM_REDUCE_TAC);;

export_thm primes_up_to_0;;

(***
let primes_up_to_suc = prove
  (`!n.
      primes_up_to (SUC n) =
      APPEND (primes_up_to n) (if prime (SUC n) then [SUC n] else [])`,
   GEN_TAC THEN
   REWRITE_TAC [primes_up_to_def] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [snth_primes]) THEN
    STRIP_

let primes_up_to_1 = prove
  (`primes_up_to 1 = []`,
   REWRITE_TAC [primes_up_to_def] THEN
   SUBGOAL_THEN `(minimal i. 0 < snth primes i) = 0`
     (fun th -> REWRITE_TAC [th; stake_0]) THEN
   MATCH_MP_TAC MINIMAL_EQ THEN
   REWRITE_TAC [LT; snth_primes_0] THEN
   NUM_REDUCE_TAC);;

let inv_init_sieve = prove
  (`inv_sieve init_sieve`,
   REWRITE_TAC
     [inv_sieve_def; init_sieve_def; inv_counters_sieve_def]
***)

logfile_end ();;

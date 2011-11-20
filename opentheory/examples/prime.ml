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

let gcd_prime = prove
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

export_thm gcd_prime;;

(***
let prime_divides_mult_imp = prove
  (`!p m n. prime p /\ divides p (m * n) ==> divides p m \/ divides p n`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC [prime_zero];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [divides_mod_cond] THEN
   REWRITE_TAC [prime_def] THEN
   ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
   REWRITE_TAC [NOT_OR_THM] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `m MOD p`) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [NOT_IMP; NOT_OR_THM] THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC [divides_def]

let prime_divides_mult = prove
  (`!p m n. prime p ==> divides p (~(n = 1) ==> ?p. prime p /\ divides p n`,

export_thm prime_divides_mult;;
***)

(***
let prime_divisor = prove
  (`!n. ~(n = 1) ==> ?p. prime p /\ divides p n`,

export_thm prime_divisor;;

let large_prime = prove
  (`!n. ?p. n <= p /\ prime p`,

export_thm large_prime;;
***)

logfile_end ();;

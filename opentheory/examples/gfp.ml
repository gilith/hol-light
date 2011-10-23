(* ------------------------------------------------------------------------- *)
(* A parametric theory of GF(p).                                             *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* gfp *)
*)

(* The theory parameters *)

new_constant ("oddprime", `:num`);;

let oddprime_odd = new_axiom `ODD oddprime`;;

let oddprime_prime = new_axiom `prime oddprime`;;

logfile "gfp-def";;

(*PARAMETRIC
(* gfp-def *)
*)

let oddprime_nonzero = prove
  (`~(oddprime = 0)`,
   STRIP_TAC THEN
   MP_TAC oddprime_prime THEN
   ASM_REWRITE_TAC [prime_zero]);;

export_thm oddprime_nonzero;;

(*PARAMETRIC
let oddprime_nonzero = new_axiom
  `~(oddprime = 0)`;;
*)

(* Parametric theory instantiation: modular *)

loads "opentheory/examples/gfp-modular.ml";;

logfile "gfp-thm";;

(*PARAMETRIC
(* gfp-thm *)
*)

let oddprime_not_one = prove
  (`~(oddprime = 1)`,
   STRIP_TAC THEN
   MP_TAC oddprime_prime THEN
   ASM_REWRITE_TAC [prime_one]);;

export_thm oddprime_not_one;;

(*PARAMETRIC
let oddprime_not_one = new_axiom
  `~(oddprime = 1)`;;
*)

let oddprime_not_two = prove
  (`~(oddprime = 2)`,
   STRIP_TAC THEN
   MP_TAC oddprime_odd THEN
   ASM_REWRITE_TAC [ODD; TWO; ONE; EVEN]);;

export_thm oddprime_not_two;;

(*PARAMETRIC
let oddprime_not_two = new_axiom
  `~(oddprime = 2)`;;
*)

let one_lt_oddprime = prove
  (`1 < oddprime`,
   REWRITE_TAC [LT_LE; oddprime_not_one] THEN
   REWRITE_TAC [ONE; LE_SUC_LT] THEN
   REWRITE_TAC [LT_NZ; oddprime_nonzero]);;

export_thm one_lt_oddprime;;

(*PARAMETRIC
let one_lt_oddprime = new_axiom
  `1 < oddprime`;;
*)

let two_lt_oddprime = prove
  (`2 < oddprime`,
   REWRITE_TAC [LT_LE; oddprime_not_two] THEN
   REWRITE_TAC [TWO; LE_SUC_LT; one_lt_oddprime]);;

export_thm two_lt_oddprime;;

(*PARAMETRIC
let two_lt_oddprime = new_axiom
  `2 < oddprime`;;
*)

let one_mod_oddprime = prove
  (`1 MOD oddprime = 1`,
   MATCH_MP_TAC mod_lt_oddprime THEN
   ACCEPT_TAC one_lt_oddprime);;

export_thm one_mod_oddprime;;

(*PARAMETRIC
let one_mod_oddprime = new_axiom
  `1 MOD oddprime = 1`;;
*)

let two_mod_oddprime = prove
  (`2 MOD oddprime = 2`,
   MATCH_MP_TAC mod_lt_oddprime THEN
   ACCEPT_TAC two_lt_oddprime);;

export_thm two_mod_oddprime;;

(*PARAMETRIC
let two_mod_oddprime = new_axiom
  `2 MOD oddprime = 1`;;
*)

(***
let gfp_inverse_exists = prove
  (`!n : gfp. ~(n = num_to_gfp 0) ==> ?m. gfp_mult m n = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num n`] gcd_prime) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [oddprime_prime] THEN
    MP_TAC (SPECL [`oddprime`; `gfp_to_num n`] divides_mod) THEN
    REWRITE_TAC [oddprime_nonzero; gfp_to_num_mod_bound] THEN
    DISCH_THEN SUBST1_TAC THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~(n = num_to_gfp 0)` THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC gfp_to_num_inj THEN
    ASM_REWRITE_TAC [num_to_gfp_to_num]
    ...

(*PARAMETRIC
let gfp_inverse_exists = new_axiom
   `!n : gfp. ~(n = num_to_gfp 0) ==> ?m. gfp_mult m n = num_to_gfp 1`;;
*)

export_thm gfp_inverse_exists;;
***)

(***
logfile "gfp-inverse-def";;

(*PARAMETRIC
(* gfp-inverse-def *)
*)

let gfp_inverse_def =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inverse_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inverse"] th1;;

(*PARAMETRIC
new_constant ("gfp_inverse", `:gfp -> gfp`);;
*)

export_thm gfp_inverse_def;;
***)

logfile_end ();;

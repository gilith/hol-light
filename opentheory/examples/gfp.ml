(* ------------------------------------------------------------------------- *)
(* A parametric theory of GF(p).                                             *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* gfp *)
*)

(* The theory parameters *)

logfile "gfp-witness";;

let (oddprime_odd,oddprime_prime) =
  let def = new_definition `oddprime = 3` in
  let odd = prove
    (`ODD oddprime`,
     REWRITE_TAC [def] THEN
     NUM_REDUCE_TAC)
  and prime = prove
    (`prime oddprime`,
     REWRITE_TAC [def; prime_three]) in
  (odd,prime);;

export_thm oddprime_odd;;
export_thm oddprime_prime;;

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

let gfp_one_nonzero = prove
  (`~(num_to_gfp 1 = num_to_gfp 0)`,
   STRIP_TAC THEN
   SUBGOAL_THEN `1 MOD oddprime = 0 MOD oddprime` MP_TAC THENL
   [ONCE_REWRITE_TAC [GSYM num_to_gfp_to_num] THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [one_mod_oddprime; zero_mod_oddprime] THEN
    NUM_REDUCE_TAC]);;

export_thm gfp_one_nonzero;;

(*PARAMETRIC
let gfp_one_nonzero = new_axiom
   `~(num_to_gfp 1 = num_to_gfp 0)`;;
*)

logfile "gfp-inverse-def";;

(*PARAMETRIC
(* gfp-inverse-def *)
*)

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
    ASM_REWRITE_TAC [num_to_gfp_to_num; zero_mod_oddprime];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num n`] egcd_exists) THEN
   POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [DIST_CASES] THEN
   STRIP_TAC THENL
   [EXISTS_TAC `num_to_gfp t` THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_to_num_to_gfp)))) THEN
    REWRITE_TAC [GSYM num_to_gfp_mult] THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [num_to_gfp_add; num_to_gfp_mult] THEN
    REWRITE_TAC [num_to_gfp_oddprime; gfp_mult_right_zero; gfp_add_left_zero];
    EXISTS_TAC `gfp_neg (num_to_gfp t)` THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_to_num_to_gfp)))) THEN
    ONCE_REWRITE_TAC
      [GSYM (SPEC `gfp_neg (num_to_gfp 1)` gfp_add_right_cancel)] THEN
    REWRITE_TAC [gfp_mult_left_neg; gfp_neg_add; gfp_add_right_neg] THEN
    REWRITE_TAC [GSYM num_to_gfp_mult; GSYM num_to_gfp_add] THEN
    POP_ASSUM SUBST1_TAC THEN
    REWRITE_TAC
      [num_to_gfp_mult; num_to_gfp_oddprime; gfp_mult_right_zero;
       gfp_neg_zero]]);;

let gfp_mult_left_inverse =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inverse_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inverse"] th1;;

export_thm gfp_mult_left_inverse;;

(*PARAMETRIC
new_constant ("gfp_inverse", `:gfp -> gfp`);;

let gfp_mult_left_inverse = new_axiom
   `!n. ~(n = num_to_gfp 0) ==> gfp_mult (gfp_inverse n) n = num_to_gfp 1`;;
*)

logfile "gfp-inverse-thm";;

let gfp_mult_right_inverse = prove
  (`!n. ~(n = num_to_gfp 0) ==> gfp_mult n (gfp_inverse n) = num_to_gfp 1`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_ACCEPT_TAC gfp_mult_left_inverse);;

export_thm gfp_mult_right_inverse;;

(*PARAMETRIC
let gfp_mult_right_inverse = prove
   `!n. ~(n = num_to_gfp 0) ==> gfp_mult n (gfp_inverse n) = num_to_gfp 1`;;
*)

let gfp_mult_left_cancel = prove
  (`!x y z. gfp_mult x y = gfp_mult x z <=> x = num_to_gfp 0 \/ y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `x = num_to_gfp 0` THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [GSYM gfp_mult_left_one] THEN
    MP_TAC (SPEC `x : gfp` gfp_mult_left_inverse) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    ASM_REWRITE_TAC [gfp_mult_assoc];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [gfp_mult_left_zero]]);;

export_thm gfp_mult_left_cancel;;

(*PARAMETRIC
let gfp_mult_left_cancel = new_axiom
   `!x y z. gfp_mult x y = gfp_mult x z <=> x = num_to_gfp 0 \/ y = z`;;
*)

let gfp_mult_right_cancel = prove
  (`!x y z. gfp_mult y x = gfp_mult z x <=> x = num_to_gfp 0 \/ y = z`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   REWRITE_TAC [gfp_mult_left_cancel]);;

export_thm gfp_mult_right_cancel;;

(*PARAMETRIC
let gfp_mult_right_cancel = new_axiom
   `!x y z. gfp_mult y x = gfp_mult z x <=> x = num_to_gfp 0 \/ y = z`;;
*)

let gfp_mult_left_cancel_one = prove
  (`!x y. gfp_mult x y = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_mult_right_one)))) THEN
   REWRITE_TAC [gfp_mult_left_cancel]);;

export_thm gfp_mult_left_cancel_one;;

(*PARAMETRIC
let gfp_mult_left_cancel_one = new_axiom
   `!x y. gfp_mult x y = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`;;
*)

let gfp_mult_right_cancel_one = prove
  (`!x y. gfp_mult y x = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_ACCEPT_TAC gfp_mult_left_cancel_one);;

export_thm gfp_mult_right_cancel_one;;

(*PARAMETRIC
let gfp_mult_right_cancel_one = new_axiom
   `!x y. gfp_mult y x = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`;;
*)

let gfp_inverse_nonzero = prove
  (`!x. ~(x = num_to_gfp 0) ==> ~(gfp_inverse x = num_to_gfp 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_mult_left_inverse) THEN
   ASM_REWRITE_TAC [gfp_mult_left_zero; gfp_one_nonzero]);;

export_thm gfp_inverse_nonzero;;

(*PARAMETRIC
let gfp_inverse_nonzero = new_axiom
   `!x. ~(x = num_to_gfp 0) ==> ~(gfp_inverse x = num_to_gfp 0)`;;
*)

let gfp_inverse_inverse = prove
  (`!x. ~(x = num_to_gfp 0) ==> gfp_inverse (gfp_inverse x) = x`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_inverse_nonzero) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `gfp_inverse x` gfp_mult_left_cancel) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   ASM_SIMP_TAC [gfp_mult_right_inverse; gfp_mult_left_inverse]);;

export_thm gfp_inverse_inverse;;

(*PARAMETRIC
let gfp_inverse_inverse = new_axiom
   `!x. ~(x = num_to_gfp 0) ==> gfp_inverse (gfp_inverse x) = x`;;
*)

let gfp_inverse_inj = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) /\
      gfp_inverse x = gfp_inverse y ==>
      x = y`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_inverse_inverse) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   MATCH_MP_TAC gfp_inverse_inverse THEN
   ASM_REWRITE_TAC []);;

export_thm gfp_inverse_inj;;

(*PARAMETRIC
let gfp_inverse_inj = new_axiom
   `!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) /\
      gfp_inverse x = gfp_inverse y ==>
      x = y`;;
*)

let gfp_inverse_one = prove
  (`gfp_inverse (num_to_gfp 1) = num_to_gfp 1`,
   MP_TAC (SPEC `num_to_gfp 1` gfp_mult_left_cancel) THEN
   REWRITE_TAC [gfp_one_nonzero] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   REWRITE_TAC [gfp_mult_right_one] THEN
   MATCH_MP_TAC gfp_mult_right_inverse THEN
   ACCEPT_TAC gfp_one_nonzero);;

export_thm gfp_inverse_one;;

(*PARAMETRIC
let gfp_inverse_one = new_axiom
   `gfp_inverse (num_to_gfp 1) = num_to_gfp 1`;;
*)

let gfp_inverse_is_one = prove
  (`!x.
      ~(x = num_to_gfp 0) /\ gfp_inverse x = num_to_gfp 1 ==>
      x = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gfp_inverse_inj THEN
   ASM_REWRITE_TAC [gfp_inverse_one; gfp_one_nonzero]);;

export_thm gfp_inverse_is_one;;

(*PARAMETRIC
let gfp_inverse_is_one = new_axiom
   `!x.
      ~(x = num_to_gfp 0) /\ gfp_inverse x = num_to_gfp 1 ==>
      x = num_to_gfp 1`;;
*)

let gfp_mult_eq_zero = prove
  (`!x y.
      gfp_mult x y = num_to_gfp 0 <=> x = num_to_gfp 0 \/ y = num_to_gfp 0`,
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `x = num_to_gfp 0` THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPEC `x : gfp` gfp_mult_left_cancel) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    ASM_REWRITE_TAC [gfp_mult_right_zero];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [gfp_mult_left_zero; gfp_mult_right_zero]]);;

export_thm gfp_mult_eq_zero;;

(*PARAMETRIC
let gfp_mult_eq_zero = new_axiom
   `!x y.
      gfp_mult x y = num_to_gfp 0 <=> x = num_to_gfp 0 \/ y = num_to_gfp 0`;;
*)

let gfp_inverse_mult = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      gfp_mult (gfp_inverse x) (gfp_inverse y) =
      gfp_inverse (gfp_mult x y)`,
   REPEAT STRIP_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV gfp_mult_comm)) THEN
   MP_TAC (SPEC `gfp_mult x y` gfp_mult_left_cancel) THEN
   ASM_REWRITE_TAC [gfp_mult_eq_zero] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `num_to_gfp 1` THEN
   STRIP_TAC THENL
   [ONCE_REWRITE_TAC [gfp_mult_assoc] THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_mult_assoc)))) THEN
    MP_TAC (SPEC `y : gfp` gfp_mult_right_inverse) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [gfp_mult_left_one] THEN
    MATCH_MP_TAC gfp_mult_right_inverse THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC gfp_mult_right_inverse THEN
    ASM_REWRITE_TAC [gfp_mult_eq_zero]]);;

export_thm gfp_inverse_mult;;

(*PARAMETRIC
let gfp_inverse_mult = new_axiom
   `!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      gfp_mult (gfp_inverse x) (gfp_inverse y) =
      gfp_inverse (gfp_mult x y)`;;
*)

logfile_end ();;

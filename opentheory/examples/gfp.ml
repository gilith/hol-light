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

logfile "gfp-div-def";;

(*PARAMETRIC
(* gfp-div-def *)
*)

let gfp_inv_exists = prove
  (`!x : gfp. ~(x = num_to_gfp 0) ==> ?y. gfp_mult y x = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num x`] gcd_prime) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [oddprime_prime] THEN
    MP_TAC (SPECL [`oddprime`; `gfp_to_num x`] divides_mod) THEN
    REWRITE_TAC [oddprime_nonzero; gfp_to_num_mod_bound] THEN
    DISCH_THEN SUBST1_TAC THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~(x = num_to_gfp 0)` THEN
    REWRITE_TAC [] THEN
    MATCH_MP_TAC gfp_to_num_inj THEN
    ASM_REWRITE_TAC [num_to_gfp_to_num; zero_mod_oddprime];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num x`] egcd_exists) THEN
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

let gfp_mult_left_inv =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inv_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inv"] th1;;

export_thm gfp_mult_left_inv;;

(*PARAMETRIC
new_constant ("gfp_inv", `:gfp -> gfp`);;

let gfp_mult_left_inv = new_axiom
   `!x. ~(x = num_to_gfp 0) ==> gfp_mult (gfp_inv x) x = num_to_gfp 1`;;
*)

let gfp_mult_left_div =
    let def = new_definition `!x y. gfp_div x y = gfp_mult x (gfp_inv y)` in
    prove
    (`!x y. ~(x = num_to_gfp 0) ==> gfp_div (gfp_mult x y) x = y`,
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [def] THEN
     CONV_TAC (LAND_CONV (REWR_CONV gfp_mult_comm)) THEN
     REWRITE_TAC [GSYM gfp_mult_assoc] THEN
     MP_TAC (SPEC `x : gfp` gfp_mult_left_inv) THEN
     ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST1_TAC THEN
      MATCH_ACCEPT_TAC gfp_mult_left_one]);;

export_thm gfp_mult_left_div;;

(*PARAMETRIC
new_constant ("gfp_div", `:gfp -> gfp -> gfp`);;

let gfp_mult_left_div = new_axiom
   `!x y. ~(x = num_to_gfp 0) ==> gfp_div (gfp_mult x y) x = y`;;
*)

logfile "gfp-div-thm";;

let gfp_mult_right_inv = prove
  (`!x. ~(x = num_to_gfp 0) ==> gfp_mult x (gfp_inv x) = num_to_gfp 1`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_ACCEPT_TAC gfp_mult_left_inv);;

export_thm gfp_mult_right_inv;;

(*PARAMETRIC
let gfp_mult_right_inv = prove
   `!x. ~(x = num_to_gfp 0) ==> gfp_mult x (gfp_inv x) = num_to_gfp 1`;;
*)

let gfp_mult_right_div = prove
  (`!x y. ~(x = num_to_gfp 0) ==> gfp_div (gfp_mult y x) x = y`,
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   ACCEPT_TAC gfp_mult_left_div);;

export_thm gfp_mult_right_div;;

(*PARAMETRIC
let gfp_mult_right_div = new_axiom
   `!x y. ~(x = num_to_gfp 0) ==> gfp_div (gfp_mult y x) x = y`;;
*)

let gfp_mult_left_cancel = prove
  (`!x y z. gfp_mult x y = gfp_mult x z <=> x = num_to_gfp 0 \/ y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `x = num_to_gfp 0` THEN
    ASM_REWRITE_TAC [] THEN
    ONCE_REWRITE_TAC [GSYM gfp_mult_left_one] THEN
    MP_TAC (SPEC `x : gfp` gfp_mult_left_inv) THEN
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

let gfp_inv_nonzero = prove
  (`!x. ~(x = num_to_gfp 0) ==> ~(gfp_inv x = num_to_gfp 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_mult_left_inv) THEN
   ASM_REWRITE_TAC [gfp_mult_left_zero; gfp_one_nonzero]);;

export_thm gfp_inv_nonzero;;

(*PARAMETRIC
let gfp_inv_nonzero = new_axiom
   `!x. ~(x = num_to_gfp 0) ==> ~(gfp_inv x = num_to_gfp 0)`;;
*)

let gfp_inv_inv = prove
  (`!x. ~(x = num_to_gfp 0) ==> gfp_inv (gfp_inv x) = x`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_inv_nonzero) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `gfp_inv x` gfp_mult_left_cancel) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   ASM_SIMP_TAC [gfp_mult_right_inv; gfp_mult_left_inv]);;

export_thm gfp_inv_inv;;

(*PARAMETRIC
let gfp_inv_inv = new_axiom
   `!x. ~(x = num_to_gfp 0) ==> gfp_inv (gfp_inv x) = x`;;
*)

let gfp_inv_inj = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) /\
      gfp_inv x = gfp_inv y ==>
      x = y`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_inv_inv) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   MATCH_MP_TAC gfp_inv_inv THEN
   ASM_REWRITE_TAC []);;

export_thm gfp_inv_inj;;

(*PARAMETRIC
let gfp_inv_inj = new_axiom
   `!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) /\
      gfp_inv x = gfp_inv y ==>
      x = y`;;
*)

let gfp_inv_one = prove
  (`gfp_inv (num_to_gfp 1) = num_to_gfp 1`,
   MP_TAC (SPEC `num_to_gfp 1` gfp_mult_left_cancel) THEN
   REWRITE_TAC [gfp_one_nonzero] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   REWRITE_TAC [gfp_mult_right_one] THEN
   MATCH_MP_TAC gfp_mult_right_inv THEN
   ACCEPT_TAC gfp_one_nonzero);;

export_thm gfp_inv_one;;

(*PARAMETRIC
let gfp_inv_one = new_axiom
   `gfp_inv (num_to_gfp 1) = num_to_gfp 1`;;
*)

let gfp_inv_is_one = prove
  (`!x.
      ~(x = num_to_gfp 0) /\ gfp_inv x = num_to_gfp 1 ==>
      x = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gfp_inv_inj THEN
   ASM_REWRITE_TAC [gfp_inv_one; gfp_one_nonzero]);;

export_thm gfp_inv_is_one;;

(*PARAMETRIC
let gfp_inv_is_one = new_axiom
   `!x.
      ~(x = num_to_gfp 0) /\ gfp_inv x = num_to_gfp 1 ==>
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

let gfp_inv_mult = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      gfp_mult (gfp_inv x) (gfp_inv y) =
      gfp_inv (gfp_mult x y)`,
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
    MP_TAC (SPEC `y : gfp` gfp_mult_right_inv) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [gfp_mult_left_one] THEN
    MATCH_MP_TAC gfp_mult_right_inv THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC gfp_mult_right_inv THEN
    ASM_REWRITE_TAC [gfp_mult_eq_zero]]);;

export_thm gfp_inv_mult;;

(*PARAMETRIC
let gfp_inv_mult = new_axiom
   `!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      gfp_mult (gfp_inv x) (gfp_inv y) =
      gfp_inv (gfp_mult x y)`;;
*)

logfile_end ();;

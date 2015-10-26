(* ========================================================================= *)
(* PARAMETRIC THEORY OF GF(p) FINITE FIELDS                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "natural-bits";
   "natural-fibonacci";
   "natural-divides";
   "natural-prime";
   "natural-fibonacci"];;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/gfp/gfp.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness.                                                *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-witness";;

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

(* ------------------------------------------------------------------------- *)
(* Definition of GF(p) finite fields.                                        *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-def";;

let oddprime_nonzero = prove
  (`~(oddprime = 0)`,
   STRIP_TAC THEN
   MP_TAC oddprime_prime THEN
   ASM_REWRITE_TAC [prime_zero]);;

export_thm oddprime_nonzero;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "modular";
   Import.interpretation = "opentheory/theories/gfp/gfp-def-modular.int";
   Import.theorem_renamer = Import.replace "modular" "gfp" o
                            Import.replace "modulus" "oddprime";
   Import.destination_theory = "gfp-def"};;

(* ------------------------------------------------------------------------- *)
(* Properties of GF(p) finite fields.                                        *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-thm";;

let oddprime_not_one = prove
  (`~(oddprime = 1)`,
   STRIP_TAC THEN
   MP_TAC oddprime_prime THEN
   ASM_REWRITE_TAC [prime_one]);;

export_thm oddprime_not_one;;

let oddprime_not_two = prove
  (`~(oddprime = 2)`,
   STRIP_TAC THEN
   MP_TAC oddprime_odd THEN
   ASM_REWRITE_TAC [ODD; TWO; ONE; EVEN]);;

export_thm oddprime_not_two;;

let one_lt_oddprime = prove
  (`1 < oddprime`,
   REWRITE_TAC [LT_LE; oddprime_not_one] THEN
   REWRITE_TAC [ONE; LE_SUC_LT] THEN
   REWRITE_TAC [LT_NZ; oddprime_nonzero]);;

export_thm one_lt_oddprime;;

let two_lt_oddprime = prove
  (`2 < oddprime`,
   REWRITE_TAC [LT_LE; oddprime_not_two] THEN
   REWRITE_TAC [TWO; LE_SUC_LT; one_lt_oddprime]);;

export_thm two_lt_oddprime;;

let one_mod_oddprime = prove
  (`1 MOD oddprime = 1`,
   MATCH_MP_TAC mod_lt_oddprime THEN
   ACCEPT_TAC one_lt_oddprime);;

export_thm one_mod_oddprime;;

let two_mod_oddprime = prove
  (`2 MOD oddprime = 2`,
   MATCH_MP_TAC mod_lt_oddprime THEN
   ACCEPT_TAC two_lt_oddprime);;

export_thm two_mod_oddprime;;

let oddprime_divides_mult = prove
  (`!m n.
      divides oddprime (m * n) <=> divides oddprime m \/ divides oddprime n`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC prime_divides_mult THEN
   ACCEPT_TAC oddprime_prime);;

export_thm oddprime_divides_mult;;

let oddprime_divides_one = prove
  (`~divides oddprime 1`,
   REWRITE_TAC [divides_one; oddprime_not_one]);;

export_thm oddprime_divides_one;;

let two_divides_oddprime = prove
  (`~divides 2 oddprime`,
   REWRITE_TAC [two_divides; NOT_EVEN; oddprime_odd]);;

export_thm two_divides_oddprime;;

let oddprime_divides_two = prove
  (`~divides oddprime 2`,
   REWRITE_TAC [divides_two; oddprime_not_one; oddprime_not_two]);;

export_thm oddprime_divides_two;;

let gfp_one_nonzero = prove
  (`~(num_to_gfp 1 = num_to_gfp 0)`,
   REWRITE_TAC [num_to_gfp_is_zero; oddprime_divides_one]);;

export_thm gfp_one_nonzero;;

let gfp_two_nonzero = prove
  (`~(num_to_gfp 2 = num_to_gfp 0)`,
   REWRITE_TAC [num_to_gfp_is_zero; oddprime_divides_two]);;

export_thm gfp_two_nonzero;;

let gfp_mult_eq_zero = prove
  (`!x y.
      gfp_mult x y = num_to_gfp 0 <=>
      x = num_to_gfp 0 \/ y = num_to_gfp 0`,
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [ALL_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC [gfp_mult_left_zero; gfp_mult_right_zero]] THEN
   MP_TAC (SPEC `x : gfp` gfp_to_num_to_gfp) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPEC `y : gfp` gfp_to_num_to_gfp) THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM num_to_gfp_mult] THEN
   REWRITE_TAC [num_to_gfp_is_zero; oddprime_divides_mult]);;

export_thm gfp_mult_eq_zero;;

let gfp_exp_eq_zero = prove
 (`!x n. gfp_exp x n = num_to_gfp 0 <=> x = num_to_gfp 0 /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `n : num` num_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [gfp_exp_zero; gfp_one_nonzero];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [NOT_SUC] THEN
  SPEC_TAC (`n' : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [gfp_exp_zero; gfp_exp_suc; gfp_mult_right_one];
   ONCE_REWRITE_TAC [gfp_exp_suc] THEN
   ASM_REWRITE_TAC [gfp_mult_eq_zero]]);;

export_thm gfp_exp_eq_zero;;

(* ------------------------------------------------------------------------- *)
(* Definition of GF(p) field division.                                       *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-def";;

let gfp_inv_exists = prove
  (`!x : gfp. ~(x = num_to_gfp 0) ==> ?y. gfp_mult y x = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num x`] coprime_prime_imp) THEN
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
   MP_TAC (SPECL [`gfp_to_num x`; `oddprime`] egcd_exists_nonzero2) THEN
   ANTS_TAC THENL
   [POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [CONTRAPOS_THM] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC gfp_to_num_to_gfp;
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   EXISTS_TAC `num_to_gfp s` THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_to_num_to_gfp)))) THEN
   REWRITE_TAC [GSYM num_to_gfp_mult] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC
     [num_to_gfp_add; num_to_gfp_mult; num_to_gfp_oddprime;
      gfp_mult_right_zero; gfp_add_left_zero]);;

let gfp_mult_left_inv =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inv_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inv"] th1;;

export_thm gfp_mult_left_inv;;

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

(* ------------------------------------------------------------------------- *)
(* Properties of GF(p) field division.                                       *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-thm";;

let gfp_mult_right_inv = prove
  (`!x. ~(x = num_to_gfp 0) ==> gfp_mult x (gfp_inv x) = num_to_gfp 1`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_ACCEPT_TAC gfp_mult_left_inv);;

export_thm gfp_mult_right_inv;;

let gfp_mult_right_div = prove
  (`!x y. ~(x = num_to_gfp 0) ==> gfp_div (gfp_mult y x) x = y`,
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   ACCEPT_TAC gfp_mult_left_div);;

export_thm gfp_mult_right_div;;

let gfp_mult_left_cancel_imp = prove
  (`!x y z. ~(x = num_to_gfp 0) /\ gfp_mult x y = gfp_mult x z ==> y = z`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM gfp_mult_left_one] THEN
   MP_TAC (SPEC `x : gfp` gfp_mult_left_inv) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   ASM_REWRITE_TAC [gfp_mult_assoc]);;

export_thm gfp_mult_left_cancel_imp;;

let gfp_mult_left_cancel = prove
  (`!x y z. gfp_mult x y = gfp_mult x z <=> x = num_to_gfp 0 \/ y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_CASES_TAC `x = num_to_gfp 0` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC gfp_mult_left_cancel_imp THEN
    EXISTS_TAC `x : gfp` THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [gfp_mult_left_zero]]);;

export_thm gfp_mult_left_cancel;;

let gfp_mult_right_cancel_imp = prove
  (`!x y z. ~(x = num_to_gfp 0) /\ gfp_mult y x = gfp_mult z x ==> y = z`,
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   ACCEPT_TAC gfp_mult_left_cancel_imp);;

export_thm gfp_mult_right_cancel_imp;;

let gfp_mult_right_cancel = prove
  (`!x y z. gfp_mult y x = gfp_mult z x <=> x = num_to_gfp 0 \/ y = z`,
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   ACCEPT_TAC gfp_mult_left_cancel);;

export_thm gfp_mult_right_cancel;;

let gfp_mult_left_cancel_one = prove
  (`!x y. gfp_mult x y = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM gfp_mult_right_one)))) THEN
   REWRITE_TAC [gfp_mult_left_cancel]);;

export_thm gfp_mult_left_cancel_one;;

let gfp_mult_right_cancel_one = prove
  (`!x y. gfp_mult y x = x <=> x = num_to_gfp 0 \/ y = num_to_gfp 1`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_ACCEPT_TAC gfp_mult_left_cancel_one);;

export_thm gfp_mult_right_cancel_one;;

let gfp_inv_nonzero = prove
  (`!x. ~(x = num_to_gfp 0) ==> ~(gfp_inv x = num_to_gfp 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : gfp` gfp_mult_left_inv) THEN
   ASM_REWRITE_TAC [gfp_mult_left_zero; gfp_one_nonzero]);;

export_thm gfp_inv_nonzero;;

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

let gfp_inv_one = prove
  (`gfp_inv (num_to_gfp 1) = num_to_gfp 1`,
   MP_TAC (SPEC `num_to_gfp 1` gfp_mult_left_cancel) THEN
   REWRITE_TAC [gfp_one_nonzero] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   REWRITE_TAC [gfp_mult_right_one] THEN
   MATCH_MP_TAC gfp_mult_right_inv THEN
   ACCEPT_TAC gfp_one_nonzero);;

export_thm gfp_inv_one;;

let gfp_inv_is_one = prove
  (`!x.
      ~(x = num_to_gfp 0) /\ gfp_inv x = num_to_gfp 1 ==>
      x = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gfp_inv_inj THEN
   ASM_REWRITE_TAC [gfp_inv_one; gfp_one_nonzero]);;

export_thm gfp_inv_is_one;;

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

let gfp_div_inv = prove
  (`!x y. ~(x = num_to_gfp 0) ==> gfp_div y x = gfp_mult y (gfp_inv x)`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `gfp_div (gfp_mult x (gfp_mult (gfp_inv x) y)) x` THEN
   STRIP_TAC THENL
   [AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC [gfp_mult_right_cancel_one; GSYM gfp_mult_assoc] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC gfp_mult_right_inv THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC gfp_mult_left_div THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm gfp_div_inv;;

let gfp_div_right_mult = prove
  (`!x y. ~(x = num_to_gfp 0) ==> gfp_mult (gfp_div y x) x = y`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`x : gfp`; `y : gfp`] gfp_div_inv) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [gfp_mult_assoc] THEN
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM gfp_mult_right_one))) THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC gfp_mult_left_inv THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm gfp_div_right_mult;;

let gfp_div_left_mult = prove
  (`!x y. ~(x = num_to_gfp 0) ==> gfp_mult x (gfp_div y x) = y`,
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   ACCEPT_TAC gfp_div_right_mult);;

export_thm gfp_div_left_mult;;

let gfp_div_nonzero = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      ~(gfp_div y x = num_to_gfp 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`x : gfp`; `y : gfp`] gfp_div_left_mult) THEN
   ASM_REWRITE_TAC [gfp_mult_right_zero]);;

export_thm gfp_div_nonzero;;

let gfp_div_one = prove
  (`!x. gfp_div x (num_to_gfp 1) = x`,
   GEN_TAC THEN
   CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM gfp_mult_right_one])) THEN
   MATCH_MP_TAC gfp_div_right_mult THEN
   ACCEPT_TAC gfp_one_nonzero);;

export_thm gfp_div_one;;

let gfp_inv_div = prove
  (`!x y.
      ~(x = num_to_gfp 0) /\ ~(y = num_to_gfp 0) ==>
      gfp_inv (gfp_div y x) = gfp_div x y`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`y : gfp`; `x : gfp`] gfp_div_inv) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`x : gfp`; `y : gfp`] gfp_div_inv) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`y : gfp`; `gfp_inv x`] gfp_inv_mult) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC gfp_inv_nonzero THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [gfp_mult_comm])) THEN
   REWRITE_TAC [gfp_mult_left_cancel] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC gfp_inv_inv THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm gfp_inv_div;;

let gfp_div_div = prove
  (`!x y z.
      ~(y = num_to_gfp 0) /\ ~(z = num_to_gfp 0) ==>
      gfp_div x (gfp_div y z) = gfp_div (gfp_mult x z) y`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`gfp_div y z`; `x : gfp`] gfp_div_inv) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC gfp_div_nonzero THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`z : gfp`; `y : gfp`] gfp_inv_div) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC gfp_mult_right_cancel_imp THEN
   EXISTS_TAC `y : gfp` THEN
   CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `gfp_mult x z` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC gfp_div_right_mult THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [gfp_mult_assoc; gfp_mult_left_cancel] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC gfp_div_right_mult THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm gfp_div_div;;

let gfp_mult_div = prove
  (`!x y.
      gfp_mult x y =
      if y = num_to_gfp 0 then num_to_gfp 0
      else gfp_div x (gfp_div (num_to_gfp 1) y)`,
   REPEAT STRIP_TAC THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [gfp_mult_right_zero];
    MP_TAC (SPECL [`x : gfp`; `num_to_gfp 1`; `y : gfp`] gfp_div_div) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [gfp_one_nonzero];
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [gfp_div_one]]]);;

export_thm gfp_mult_div;;

let gfp_exp_inv = prove
  (`!x n.
      ~(x = num_to_gfp 0) ==>
      gfp_exp (gfp_inv x) n = gfp_inv (gfp_exp x n)`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [gfp_exp_zero; gfp_inv_one];
    ASM_REWRITE_TAC [gfp_exp_suc] THEN
    MATCH_MP_TAC gfp_inv_mult THEN
    ASM_REWRITE_TAC [gfp_exp_eq_zero]]);;

export_thm gfp_exp_inv;;

(* ------------------------------------------------------------------------- *)
(* Definition of a GF(p) division algorithm based on gcd.                    *)
(*                                                                           *)
(* This is Algorithm 2.22 in Guide to Elliptic Curve Cryptography.           *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-gcd-def";;

let gfp_div_gcd_def =
  let th = prove
    (`?f. !u v x1 x2.
        f u v x1 x2 =
          if u = 1 then
            x1
          else if v = 1 then
            x2
          else if EVEN u then
            f (u DIV 2) v (gfp_div x1 (num_to_gfp 2)) x2
          else if EVEN v then
            f u (v DIV 2) x1 (gfp_div x2 (num_to_gfp 2))
          else if v <= u then
            f (u - v) v (gfp_sub x1 x2) x2
          else
            f u (v - u) x1 (gfp_sub x2 x1)`,
     MP_TAC
      (ISPECL
         [`\ (u, v, (x1 : gfp), (x2 : gfp)).
             ~(u = 1) /\ ~(v = 1)`;
          `\ (u, v, x1, x2).
             if EVEN u then
               (u DIV 2, v, gfp_div x1 (num_to_gfp 2), x2)
             else if EVEN v then
               (u, v DIV 2, x1, gfp_div x2 (num_to_gfp 2))
             else if v <= u then
               (u - v, v, gfp_sub x1 x2, x2)
             else
               (u, v - u, x1, gfp_sub x2 x1)`;
          `\ (u, (v : num), (x1 : gfp), (x2 : gfp)).
             if u = 1 then x1 else x2`]
         WF_REC_TAIL) THEN
     DISCH_THEN
       (X_CHOOSE_THEN `g : num # num # gfp # gfp -> gfp` STRIP_ASSUME_TAC o
        REWRITE_RULE [FORALL_PAIR_THM]) THEN
     EXISTS_TAC
       `\u v x1 x2. (g : num # num # gfp # gfp -> gfp) (u,v,x1,x2)` THEN
     REPEAT GEN_TAC THEN
     REWRITE_TAC [] THEN
     FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV) THEN
     ASM_CASES_TAC `u = 1` THEN
     ASM_REWRITE_TAC [] THEN
     ASM_CASES_TAC `v = 1` THEN
     ASM_REWRITE_TAC [] THEN
     ASM_CASES_TAC `EVEN u` THEN
     ASM_REWRITE_TAC [] THEN
     ASM_CASES_TAC `EVEN v` THEN
     ASM_REWRITE_TAC [] THEN
     ASM_CASES_TAC `v <= (u : num)` THEN
     ASM_REWRITE_TAC []) in
  new_specification ["gfp_div_gcd"] th;;

export_thm gfp_div_gcd_def;;

(* ------------------------------------------------------------------------- *)
(* Correctness of a GF(p) division algorithm based on gcd.                   *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-gcd-thm";;

let gfp_div_gcd_induction = prove
  (`!p : num -> num -> bool.
      (!v. p 1 v) /\
      (!u. ~(u = 1) ==> p u 1) /\
      (!u v.
         gcd (2 * u) v = 1 /\ ~(v = 1) /\ p u v ==>
         p (2 * u) v) /\
      (!u v.
         gcd u (2 * v) = 1 /\ ~(u = 1) /\ ODD u /\ p u v ==>
         p u (2 * v)) /\
      (!u v.
         gcd u v = 1 /\ EVEN u /\ ~(v = 1) /\ ODD v /\ p u v ==>
         p (v + u) v) /\
      (!u v.
         gcd u v = 1 /\ ~(u = 1) /\ ODD u /\ EVEN v /\ p u v ==>
         p u (u + v)) ==>
      (!u v. gcd u v = 1 ==> p u v)`,
   GEN_TAC THEN
   STRIP_TAC THEN
   REPEAT GEN_TAC THEN
   WF_INDUCT_TAC `(u : num) + v` THEN
   ASM_CASES_TAC `u = 1` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_CASES_TAC `v = 1` THENL
   [ASM_REWRITE_TAC [] THEN
    DISCH_THEN (K ALL_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `u = 0` THENL
   [ASM_REWRITE_TAC [zero_gcd];
    ALL_TAC] THEN
   ASM_CASES_TAC `v = 0` THENL
   [ASM_REWRITE_TAC [gcd_zero];
    ALL_TAC] THEN
   ASM_CASES_TAC `EVEN u` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [EVEN_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN `u' : num` SUBST_VAR_TAC) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LT_ADD_RCANCEL] THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM ONE_MULT))) THEN
     REWRITE_TAC [LT_MULT_RCANCEL] THEN
     NUM_REDUCE_TAC THEN
     UNDISCH_TAC `~(2 * u' = 0)` THEN
     REWRITE_TAC [MULT_EQ_0; NOT_OR_THM] THEN
     STRIP_TAC;
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [mult_coprime] THEN
     STRIP_TAC];
    ALL_TAC] THEN
   ASM_CASES_TAC `EVEN v` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [EVEN_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN `v' : num` SUBST_VAR_TAC) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [GSYM NOT_EVEN] THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LT_ADD_LCANCEL] THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM ONE_MULT))) THEN
     REWRITE_TAC [LT_MULT_RCANCEL] THEN
     NUM_REDUCE_TAC THEN
     UNDISCH_TAC `~(2 * v' = 0)` THEN
     REWRITE_TAC [MULT_EQ_0; NOT_OR_THM] THEN
     STRIP_TAC;
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [coprime_mult] THEN
     STRIP_TAC];
    ALL_TAC] THEN
   MP_TAC (SPECL [`u : num`; `v : num`] LE_CASES) THEN
   STRIP_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN `v' : num` SUBST_VAR_TAC) THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [EVEN_ADD; gcd_addl] THEN
    STRIP_TAC THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [GSYM NOT_EVEN] THEN
    POP_ASSUM MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL; LT_ADDR; LT_NZ];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (X_CHOOSE_THEN `u' : num` SUBST_VAR_TAC) THEN
    UNDISCH_TAC `~EVEN (v + u')` THEN
    ASM_REWRITE_TAC [EVEN_ADD; addl_gcd] THEN
    STRIP_TAC THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [GSYM NOT_EVEN] THEN
    POP_ASSUM MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [LT_ADD_RCANCEL; LT_ADDR; LT_NZ]]);;

export_thm gfp_div_gcd_induction;;

let gfp_div_gcd_recursion = prove
  (`!p : num -> num -> gfp -> gfp -> gfp -> bool.
      (!v x1 x2. p 1 v x1 x2 x1) /\
      (!u x1 x2. p u 1 x1 x2 x2) /\
      (!u v x1 x2 g.
         gcd (2 * u) v = 1 /\ p u v x1 x2 g ==>
         p (2 * u) v (gfp_mult (num_to_gfp 2) x1) x2 g) /\
      (!u v x1 x2 g.
         gcd u (2 * v) = 1 /\ p u v x1 x2 g ==>
         p u (2 * v) x1 (gfp_mult (num_to_gfp 2) x2) g) /\
      (!u v x1 x2 g.
         gcd u v = 1 /\ p u v x1 x2 g ==>
         p (v + u) v (gfp_add x2 x1) x2 g) /\
      (!u v x1 x2 g.
         gcd u v = 1 /\ p u v x1 x2 g ==>
         p u (u + v) x1 (gfp_add x1 x2) g) ==>
      (!u v x1 x2. gcd u v = 1 ==> p u v x1 x2 (gfp_div_gcd u v x1 x2))`,
   GEN_TAC THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
   ONCE_REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
   MATCH_MP_TAC gfp_div_gcd_induction THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [gfp_div_gcd_def];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [gfp_div_gcd_def] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [gfp_div_gcd_def] THEN
    ASM_CASES_TAC `2 * u = 1` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o EQF_INTRO) THEN
    ASM_REWRITE_TAC [EVEN_DOUBLE] THEN
    SUBGOAL_THEN `(2 * u) DIV 2 = u` SUBST1_TAC THENL
    [MATCH_MP_TAC DIV_MULT THEN
     NUM_REDUCE_TAC;
     ALL_TAC] THEN
    UNDISCH_THEN
      `!u v x1 (x2 : gfp) (g : gfp).
         gcd (2 * u) v = 1 /\ p u v x1 x2 g
         ==> p (2 * u) v (gfp_mult (num_to_gfp 2) x1) x2 g`
      (MP_TAC o SPECL [`u : num`; `v : num`; `gfp_div x1 (num_to_gfp 2)`]) THEN
    MP_TAC (SPECL [`num_to_gfp 2`; `x1 : gfp`] gfp_div_left_mult) THEN
    ANTS_TAC THENL
    [ACCEPT_TAC gfp_two_nonzero;
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [gfp_div_gcd_def] THEN
    ASM_REWRITE_TAC [EVEN_DOUBLE] THEN
    ASM_CASES_TAC `2 * v = 1` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o EQF_INTRO) THEN
    ASM_REWRITE_TAC [GSYM NOT_ODD] THEN
    SUBGOAL_THEN `(2 * v) DIV 2 = v` SUBST1_TAC THENL
    [MATCH_MP_TAC DIV_MULT THEN
     NUM_REDUCE_TAC;
     ALL_TAC] THEN
    UNDISCH_THEN
      `!u v (x1 : gfp) x2 (g : gfp).
         gcd u (2 * v) = 1 /\ p u v x1 x2 g
         ==> p u (2 * v) x1 (gfp_mult (num_to_gfp 2) x2) g`
      (MP_TAC o SPECL [`u : num`; `v : num`; `x1 : gfp`;
                       `gfp_div x2 (num_to_gfp 2)`]) THEN
    MP_TAC (SPECL [`num_to_gfp 2`; `x2 : gfp`] gfp_div_left_mult) THEN
    ANTS_TAC THENL
    [ACCEPT_TAC gfp_two_nonzero;
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [gfp_div_gcd_def] THEN
    ASM_REWRITE_TAC [EVEN_ADD] THEN
    ASM_CASES_TAC `v + u = 1` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o EQF_INTRO) THEN
    ASM_REWRITE_TAC [GSYM NOT_ODD; LE_ADD; ADD_SUB2] THEN
    UNDISCH_THEN
      `!u v x1 x2 (g : gfp).
         gcd u v = 1 /\ p u v x1 x2 g ==>
         p (v + u) v (gfp_add x2 x1) x2 g`
      (MP_TAC o SPECL [`u : num`; `v : num`; `gfp_sub x1 x2`; `x2 : gfp`]) THEN
    ONCE_REWRITE_TAC [gfp_add_comm] THEN
    REWRITE_TAC
      [gfp_sub_def; gfp_add_assoc; gfp_add_left_neg; gfp_add_right_zero] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC [gfp_div_gcd_def] THEN
    ASM_REWRITE_TAC [EVEN_ADD] THEN
    ASM_CASES_TAC `u + v = 1` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o EQF_INTRO) THEN
    ASM_REWRITE_TAC [GSYM NOT_ODD] THEN
    ASM_CASES_TAC `u + v <= (u : num)` THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN
     UNDISCH_TAC `gcd u v = 1` THEN
     POP_ASSUM (MP_TAC o CONV_RULE (RAND_CONV (REWR_CONV (GSYM ADD_0)))) THEN
     REWRITE_TAC [LE_ADD_LCANCEL; LE_ZERO] THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC [gcd_zero];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o EQF_INTRO) THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_THEN
      `!u v x1 x2 (g : gfp).
         gcd u v = 1 /\ p u v x1 x2 g ==>
         p u (u + v) x1 (gfp_add x1 x2) g`
      (MP_TAC o SPECL [`u : num`; `v : num`; `x1 : gfp`; `gfp_sub x2 x1`]) THEN
    ONCE_REWRITE_TAC [gfp_add_comm] THEN
    REWRITE_TAC
      [gfp_sub_def; gfp_add_assoc; gfp_add_left_neg; gfp_add_right_zero] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [ADD_SUB2]]);;

export_thm gfp_div_gcd_recursion;;

let gfp_div_gcd_invariant = prove
  (`!u v x1 x2.
      gcd u v = 1 /\
      gfp_mult (num_to_gfp u) x2 = gfp_mult (num_to_gfp v) x1 ==>
      (gfp_mult (num_to_gfp u) (gfp_div_gcd u v x1 x2) = x1 /\
       gfp_mult (num_to_gfp v) (gfp_div_gcd u v x1 x2) = x2)`,
   ONCE_REWRITE_TAC [IMP_CONJ] THEN
   MATCH_MP_TAC gfp_div_gcd_recursion THEN
   REWRITE_TAC [gfp_mult_left_one] THEN
   REPEAT CONJ_TAC THEN
   REPEAT GEN_TAC THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    REWRITE_TAC [num_to_gfp_mult; GSYM gfp_mult_assoc] THEN
    CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV gfp_mult_comm)))) THEN
    REWRITE_TAC [gfp_mult_assoc; gfp_mult_left_cancel; gfp_two_nonzero] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [num_to_gfp_mult; GSYM gfp_mult_assoc] THEN
    CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV gfp_mult_comm)))) THEN
    REWRITE_TAC [gfp_mult_assoc; gfp_mult_left_cancel; gfp_two_nonzero] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC
      [num_to_gfp_add; gfp_add_left_distrib; gfp_add_right_distrib;
       gfp_add_assoc; gfp_add_left_cancel] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
    [FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC
      [num_to_gfp_add; gfp_add_left_distrib; gfp_add_right_distrib;
       gfp_add_assoc; gfp_add_left_cancel] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
    [FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm gfp_div_gcd_invariant;;

let gfp_div_gcd = prove
  (`!x y.
      ~(y = num_to_gfp 0) ==>
      gfp_div x y = gfp_div_gcd (gfp_to_num y) oddprime x (num_to_gfp 0)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`y : gfp`; `x : gfp`] gfp_div_inv) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC gfp_mult_left_cancel_imp THEN
   EXISTS_TAC `y : gfp` THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`gfp_to_num y`; `oddprime`;
                  `x : gfp`; `num_to_gfp 0`] gfp_div_gcd_invariant) THEN
   ANTS_TAC THENL
   [REWRITE_TAC
      [gfp_mult_right_zero; num_to_gfp_oddprime; gfp_mult_left_zero] THEN
    ONCE_REWRITE_TAC [gcd_comm] THEN
    MATCH_MP_TAC coprime_prime_imp THEN
    ASM_REWRITE_TAC
      [oddprime_prime; GSYM num_to_gfp_is_zero; gfp_to_num_to_gfp];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o REWRITE_RULE [gfp_to_num_to_gfp] o CONJUNCT1) THEN
   ONCE_REWRITE_TAC [gfp_mult_comm] THEN
   REWRITE_TAC [gfp_mult_assoc; gfp_mult_left_cancel_one] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC gfp_mult_left_inv THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm gfp_div_gcd;;

(* ------------------------------------------------------------------------- *)
(* Definition of a GF(p) exponentiation algorithm based on division.         *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-exp-def";;

let (gfp_exp_div_nil,gfp_exp_div_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!b n d f p.
        gfp_exp_div b n d f p [] =
        if b then gfp_div n d else gfp_div d n) /\
     (!b n d f p h t.
        gfp_exp_div b n d f p (CONS h t) =
        let s = gfp_div p f in
        gfp_exp_div (~b) d (if h then gfp_div n s else n) s f t)` in
  CONJ_PAIR def;;

export_thm gfp_exp_div_nil;;
export_thm gfp_exp_div_cons;;

(* ------------------------------------------------------------------------- *)
(* Correctness of a GF(p) exponentiation algorithm based on division.        *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-div-exp-thm";;

let gfp_exp_div_invariant = prove
 (`!x n d f p l.
     ~(x = num_to_gfp 0) /\ ~(n = num_to_gfp 0) /\ ~(d = num_to_gfp 0) ==>
     (gfp_exp_div T n d (gfp_exp x f) (gfp_inv (gfp_exp x p)) l =
      gfp_mult (gfp_div n d) (gfp_exp x (decode_fib_dest f p l))) /\
     (gfp_exp_div F n d (gfp_inv (gfp_exp x f)) (gfp_exp x p) l =
      gfp_mult (gfp_div d n) (gfp_exp x (decode_fib_dest f p l)))`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [IMP_IMP] THEN
  SPEC_TAC (`p : num`, `p : num`) THEN
  SPEC_TAC (`f : num`, `f : num`) THEN
  SPEC_TAC (`d : gfp`, `d : gfp`) THEN
  SPEC_TAC (`n : gfp`, `n : gfp`) THEN
  SPEC_TAC (`l : bool list`, `l : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [gfp_exp_zero; decode_fib_dest_def; gfp_exp_div_nil; gfp_mult_right_one];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC
    [gfp_exp_suc; decode_fib_dest_def; gfp_exp_div_cons;
     LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
  SUBGOAL_THEN
    `gfp_div (gfp_inv (gfp_exp x p)) (gfp_exp x f) =
     gfp_inv (gfp_exp x (f + p))` SUBST1_TAC THENL
  [SUBGOAL_THEN
    `gfp_inv (gfp_exp x p) =
     gfp_mult (gfp_inv (gfp_exp x (f + p))) (gfp_exp x f)` SUBST1_TAC THENL
   [MATCH_MP_TAC gfp_mult_right_cancel_imp THEN
    EXISTS_TAC `gfp_exp x p` THEN
    ASM_REWRITE_TAC [gfp_exp_eq_zero] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `num_to_gfp 1` THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC gfp_mult_left_inv THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     MATCH_MP_TAC EQ_SYM THEN
     REWRITE_TAC [gfp_mult_assoc; gfp_exp_add] THEN
     MATCH_MP_TAC gfp_mult_left_inv THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero]];
    MATCH_MP_TAC gfp_mult_right_div THEN
    ASM_REWRITE_TAC [gfp_exp_eq_zero]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `gfp_div n (gfp_inv (gfp_exp x (f + p))) =
      gfp_mult n (gfp_exp x (f + p))` SUBST1_TAC THENL
   [MP_TAC (SPECL [`gfp_inv (gfp_exp x (f + p))`; `n : gfp`] gfp_div_inv) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC gfp_inv_nonzero THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [gfp_mult_left_cancel] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC gfp_inv_inv THEN
    ASM_REWRITE_TAC [gfp_exp_eq_zero];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL
     [`d : gfp`; `if h then gfp_mult n (gfp_exp x (f + p)) else n`;
      `f + p : num`; `f : num`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    BOOL_CASES_TAC `h : bool` THEN
    ASM_REWRITE_TAC [gfp_mult_eq_zero; gfp_exp_eq_zero];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
   BOOL_CASES_TAC `h : bool` THENL
   [ASM_REWRITE_TAC [] THEN
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM gfp_exp_add])) THEN
    REWRITE_TAC [GSYM gfp_mult_assoc; gfp_mult_right_cancel] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC gfp_mult_right_cancel_imp THEN
    EXISTS_TAC `d : gfp` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `gfp_mult n (gfp_exp x (f + p))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC gfp_div_right_mult THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC EQ_SYM THEN
     REWRITE_TAC [gfp_mult_assoc] THEN
     CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [gfp_mult_comm]))) THEN
     REWRITE_TAC [GSYM gfp_mult_assoc; gfp_mult_right_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC gfp_div_right_mult THEN
     FIRST_ASSUM ACCEPT_TAC];
    ASM_REWRITE_TAC []];
   SUBGOAL_THEN
     `gfp_div (gfp_exp x p) (gfp_inv (gfp_exp x f)) =
      gfp_exp x (f + p)` SUBST1_TAC THENL
   [MP_TAC (SPECL [`gfp_inv (gfp_exp x f)`; `gfp_exp x p`] gfp_div_inv) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC gfp_inv_nonzero THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    REWRITE_TAC [GSYM gfp_exp_add; gfp_mult_left_cancel] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC gfp_inv_inv THEN
    ASM_REWRITE_TAC [gfp_exp_eq_zero];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL
     [`d : gfp`; `if h then gfp_div n (gfp_exp x (f + p)) else n`;
      `f + p : num`; `f : num`]) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    BOOL_CASES_TAC `h : bool` THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC gfp_div_nonzero THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
   BOOL_CASES_TAC `h : bool` THENL
   [ASM_REWRITE_TAC [] THEN
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM gfp_exp_add])) THEN
    REWRITE_TAC [GSYM gfp_mult_assoc; gfp_mult_right_cancel] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC gfp_mult_left_cancel_imp THEN
    EXISTS_TAC `gfp_div n (gfp_exp x (f + p))` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC gfp_div_nonzero THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `d : gfp` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC gfp_div_left_mult THEN
     MATCH_MP_TAC gfp_div_nonzero THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     ALL_TAC] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `gfp_mult n (gfp_div d n)` THEN
    CONJ_TAC THENL
    [CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [gfp_mult_comm]))) THEN
     REWRITE_TAC [GSYM gfp_mult_assoc; gfp_mult_right_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC gfp_div_right_mult THEN
     ASM_REWRITE_TAC [gfp_exp_eq_zero];
     MATCH_MP_TAC gfp_div_left_mult THEN
     FIRST_ASSUM ACCEPT_TAC];
    ASM_REWRITE_TAC []]]);;

export_thm gfp_exp_div_invariant;;

let gfp_exp_div = prove
 (`!x n.
     gfp_exp x n =
     (if n = 0 then num_to_gfp 1
      else if x = num_to_gfp 0 then num_to_gfp 0
      else gfp_exp_div T (num_to_gfp 1) (num_to_gfp 1) x (num_to_gfp 1)
             (encode_fib n))`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [gfp_exp_zero];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [gfp_exp_eq_zero];
   ALL_TAC] THEN
  MP_TAC (SPECL [`x : gfp`; `num_to_gfp 1`; `num_to_gfp 1`; `1`; `0`;
                 `encode_fib n`] gfp_exp_div_invariant) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [gfp_one_nonzero];
   ALL_TAC] THEN
  DISCH_THEN
    (SUBST1_TAC o
     REWRITE_RULE [gfp_exp_zero; gfp_exp_suc; gfp_inv_one; gfp_exp_one] o
     CONJUNCT1) THEN
  REWRITE_TAC
    [gfp_div_one; gfp_mult_left_one; GSYM decode_fib_def; encode_decode_fib]);;

export_thm gfp_exp_div;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "gfp-hol-light-thm";;

export_theory_thm_names "gfp"
  ["gfp-def";
   "gfp-thm";
   "gfp-div-def";
   "gfp-div-thm";
   "gfp-div-gcd-def";
   "gfp-div-gcd-thm";
   "gfp-div-exp-def";
   "gfp-div-exp-thm"];;

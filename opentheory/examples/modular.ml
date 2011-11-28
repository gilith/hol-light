(* ------------------------------------------------------------------------- *)
(* A parametric theory of modular arithmetic.                                *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* modular *)
*)

(* The theory parameters *)

logfile "modular-witness";;

let modulus_nonzero =
  let def = new_definition `modulus = SUC 0` in
  prove
  (`~(modulus = 0)`,
   REWRITE_TAC [def; NOT_SUC]);;

export_thm modulus_nonzero;;

logfile "modular-def";;

(*PARAMETRIC
(* modular-def *)
*)

let mod_refl_modulus = prove
  (`modulus MOD modulus = 0`,
   MATCH_MP_TAC MOD_REFL THEN
   REWRITE_TAC [modulus_nonzero]);;

export_thm mod_refl_modulus;;

(*PARAMETRIC
let mod_refl_modulus = new_axiom
  `modulus MOD modulus = 0`;;
*)

let mod_lt_modulus = prove
  (`!n. n < modulus ==> n MOD modulus = n`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n:num`; `modulus:num`] MOD_LT) THEN
   ASM_REWRITE_TAC []);;

export_thm mod_lt_modulus;;

(*PARAMETRIC
let mod_lt_modulus = new_axiom
  `!n. n < modulus ==> n MOD modulus = n`;;
*)

let zero_mod_modulus = prove
  (`0 MOD modulus = 0`,
   MATCH_MP_TAC mod_lt_modulus THEN
   REWRITE_TAC [LT_NZ; modulus_nonzero]);;

export_thm zero_mod_modulus;;

(*PARAMETRIC
let zero_mod_modulus = new_axiom
  `0 MOD modulus = 0`;;
*)

let lt_mod_modulus = prove
  (`!n. n MOD modulus < modulus`,
   GEN_TAC THEN
   MP_TAC (SPECL [`n:num`; `modulus:num`] DIVISION) THEN
   COND_TAC THENL
   [REWRITE_TAC [modulus_nonzero];
    DISCH_THEN (ACCEPT_TAC o CONJUNCT2)]);;

export_thm lt_mod_modulus;;

(*PARAMETRIC
let lt_mod_modulus = new_axiom
  `!n. n MOD modulus < modulus`;;
*)

let mod_mod_refl_modulus = prove
  (`!n. n MOD modulus MOD modulus = n MOD modulus`,
   GEN_TAC THEN
   MP_TAC (SPECL [`n:num`; `modulus:num`] MOD_MOD_REFL) THEN
   COND_TAC THENL
   [REWRITE_TAC [modulus_nonzero];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_mod_refl_modulus;;

(*PARAMETRIC
let mod_mod_refl_modulus = new_axiom
  `!n. n MOD modulus MOD modulus = n MOD modulus`;;
*)

let mod_add_mod_modulus = prove
  (`!m n. (m MOD modulus + n MOD modulus) MOD modulus = (m + n) MOD modulus`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m:num`; `n:num`; `modulus:num`] MOD_ADD_MOD) THEN
   COND_TAC THENL
   [REWRITE_TAC [modulus_nonzero];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_add_mod_modulus;;

(*PARAMETRIC
let mod_add_mod_modulus = new_axiom
  `!m n. (m MOD modulus + n MOD modulus) MOD modulus = (m + n) MOD modulus`;;
*)

let mod_mult_mod_modulus = prove
  (`!m n. (m MOD modulus * n MOD modulus) MOD modulus = (m * n) MOD modulus`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m:num`; `modulus`; `n:num`] MOD_MULT_MOD2) THEN
   COND_TAC THENL
   [REWRITE_TAC [modulus_nonzero];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_mult_mod_modulus;;

(*PARAMETRIC
let mod_mult_mod_modulus = new_axiom
  `!m n. (m MOD modulus * n MOD modulus) MOD modulus = (m * n) MOD modulus`;;
*)

let divides_mod_modulus = prove
  (`!n. divides modulus n <=> n MOD modulus = 0`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`modulus`; `n:num`] divides_mod) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [modulus_nonzero];
    DISCH_THEN ACCEPT_TAC]);;

export_thm divides_mod_modulus;;

(*PARAMETRIC
let divides_mod_modulus = new_axiom
   `!n. divides modulus n <=> n MOD modulus = 0`;;
*)

let modular_equiv_def = new_definition
  `!x y. modular_equiv x y = x MOD modulus = y MOD modulus`;;

let modular_equiv_refl = prove
  (`!x. modular_equiv x x`,
   REWRITE_TAC [modular_equiv_def]);;

let modular_equiv_trans = prove
  (`!x y z. modular_equiv x y /\ modular_equiv y z ==> modular_equiv x z`,
   REWRITE_TAC [modular_equiv_def] THEN
   SIMP_TAC []);;

let modular_equiv_eq = prove
  (`!x y. modular_equiv x = modular_equiv y <=> x MOD modulus = y MOD modulus`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [modular_equiv_def] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (MP_TAC o SPEC `y:num`) THEN
    REWRITE_TAC [];
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

let modular_equiv_inj = prove
  (`!x y.
      x < modulus /\ y < modulus /\ modular_equiv x = modular_equiv y ==>
      x = y`,
   REWRITE_TAC [modular_equiv_eq] THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC [mod_lt_modulus]);;

let modular_equiv_add = prove
  (`!x1 x2 y1 y2.
      modular_equiv x1 x2 /\ modular_equiv y1 y2 ==>
      modular_equiv (x1 + y1) (x2 + y2)`,
   REWRITE_TAC [modular_equiv_def] THEN
   ONCE_REWRITE_TAC [GSYM mod_add_mod_modulus] THEN
   SIMP_TAC []);;

let modular_equiv_mult = prove
  (`!x1 x2 y1 y2.
      modular_equiv x1 x2 /\ modular_equiv y1 y2 ==>
      modular_equiv (x1 * y1) (x2 * y2)`,
   REWRITE_TAC [modular_equiv_def] THEN
   ONCE_REWRITE_TAC [GSYM mod_mult_mod_modulus] THEN
   SIMP_TAC []);;

let (modular_abs_rep,modular_rep_abs) = define_quotient_type
  "modular" ("modular_from_class","modular_to_class") `modular_equiv`;;

(*PARAMETRIC
new_type ("modular",0);;
*)

let num_to_modular_def = new_definition
  `!x. num_to_modular x = modular_from_class (modular_equiv x)`;;

(*PARAMETRIC
new_constant ("num_to_modular", `:num -> modular`);;
*)

let modular_rep_abs_surj = prove
  (`!x. (?y. modular_to_class x = modular_equiv y)`,
   GEN_TAC THEN
   REWRITE_TAC [modular_rep_abs; modular_abs_rep]);;

let modular_rep_abs_triv = prove
  (`!x.
      modular_to_class (modular_from_class (modular_equiv x)) =
      modular_equiv x`,
   GEN_TAC THEN
   REWRITE_TAC [GSYM modular_rep_abs] THEN
   EXISTS_TAC `x:num` THEN
   REFL_TAC);;

let modular_from_class_inj = prove
  (`!x y.
      modular_from_class (modular_equiv x) =
      modular_from_class (modular_equiv y) ==>
      modular_equiv x = modular_equiv y`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM modular_rep_abs_triv] THEN
   ASM_REWRITE_TAC []);;

let modular_to_num_exists = prove
  (`!x. ?y. y < modulus /\ num_to_modular y = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM modular_abs_rep] THEN
   REWRITE_TAC [num_to_modular_def] THEN
   MP_TAC (SPEC `x:modular` modular_rep_abs_surj) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `y MOD modulus` THEN
   REWRITE_TAC [lt_mod_modulus; modular_abs_rep] THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   REWRITE_TAC [modular_equiv_def; mod_mod_refl_modulus]);;

let modular_to_num_def = new_specification ["modular_to_num"]
  (REWRITE_RULE [SKOLEM_THM] modular_to_num_exists);;

(*PARAMETRIC
new_constant ("modular_to_num", `:modular -> num`);;
*)

let modular_to_num_to_modular = prove
  (`!x. num_to_modular (modular_to_num x) = x`,
   REWRITE_TAC [modular_to_num_def]);;

export_thm modular_to_num_to_modular;;

(*PARAMETRIC
let modular_to_num_to_modular = new_axiom
  `!x. num_to_modular (modular_to_num x) = x`;;
*)

let num_to_modular_inj = prove
  (`!x y.
      x < modulus /\ y < modulus /\ num_to_modular x = num_to_modular y ==>
      x = y`,
   REWRITE_TAC [num_to_modular_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC modular_equiv_inj THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC modular_from_class_inj THEN
   ASM_REWRITE_TAC []);;

export_thm num_to_modular_inj;;

(*PARAMETRIC
let num_to_modular_inj = new_axiom
   `!x y.
      x < modulus /\ y < modulus /\ num_to_modular x = num_to_modular y ==>
      x = y`;;
*)

let num_to_modular_to_num = prove
  (`!x. modular_to_num (num_to_modular x) = x MOD modulus`,
   GEN_TAC THEN
   MATCH_MP_TAC num_to_modular_inj THEN
   SIMP_TAC [modular_to_num_def; modular_to_num_to_modular; lt_mod_modulus] THEN
   REWRITE_TAC [num_to_modular_def] THEN
   AP_TERM_TAC THEN
   SIMP_TAC [modular_equiv_eq; mod_mod_refl_modulus]);;

export_thm num_to_modular_to_num;;

(*PARAMETRIC
let num_to_modular_to_num = new_axiom
  `!x. modular_to_num (num_to_modular x) = x MOD modulus`;;
*)

let (modular_add_def,modular_add_lift) = lift_function
  modular_rep_abs (modular_equiv_refl,modular_equiv_trans)
  "modular_add" modular_equiv_add;;

(*PARAMETRIC
new_constant ("modular_add", `:modular -> modular -> modular`);;
*)

let num_to_modular_add =
  GEN_ALL (REWRITE_RULE [GSYM num_to_modular_def] modular_add_lift);;

export_thm num_to_modular_add;;

(*PARAMETRIC
let num_to_modular_add = new_axiom
  `!x1 y1.
     num_to_modular (x1 + y1) =
     modular_add (num_to_modular x1) (num_to_modular y1)`;;
*)

let (modular_mult_def,modular_mult_lift) = lift_function
  modular_rep_abs (modular_equiv_refl,modular_equiv_trans)
  "modular_mult" modular_equiv_mult;;

(*PARAMETRIC
new_constant ("modular_mult", `:modular -> modular -> modular`);;
*)

let num_to_modular_mult =
  GEN_ALL (REWRITE_RULE [GSYM num_to_modular_def] modular_mult_lift);;

export_thm num_to_modular_mult;;

(*PARAMETRIC
let num_to_modular_mult = new_axiom
  `!x1 y1.
     num_to_modular (x1 * y1) =
     modular_mult (num_to_modular x1) (num_to_modular y1)`;;
*)

let modular_neg_def = new_definition
  `!x. modular_neg x = num_to_modular (modulus - modular_to_num x)`;;

(*PARAMETRIC
new_constant ("modular_neg", `:modular -> modular`);;
*)

export_thm modular_neg_def;;

(*PARAMETRIC
let modular_neg_def = new_axiom
  `!x. modular_neg x = num_to_modular (modulus - modular_to_num x)`;;
*)

let modular_sub_def = new_definition
  `!x y. modular_sub x y = modular_add x (modular_neg y)`;;

(*PARAMETRIC
new_constant ("modular_sub", `:modular -> modular -> modular`);;
*)

export_thm modular_sub_def;;

(*PARAMETRIC
let modular_sub_def = new_axiom
  `!x y. modular_sub x y = modular_add x (modular_neg y)`;;
*)

let modular_le_def = new_definition
  `!x y. modular_le x y = modular_to_num x <= modular_to_num y`;;

(*PARAMETRIC
new_constant ("modular_le", `:modular -> modular -> bool`);;
*)

export_thm modular_le_def;;

(*PARAMETRIC
let modular_le_def = new_axiom
  `!x y. modular_le x y = modular_to_num x <= modular_to_num y`;;
*)

let modular_lt_def = new_definition
  `!x y. modular_lt x y = ~(modular_le y x)`;;

(*PARAMETRIC
new_constant ("modular_lt", `:modular -> modular -> bool`);;
*)

export_thm modular_lt_def;;

(*PARAMETRIC
let modular_lt_def = new_axiom
  `!x y. modular_lt x y = ~(modular_le y x)`;;
*)

logfile "modular-thm";;

(*PARAMETRIC
(* modular-thm *)
*)

let modular_to_num_inj = prove
  (`!x y. modular_to_num x = modular_to_num y ==> x = y`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM modular_to_num_to_modular] THEN
   ASM_REWRITE_TAC []);;

export_thm modular_to_num_inj;;

(*PARAMETRIC
let modular_to_num_inj = new_axiom
  `!x y. modular_to_num x = modular_to_num y ==> x = y`;;
*)

let num_to_modular_eq = prove
  (`!x y.
      num_to_modular x = num_to_modular y <=> x MOD modulus = y MOD modulus`,
   REWRITE_TAC [GSYM num_to_modular_to_num] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    MATCH_MP_TAC modular_to_num_inj THEN
    ASM_REWRITE_TAC []]);;

export_thm num_to_modular_eq;;

(*PARAMETRIC
let num_to_modular_eq = new_axiom
   `!x y.
      num_to_modular x = num_to_modular y <=> x MOD modulus = y MOD modulus`;;
*)

let num_to_modular_is_zero = prove
  (`!x. num_to_modular x = num_to_modular 0 <=> divides modulus x`,
   GEN_TAC THEN
   REWRITE_TAC [num_to_modular_eq; divides_mod_modulus; zero_mod_modulus]);;

export_thm num_to_modular_is_zero;;

(*PARAMETRIC
let num_to_modular_is_zero = new_axiom
   `!x. num_to_modular x = num_to_modular 0 <=> divides modulus x`;;
*)

let modular_to_num_bound = prove
  (`!x. modular_to_num x < modulus`,
   ONCE_REWRITE_TAC [GSYM modular_to_num_to_modular] THEN
   REWRITE_TAC [num_to_modular_to_num; lt_mod_modulus]);;

export_thm modular_to_num_bound;;

(*PARAMETRIC
let modular_to_num_bound = new_axiom
  `!x. modular_to_num x < modulus`;;
*)

let modular_to_num_div_bound = prove
  (`!x. modular_to_num x DIV modulus = 0`,
   GEN_TAC THEN
   MATCH_MP_TAC DIV_LT THEN
   REWRITE_TAC [modular_to_num_bound]);;

export_thm modular_to_num_div_bound;;

(*PARAMETRIC
let modular_to_num_div_bound = new_axiom
  `!x. modular_to_num x DIV modulus = 0`;;
*)

let modular_to_num_mod_bound = prove
  (`!x. modular_to_num x MOD modulus = modular_to_num x`,
   GEN_TAC THEN
   MATCH_MP_TAC MOD_LT THEN
   REWRITE_TAC [modular_to_num_bound]);;

export_thm modular_to_num_mod_bound;;

(*PARAMETRIC
let modular_to_num_mod_bound = new_axiom
  `!x. modular_to_num x MOD modulus = modular_to_num x`;;
*)

let modular_add_to_num = prove
  (`!x y.
      modular_to_num (modular_add x y) =
      (modular_to_num x + modular_to_num y) MOD modulus`,
   REPEAT GEN_TAC THEN
   (CONV_TAC o LAND_CONV o RAND_CONV o RAND_CONV)
     (REWR_CONV (GSYM modular_to_num_to_modular)) THEN
   (CONV_TAC o LAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
     (REWR_CONV (GSYM modular_to_num_to_modular)) THEN
   REWRITE_TAC [GSYM num_to_modular_add] THEN
   REWRITE_TAC [num_to_modular_to_num]);;

export_thm modular_add_to_num;;

(*PARAMETRIC
let modular_add_to_num = new_axiom
   `!x y.
      modular_to_num (modular_add x y) =
      (modular_to_num x + modular_to_num y) MOD modulus`;;
*)

let modular_mult_to_num = prove
  (`!x y.
      modular_to_num (modular_mult x y) =
      (modular_to_num x * modular_to_num y) MOD modulus`,
   REPEAT GEN_TAC THEN
   (CONV_TAC o LAND_CONV o RAND_CONV o RAND_CONV)
     (REWR_CONV (GSYM modular_to_num_to_modular)) THEN
   (CONV_TAC o LAND_CONV o RAND_CONV o RATOR_CONV o RAND_CONV)
     (REWR_CONV (GSYM modular_to_num_to_modular)) THEN
   REWRITE_TAC [GSYM num_to_modular_mult] THEN
   REWRITE_TAC [num_to_modular_to_num]);;

export_thm modular_mult_to_num;;

(*PARAMETRIC
let modular_mult_to_num = new_axiom
   `!x y.
      modular_to_num (modular_mult x y) =
      (modular_to_num x * modular_to_num y) MOD modulus`;;
*)

let modular_lt_alt = prove
  (`!x y. modular_lt x y = modular_to_num x < modular_to_num y`,
   REWRITE_TAC [modular_lt_def; modular_le_def; NOT_LE]);;

export_thm modular_lt_alt;;

(*PARAMETRIC
let modular_lt_alt = new_axiom
   `!x y. modular_lt x y = modular_to_num x < modular_to_num y`;;
*)

let num_to_modular_modulus = prove
  (`num_to_modular modulus = num_to_modular 0`,
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [num_to_modular_to_num; mod_refl_modulus; zero_mod_modulus]);;

export_thm num_to_modular_modulus;;

(*PARAMETRIC
let num_to_modular_modulus = new_axiom
   `num_to_modular modulus = num_to_modular 0`;;
*)

let modular_add_comm = prove
  (`!x y. modular_add x y = modular_add y x`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_add_to_num; num_to_modular_to_num] THEN
   CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
   REFL_TAC);;

export_thm modular_add_comm;;

(*PARAMETRIC
let modular_add_comm = new_axiom
   `!x y. modular_add x y = modular_add y x`;;
*)

let modular_add_assoc = prove
  (`!x y z. modular_add (modular_add x y) z = modular_add x (modular_add y z)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_add_to_num; num_to_modular_to_num] THEN
   ONCE_REWRITE_TAC [GSYM mod_add_mod_modulus] THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_add_mod_modulus] THEN
   REWRITE_TAC [ADD_ASSOC]);;

export_thm modular_add_assoc;;

(*PARAMETRIC
let modular_add_assoc = new_axiom
   `!x y z. modular_add (modular_add x y) z = modular_add x (modular_add y z)`;;
*)

let modular_add_left_zero = prove
  (`!x. modular_add (num_to_modular 0) x = x`,
   GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC
     [modular_add_to_num; num_to_modular_to_num; zero_mod_modulus; ADD;
      modular_to_num_mod_bound]);;

export_thm modular_add_left_zero;;

(*PARAMETRIC
let modular_add_left_zero = new_axiom
   `!x. modular_add (num_to_modular 0) x = x`;;
*)

let modular_add_right_zero = prove
  (`!x. modular_add x (num_to_modular 0) = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_add_comm] THEN
   MATCH_ACCEPT_TAC modular_add_left_zero);;

export_thm modular_add_right_zero;;

(*PARAMETRIC
let modular_add_right_zero = new_axiom
   `!x. modular_add x (num_to_modular 0) = x`;;
*)

let modular_add_left_neg = prove
  (`!x. modular_add (modular_neg x) x = num_to_modular 0`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM num_to_modular_modulus] THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_add_to_num; num_to_modular_to_num] THEN
   REWRITE_TAC [modular_neg_def; num_to_modular_to_num] THEN
   ONCE_REWRITE_TAC [GSYM mod_add_mod_modulus] THEN
   REWRITE_TAC [modular_neg_def; num_to_modular_to_num] THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_add_mod_modulus] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC SUB_ADD THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   MATCH_ACCEPT_TAC modular_to_num_bound);;

export_thm modular_add_left_neg;;

(*PARAMETRIC
let modular_add_left_neg = new_axiom
   `!x. modular_add (modular_neg x) x = num_to_modular 0`;;
*)

let modular_add_right_neg = prove
  (`!x. modular_add x (modular_neg x) = num_to_modular 0`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_add_comm] THEN
   MATCH_ACCEPT_TAC modular_add_left_neg);;

export_thm modular_add_right_neg;;

(*PARAMETRIC
let modular_add_right_neg = new_axiom
   `!x. modular_add x (modular_neg x) = num_to_modular 0`;;
*)

let modular_add_left_cancel = prove
  (`!x y z. modular_add x y = modular_add x z <=> y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM modular_add_left_zero] THEN
    ONCE_REWRITE_TAC [GSYM (SPEC `x : modular` modular_add_left_neg)] THEN
    ASM_REWRITE_TAC [modular_add_assoc];
    DISCH_THEN SUBST_VAR_TAC THEN
    REFL_TAC]);;

export_thm modular_add_left_cancel;;

(*PARAMETRIC
let modular_add_left_cancel = new_axiom
   `!x y z. modular_add x y = modular_add x z <=> y = z`;;
*)

let modular_add_right_cancel = prove
  (`!x y z. modular_add y x = modular_add z x <=> y = z`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_add_comm] THEN
   REWRITE_TAC [modular_add_left_cancel]);;

export_thm modular_add_right_cancel;;

(*PARAMETRIC
let modular_add_right_cancel = new_axiom
   `!x y z. modular_add y x = modular_add z x <=> y = z`;;
*)

let modular_add_left_cancel_zero = prove
  (`!x y. modular_add x y = x <=> y = num_to_modular 0`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM modular_add_right_zero)))) THEN
   REWRITE_TAC [modular_add_left_cancel]);;

export_thm modular_add_left_cancel_zero;;

(*PARAMETRIC
let modular_add_left_cancel_zero = new_axiom
   `!x y. modular_add x y = x <=> y = num_to_modular 0`;;
*)

let modular_add_right_cancel_zero = prove
  (`!x y. modular_add y x = x <=> y = num_to_modular 0`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_add_comm] THEN
   MATCH_ACCEPT_TAC modular_add_left_cancel_zero);;

export_thm modular_add_right_cancel_zero;;

(*PARAMETRIC
let modular_add_right_cancel_zero = new_axiom
   `!x y. modular_add y x = x <=> y = num_to_modular 0`;;
*)

let modular_neg_neg = prove
  (`!x. modular_neg (modular_neg x) = x`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `modular_neg x` modular_add_left_cancel)] THEN
   REWRITE_TAC [modular_add_right_neg; modular_add_left_neg]);;

export_thm modular_neg_neg;;

(*PARAMETRIC
let modular_neg_neg = new_axiom
   `!x. modular_neg (modular_neg x) = x`;;
*)

let modular_neg_inj = prove
  (`!x y. modular_neg x = modular_neg y ==> x = y`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM modular_neg_neg] THEN
   ASM_REWRITE_TAC []);;

export_thm modular_neg_inj;;

(*PARAMETRIC
let modular_neg_inj = new_axiom
   `!x y. modular_neg x = modular_neg y ==> x = y`;;
*)

let modular_neg_zero = prove
  (`modular_neg (num_to_modular 0) = num_to_modular 0`,
   ONCE_REWRITE_TAC
     [GSYM (SPEC `num_to_modular 0` modular_add_left_cancel)] THEN
   REWRITE_TAC [modular_add_right_neg; modular_add_right_zero]);;

export_thm modular_neg_zero;;

(*PARAMETRIC
let modular_neg_zero = new_axiom
   `modular_neg (num_to_modular 0) = num_to_modular 0`;;
*)

let modular_neg_is_zero = prove
  (`!x. modular_neg x = num_to_modular 0 <=> x = num_to_modular 0`,
   GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    MATCH_MP_TAC modular_neg_inj THEN
    ASM_REWRITE_TAC [modular_neg_zero];
    DISCH_THEN SUBST_VAR_TAC THEN
    REWRITE_TAC [modular_neg_zero]]);;

export_thm modular_neg_is_zero;;

(*PARAMETRIC
let modular_neg_is_zero = new_axiom
   `!x. modular_neg x = num_to_modular 0 <=> x = num_to_modular 0`;;
*)

let modular_neg_add = prove
  (`!x y.
      modular_add (modular_neg x) (modular_neg y) =
      modular_neg (modular_add x y)`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV modular_add_comm)) THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `modular_add x y` modular_add_left_cancel)] THEN
   REWRITE_TAC [modular_add_right_neg] THEN
   ONCE_REWRITE_TAC [modular_add_assoc] THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM modular_add_assoc)))) THEN
   REWRITE_TAC
     [modular_add_right_neg; modular_add_left_neg; modular_add_left_zero]);;

export_thm modular_neg_add;;

(*PARAMETRIC
let modular_neg_add = new_axiom
   `!x y.
      modular_add (modular_neg x) (modular_neg y) =
      modular_neg (modular_add x y)`;;
*)

let modular_mult_comm = prove
  (`!x y. modular_mult x y = modular_mult y x`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_mult_to_num; num_to_modular_to_num] THEN
   CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV MULT_SYM))) THEN
   REFL_TAC);;

export_thm modular_mult_comm;;

(*PARAMETRIC
let modular_mult_comm = new_axiom
   `!x y. modular_mult x y = modular_mult y x`;;
*)

let modular_mult_assoc = prove
  (`!x y z.
      modular_mult (modular_mult x y) z = modular_mult x (modular_mult y z)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_mult_to_num; num_to_modular_to_num] THEN
   ONCE_REWRITE_TAC [GSYM mod_mult_mod_modulus] THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_mult_mod_modulus] THEN
   REWRITE_TAC [MULT_ASSOC]);;

export_thm modular_mult_assoc;;

(*PARAMETRIC
let modular_mult_assoc = new_axiom
   `!x y z.
      modular_mult (modular_mult x y) z = modular_mult x (modular_mult y z)`;;
*)

let modular_add_left_distrib = prove
  (`!x y z.
      modular_mult x (modular_add y z) =
      modular_add (modular_mult x y) (modular_mult x z)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_add_to_num; modular_mult_to_num] THEN
   CONV_TAC (LAND_CONV (REWR_CONV (GSYM mod_mult_mod_modulus))) THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_mult_mod_modulus; mod_add_mod_modulus] THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB]);;

export_thm modular_add_left_distrib;;

(*PARAMETRIC
let modular_add_left_distrib = new_axiom
   `!x y z.
      modular_mult x (modular_add y z) =
      modular_add (modular_mult x y) (modular_mult x z)`;;
*)

let modular_add_right_distrib = prove
  (`!x y z.
      modular_mult (modular_add y z) x =
      modular_add (modular_mult y x) (modular_mult z x)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_add_to_num; modular_mult_to_num] THEN
   CONV_TAC (LAND_CONV (REWR_CONV (GSYM mod_mult_mod_modulus))) THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_mult_mod_modulus; mod_add_mod_modulus] THEN
   REWRITE_TAC [RIGHT_ADD_DISTRIB]);;

export_thm modular_add_right_distrib;;

(*PARAMETRIC
let modular_add_right_distrib = new_axiom
   `!x y z.
      modular_mult (modular_add y z) x =
      modular_add (modular_mult y x) (modular_mult z x)`;;
*)

let modular_mult_left_zero = prove
  (`!x. modular_mult (num_to_modular 0) x = num_to_modular 0`,
   GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC
     [modular_mult_to_num; num_to_modular_to_num; zero_mod_modulus;
      ZERO_MULT; modular_to_num_mod_bound]);;

export_thm modular_mult_left_zero;;

(*PARAMETRIC
let modular_mult_left_zero = new_axiom
   `!x. modular_mult (num_to_modular 0) x = num_to_modular 0`;;
*)

let modular_mult_right_zero = prove
  (`!x. modular_mult x (num_to_modular 0) = num_to_modular 0`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_mult_comm] THEN
   MATCH_ACCEPT_TAC modular_mult_left_zero);;

export_thm modular_mult_right_zero;;

(*PARAMETRIC
let modular_mult_right_zero = new_axiom
   `!x. modular_mult x (num_to_modular 0) = num_to_modular 0`;;
*)

let modular_mult_left_one = prove
  (`!x. modular_mult (num_to_modular 1) x = x`,
   GEN_TAC THEN
   MATCH_MP_TAC modular_to_num_inj THEN
   REWRITE_TAC [modular_mult_to_num; num_to_modular_to_num] THEN
   ONCE_REWRITE_TAC [GSYM mod_mult_mod_modulus] THEN
   REWRITE_TAC [mod_mod_refl_modulus] THEN
   REWRITE_TAC [mod_mult_mod_modulus; ONE_MULT; modular_to_num_mod_bound]);;

export_thm modular_mult_left_one;;

(*PARAMETRIC
let modular_mult_left_one = new_axiom
   `!x. modular_mult (num_to_modular 1) x = x`;;
*)

let modular_mult_right_one = prove
  (`!x. modular_mult x (num_to_modular 1) = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_mult_comm] THEN
   MATCH_ACCEPT_TAC modular_mult_left_one);;

export_thm modular_mult_right_one;;

(*PARAMETRIC
let modular_mult_right_one = new_axiom
   `!x. modular_mult x (num_to_modular 1) = x`;;
*)

let modular_mult_left_neg = prove
  (`!x y. modular_mult (modular_neg x) y = modular_neg (modular_mult x y)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `modular_mult x y` modular_add_left_cancel)] THEN
   REWRITE_TAC [modular_add_right_neg] THEN
   REWRITE_TAC
     [GSYM modular_add_right_distrib; modular_add_right_neg;
      modular_mult_left_zero]);;

export_thm modular_mult_left_neg;;

(*PARAMETRIC
let modular_mult_left_neg = new_axiom
   `!x y. modular_mult (modular_neg x) y = modular_neg (modular_mult x y)`;;
*)

let modular_mult_right_neg = prove
  (`!x y. modular_mult x (modular_neg y) = modular_neg (modular_mult x y)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [modular_mult_comm] THEN
   MATCH_ACCEPT_TAC modular_mult_left_neg);;

export_thm modular_mult_right_neg;;

(*PARAMETRIC
let modular_mult_right_neg = new_axiom
   `!x y. modular_mult x (modular_neg y) = modular_neg (modular_mult x y)`;;
*)

logfile_end ();;

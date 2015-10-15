(* ========================================================================= *)
(* CONSEQUENCES OF THE GROUP AXIOMS                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "group-thm";;

let group_add_left_neg' = prove
  (`!x y. group_add (group_neg x) (group_add x y) = y`,
   REWRITE_TAC
     [GSYM group_add_assoc; group_add_left_neg; group_add_left_zero]);;

export_thm group_add_left_neg';;

(*PARAMETRIC
let group_add_left_neg' = new_axiom
   `!x y. group_add (group_neg x) (group_add x y) = y`;;
*)

let group_add_right_neg = prove
  (`!x. group_add x (group_neg x) = group_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add group_zero (group_add x (group_neg x))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_left_zero;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `group_add (group_add (group_neg (group_neg x)) (group_neg x))
        (group_add x (group_neg x))` THEN
   CONJ_TAC THENL
   [AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_left_neg;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `group_add (group_neg (group_neg x))
        (group_add (group_neg x) (group_add x (group_neg x)))` THEN
   CONJ_TAC THENL
   [MATCH_ACCEPT_TAC group_add_assoc;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `group_add (group_neg (group_neg x))
        (group_add (group_add (group_neg x) x) (group_neg x))` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_assoc;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `group_add (group_neg (group_neg x))
        (group_add group_zero (group_neg x))` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC group_add_left_neg;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add (group_neg (group_neg x)) (group_neg x)` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC group_add_left_zero;
    ALL_TAC] THEN
   MATCH_ACCEPT_TAC group_add_left_neg);;

export_thm group_add_right_neg;;

(*PARAMETRIC
let group_add_right_neg = new_axiom
   `!x. group_add x (group_neg x) = group_zero`;;
*)

let group_add_right_neg' = prove
  (`!x y. group_add x (group_add (group_neg x) y) = y`,
   REWRITE_TAC
     [GSYM group_add_assoc; group_add_right_neg; group_add_left_zero]);;

export_thm group_add_right_neg';;

(*PARAMETRIC
let group_add_right_neg' = new_axiom
   `!x y. group_add x (group_add (group_neg x) y) = y`;;
*)

let group_add_right_zero = prove
  (`!x. group_add x group_zero = x`,
   GEN_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add x (group_add (group_neg x) x)` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_left_neg;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add (group_add x (group_neg x)) x` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_assoc;
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add group_zero x` THEN
   CONJ_TAC THENL
   [AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC group_add_right_neg;
    ALL_TAC] THEN
   MATCH_ACCEPT_TAC group_add_left_zero);;

export_thm group_add_right_zero;;

(*PARAMETRIC
let group_add_right_zero = new_axiom
   `!x. group_add x group_zero = x`;;
*)

let group_add_left_cancel_imp = prove
  (`!x y z. group_add x y = group_add x z ==> y = z`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add group_zero y` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_left_zero;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `group_add group_zero z` THEN
    CONJ_TAC THENL
    [SUBST1_TAC (SYM (SPEC `x : group` group_add_left_neg)) THEN
     ASM_REWRITE_TAC [group_add_assoc];
     MATCH_ACCEPT_TAC group_add_left_zero]]);;

export_thm group_add_left_cancel_imp;;

(*PARAMETRIC
let group_add_left_cancel_imp = new_axiom
   `!x y z. group_add x y = group_add x z ==> y = z`;;
*)

let group_add_left_cancel = prove
  (`!x y z. group_add x y = group_add x z <=> y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC group_add_left_cancel_imp;
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm group_add_left_cancel;;

(*PARAMETRIC
let group_add_left_cancel = new_axiom
   `!x y z. group_add x y = group_add x z <=> y = z`;;
*)

let group_add_left_cancel_zero_imp = prove
  (`!x y. group_add x y = x ==> y = group_zero`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_left_cancel_imp THEN
   EXISTS_TAC `x : group` THEN
   ASM_REWRITE_TAC [group_add_right_zero]);;

export_thm group_add_left_cancel_zero_imp;;

(*PARAMETRIC
let group_add_left_cancel_zero_imp = new_axiom
   `!x y. group_add x y = x ==> y = group_zero`;;
*)

let group_add_left_cancel_zero = prove
  (`!x y. group_add x y = x <=> y = group_zero`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC group_add_left_cancel_zero_imp;
    DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC group_add_right_zero]);;

export_thm group_add_left_cancel_zero;;

(*PARAMETRIC
let group_add_left_cancel_zero = new_axiom
   `!x y. group_add x y = x <=> y = group_zero`;;
*)

let group_add_right_cancel_imp = prove
  (`!x y z. group_add y x = group_add z x ==> y = z`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `group_add y group_zero` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_ACCEPT_TAC group_add_right_zero;
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `group_add z group_zero` THEN
    CONJ_TAC THENL
    [SUBST1_TAC (SYM (SPEC `x : group` group_add_right_neg)) THEN
     ASM_REWRITE_TAC [GSYM group_add_assoc];
     MATCH_ACCEPT_TAC group_add_right_zero]]);;

export_thm group_add_right_cancel_imp;;

(*PARAMETRIC
let group_add_right_cancel_imp = new_axiom
   `!x y z. group_add y x = group_add z x ==> y = z`;;
*)

let group_add_right_cancel = prove
  (`!x y z. group_add y x = group_add z x <=> y = z`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC group_add_right_cancel_imp;
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm group_add_right_cancel;;

(*PARAMETRIC
let group_add_right_cancel = new_axiom
   `!x y z. group_add y x = group_add z x <=> y = z`;;
*)

let group_add_right_cancel_zero_imp = prove
  (`!x y. group_add y x = x ==> y = group_zero`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_right_cancel_imp THEN
   EXISTS_TAC `x : group` THEN
   ASM_REWRITE_TAC [group_add_left_zero]);;

export_thm group_add_right_cancel_zero_imp;;

(*PARAMETRIC
let group_add_right_cancel_zero_imp = new_axiom
   `!x y. group_add y x = x ==> y = group_zero`;;
*)

let group_add_right_cancel_zero = prove
  (`!x y. group_add y x = x <=> y = group_zero`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC group_add_right_cancel_zero_imp;
    DISCH_THEN SUBST1_TAC THEN
    MATCH_ACCEPT_TAC group_add_left_zero]);;

export_thm group_add_right_cancel_zero;;

(*PARAMETRIC
let group_add_right_cancel_zero = new_axiom
   `!x y. group_add y x = x <=> y = group_zero`;;
*)

let group_neg_inj_imp = prove
  (`!x y. group_neg x = group_neg y ==> x = y`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_left_cancel_imp THEN
   EXISTS_TAC `group_neg x` THEN
   REWRITE_TAC [group_add_left_neg] THEN
   POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [group_add_left_neg]);;

export_thm group_neg_inj_imp;;

(*PARAMETRIC
let group_neg_inj_imp = new_axiom
   `!x y. group_neg x = group_neg y ==> x = y`;;
*)

let group_neg_inj = prove
  (`!x y. group_neg x = group_neg y <=> x = y`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC group_neg_inj_imp;
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm group_neg_inj;;

(*PARAMETRIC
let group_neg_inj = new_axiom
   `!x y. group_neg x = group_neg y <=> x = y`;;
*)

let group_neg_zero = prove
  (`group_neg group_zero = group_zero`,
   MATCH_MP_TAC group_add_left_cancel_zero_imp THEN
   EXISTS_TAC `group_zero` THEN
   REWRITE_TAC [group_add_right_neg]);;

export_thm group_neg_zero;;

(*PARAMETRIC
let group_neg_zero = new_axiom
   `group_neg group_zero = group_zero`;;
*)

let group_neg_neg = prove
  (`!x. group_neg (group_neg x) = x`,
   GEN_TAC THEN
   MATCH_MP_TAC group_add_left_cancel_imp THEN
   EXISTS_TAC `group_neg x` THEN
   REWRITE_TAC [group_add_left_neg; group_add_right_neg]);;

export_thm group_neg_neg;;

(*PARAMETRIC
let group_neg_neg = new_axiom
   `!x. group_neg (group_neg x) = x`;;
*)

let group_neg_add = prove
  (`!x y. group_neg (group_add x y) = group_add (group_neg y) (group_neg x)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC group_add_right_cancel_imp THEN
   EXISTS_TAC `group_add x y` THEN
   REWRITE_TAC [group_add_left_neg] THEN
   REWRITE_TAC [group_add_assoc; group_add_left_neg; group_add_left_neg']);;

export_thm group_neg_add;;

(*PARAMETRIC
let group_neg_add = new_axiom
   `!x y. group_neg (group_add x y) = group_add (group_neg y) (group_neg x)`;;
*)

let group_neg_left_eq = prove
  (`!x y. group_add y x = group_zero ==> group_neg x = y`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_right_cancel_imp THEN
   EXISTS_TAC `x : group` THEN
   ASM_REWRITE_TAC [group_add_left_neg]);;

export_thm group_neg_left_eq;;

(*PARAMETRIC
let group_neg_left_eq = new_axiom
   `!x y. group_add y x = group_zero ==> group_neg x = y`;;
*)

let group_neg_right_eq = prove
  (`!x y. group_add x y = group_zero ==> group_neg x = y`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_left_cancel_imp THEN
   EXISTS_TAC `x : group` THEN
   ASM_REWRITE_TAC [group_add_right_neg]);;

export_thm group_neg_right_eq;;

(*PARAMETRIC
let group_neg_right_eq = new_axiom
   `!x y. group_add x y = group_zero ==> group_neg x = y`;;
*)

let group_comm_left_neg_imp = prove
  (`!x y.
      group_add x y = group_add y x ==>
      group_add (group_neg x) y = group_add y (group_neg x)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC group_add_right_cancel_imp THEN
   EXISTS_TAC `x : group` THEN
   REWRITE_TAC [group_add_left_neg; group_add_assoc; group_add_right_zero] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC
     [GSYM group_add_assoc; group_add_left_neg; group_add_left_zero]);;

export_thm group_comm_left_neg_imp;;

(*PARAMETRIC
let group_comm_left_neg_imp = new_axiom
   `!x y.
      group_add x y = group_add y x ==>
      group_add (group_neg x) y = group_add y (group_neg x)`;;
*)

let group_comm_left_neg = prove
  (`!x y.
      group_add (group_neg x) y = group_add y (group_neg x) <=>
      group_add x y = group_add y x`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM group_neg_neg)))) THEN
    CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (GSYM group_neg_neg)))) THEN
    MATCH_MP_TAC group_comm_left_neg_imp THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_ACCEPT_TAC group_comm_left_neg_imp]);;

export_thm group_comm_left_neg;;

(*PARAMETRIC
let group_comm_left_neg = new_axiom
   `!x y.
      group_add (group_neg x) y = group_add y (group_neg x) <=>
      group_add x y = group_add y x`;;
*)

let group_comm_right_neg_imp = prove
  (`!x y.
      group_add y x = group_add x y ==>
      group_add y (group_neg x) = group_add (group_neg x) y`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
   CONV_TAC (RAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
   MATCH_ACCEPT_TAC group_comm_left_neg_imp);;

export_thm group_comm_right_neg_imp;;

(*PARAMETRIC
let group_comm_right_neg_imp = new_axiom
   `!x y.
      group_add y x = group_add x y ==>
      group_add y (group_neg x) = group_add (group_neg x) y`;;
*)

let group_comm_right_neg = prove
  (`!x y.
      group_add y (group_neg x) = group_add (group_neg x) y <=>
      group_add y x = group_add x y`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
   CONV_TAC (RAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
   MATCH_ACCEPT_TAC group_comm_left_neg);;

export_thm group_comm_right_neg;;

(*PARAMETRIC
let group_comm_right_neg = new_axiom
   `!x y.
      group_add y (group_neg x) = group_add (group_neg x) y <=>
      group_add y x = group_add x y`;;
*)

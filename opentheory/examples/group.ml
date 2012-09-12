(* ------------------------------------------------------------------------- *)
(* A parametric theory of groups.                                            *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* group *)
*)

(* The theory parameters *)

logfile "group-witness";;

let (group_add_left_zero,group_add_left_neg,group_add_assoc) =
  let tybij = define_newtype ("x","group") ("u",`:1`) in
  let _ = new_definition `group_zero = mk_group one` in
  let _ = new_definition
    `!(x : group) (y : group). group_add x y = group_zero` in
  let _ = new_definition `!x : group. group_neg x = group_zero` in
  let th = prove
    (`!x : group. x = group_zero`,
     GEN_TAC THEN
     ONCE_REWRITE_TAC [GSYM (CONJUNCT1 tybij)] THEN
     ONCE_REWRITE_TAC [one] THEN
     REFL_TAC) in
  let prove_eq tm =
    prove (tm, REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [th] THEN REFL_TAC) in
  let th1 = prove_eq `!x. group_add group_zero x = x` in
  let th2 = prove_eq `!x. group_add (group_neg x) x = group_zero` in
  let th3 = prove_eq
    `!x y z. group_add (group_add x y) z = group_add x (group_add y z)` in
  (th1,th2,th3);;

logfile "group-def";;

(*PARAMETRIC
(* group-def *)
*)

let group_sub_def = new_definition
  `!(x : group) (y : group). group_sub x y = group_add x (group_neg y)`;;

(*PARAMETRIC
new_constant ("group_sub", `:group -> group -> group`);;
*)

export_thm group_sub_def;;

(*PARAMETRIC
let group_sub_def = new_axiom
  `!(x : group) (y : group). group_sub x y = group_add x (group_neg y)`;;
*)

logfile "group-thm";;

(*PARAMETRIC
(* group-thm *)
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

(*PARAMETRIC
let group_neg_inj = new_axiom
   `!x y. group_neg x = group_neg y <=> x = y`;;
*)

let group_neg_neg = prove
  (`!x. group_neg (group_neg x) = x`,
   GEN_TAC THEN
   MATCH_MP_TAC group_add_left_cancel_imp THEN
   EXISTS_TAC `group_neg x` THEN
   REWRITE_TAC [group_add_left_neg; group_add_right_neg]);;

(*PARAMETRIC
let group_neg_neg = new_axiom
   `!x. group_neg (group_neg x) = x`;;
*)

(***
***)

logfile "group-mult-def";;

(*PARAMETRIC
(* group-mult-def *)
*)

let (group_mult_zero,group_mult_suc) =
    let def = new_recursive_definition num_RECURSION
          `(!(x : group). group_mult x 0 = group_zero) /\
           (!(x : group) n.
              group_mult x (SUC n) = group_add x (group_mult x n))` in
    CONJ_PAIR def;;

(*PARAMETRIC
new_constant ("group_mult", `:group -> num -> group`);;
*)

export_thm group_mult_zero;;
export_thm group_mult_suc;;

(*PARAMETRIC
let group_mult_zero = new_axiom
  `!x. group_mult x 0 = group_zero`;;

let group_mult_suc = new_axiom
  `!x n. group_mult x (SUC n) = group_add x (group_mult x n)`;;
*)

let group_mult_def = CONJ group_mult_zero group_mult_suc;;

(*PARAMETRIC
let group_mult_def = CONJ group_mult_zero group_mult_suc;;
*)

logfile "group-mult-thm";;

(*PARAMETRIC
(* group-mult-thm *)
*)

let group_zero_mult = prove
  (`!n. group_mult group_zero n = group_zero`,
   INDUCT_TAC THENL
   [REWRITE_TAC [group_mult_zero];
    ASM_REWRITE_TAC [group_mult_suc; group_add_right_zero]]);;

(*PARAMETRIC
let group_zero_mult = new_axiom
   `!n. group_mult group_zero n = group_zero`;;
*)

let group_mult_one = prove
  (`!x. group_mult x 1 = x`,
   REWRITE_TAC [ONE; group_mult_def; group_add_right_zero]);;

(*PARAMETRIC
let group_mult_one = new_axiom
   `!x. group_mult x 1 = x`;;
*)

let group_mult_add = prove
  (`!x m n.
      group_mult x (m + n) = group_add (group_mult x m) (group_mult x n)`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [group_mult_zero; ZERO_ADD; group_add_left_zero];
    ASM_REWRITE_TAC [group_mult_suc; group_add_assoc; SUC_ADD]]);;

(*PARAMETRIC
let group_mult_add = new_axiom
   `!x m n.
      group_mult x (m + n) = group_add (group_mult x m) (group_mult x n)`;;
*)

let group_mult_suc' = prove
  (`!x n. group_mult x (SUC n) = group_add (group_mult x n) x`,
   REWRITE_TAC [ADD1; group_mult_add; group_mult_one]);;

(*PARAMETRIC
let group_mult_suc' = new_axiom
   `!x n. group_mult x (SUC n) = group_add (group_mult x n) x`;;
*)

logfile_end ();;

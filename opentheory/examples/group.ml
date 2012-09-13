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

let group_add_left_neg' = prove
  (`!x y. group_add (group_neg x) (group_add x y) = y`,
   REWRITE_TAC
     [GSYM group_add_assoc; group_add_left_neg; group_add_left_zero]);;

export_thm group_add_left_neg';;

(*PARAMETRIC
let group_add_left_neg' = prove
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
let group_add_right_neg' = prove
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

let group_neg_zero = prove
  (`group_neg group_zero = group_zero`,
   MATCH_MP_TAC group_add_left_cancel_zero_imp THEN
   EXISTS_TAC `group_zero` THEN
   REWRITE_TAC [group_add_right_neg]);;

(*PARAMETRIC
let group_neg_zero = new_axiom
   `group_neg group_zero = group_zero`;;
*)

let group_neg_add = prove
  (`!x y. group_neg (group_add x y) = group_add (group_neg y) (group_neg x)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC group_add_right_cancel_imp THEN
   EXISTS_TAC `group_add x y` THEN
   REWRITE_TAC [group_add_left_neg] THEN
   REWRITE_TAC [group_add_assoc; group_add_left_neg; group_add_left_neg']);;

(*PARAMETRIC
let group_neg_add = new_axiom
   `!x y. group_neg (group_add x y) = group_add (group_neg y) (group_neg x)`;;
*)

let group_sub_left_zero = prove
  (`!x. group_sub group_zero x = group_neg x`,
   REWRITE_TAC [group_sub_def; group_add_left_zero]);;

(*PARAMETRIC
let group_sub_left_zero = new_axiom
   `!x. group_sub group_zero x = group_neg x`;;
*)

let group_sub_right_zero = prove
  (`!x. group_sub x group_zero = x`,
   REWRITE_TAC [group_sub_def; group_neg_zero; group_add_right_zero]);;

(*PARAMETRIC
let group_sub_right_zero = prove
   `!x. group_sub x group_zero = x`;;
*)

let group_sub_refl = prove
  (`!x. group_sub x x = group_zero`,
   REWRITE_TAC [group_sub_def; group_add_right_neg]);;

(*PARAMETRIC
let group_sub_refl = new_axiom
   `!x. group_sub x x = group_zero`;;
*)

let group_neg_sub = prove
  (`!x y. group_neg (group_sub x y) = group_sub y x`,
   REWRITE_TAC [group_sub_def; group_neg_add; group_neg_neg]);;

(*PARAMETRIC
let group_neg_sub = prove
   `!x y. group_neg (group_sub x y) = group_sub y x`;;
*)

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

let group_mult_mult = prove
  (`!x m n. group_mult (group_mult x m) n = group_mult x (m * n)`,
   GEN_TAC THEN
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [group_mult_zero; MULT_0];
    ASM_REWRITE_TAC [group_mult_suc; MULT_SUC; group_mult_add]]);;

(*PARAMETRIC
let group_mult_mult = new_axiom
   `!x m n. group_mult (group_mult x m) n = group_mult x (m * n)`;;
*)

logfile "group-mult-sub-def";;

(*PARAMETRIC
(* group-mult-sub-def *)
*)

let (group_mult_sub_nil,group_mult_sub_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!b n d f p.
        group_mult_sub b n d f p [] =
        if b then group_sub n d else group_sub d n) /\
     (!b n d f p h t.
        group_mult_sub b n d f p (CONS h t) =
        let s = group_sub p f in
        group_mult_sub (~b) d (if h then group_sub n s else n) s f t)` in
  CONJ_PAIR def;;

(*PARAMETRIC
new_constant
  ("group_mult_sub",
   `:bool -> group -> group -> group -> group -> bool list -> group`);;
*)

export_thm group_mult_sub_nil;;
export_thm group_mult_sub_cons;;

(*PARAMETRIC
let group_mult_sub_nil = new_axiom
    `(!b n d f p.
        group_mult_sub b n d f p [] =
        if b then group_sub n d else group_sub d n)`;;

let group_mult_sub_cons = new_axiom
    `(!b n d f p h t.
        group_mult_sub b n d f p (CONS h t) =
        let s = group_sub p f in
        group_mult_sub (~b) d (if h then group_sub n s else n) s f t)`;;
*)

let group_mult_sub_def = CONJ group_mult_sub_nil group_mult_sub_cons;;

(*PARAMETRIC
let group_mult_sub_def = CONJ group_mult_sub_nil group_mult_sub_cons;;
*)

(***
logfile "group-mult-sub-thm";;

(*PARAMETRIC
(* group-mult-sub-thm *)
*)

let group_mult_sub_invariant = prove
  (`!x n d f p l.
      (group_add x n = group_add n x) /\
      (group_add x d = group_add d x) ==>
      (group_mult_sub T n d (group_mult x f) (group_neg (group_mult x p)) l =
       group_add (group_sub n d) (group_mult x (decode_fib_dest f p l))) /\
      (group_mult_sub F n d (group_neg (group_mult x f)) (group_mult x p) l =
       group_add (group_sub d n) (group_mult x (decode_fib_dest f p l)))`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`p : num`, `p : num`) THEN
   SPEC_TAC (`f : num`, `f : num`) THEN
   SPEC_TAC (`d : group`, `d : group`) THEN
   SPEC_TAC (`n : group`, `n : group`) THEN
   SPEC_TAC (`l : bool list`, `l : bool list`) THEN
   LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC
      [group_mult_def; decode_fib_dest_def; group_mult_sub_def;
       group_add_right_zero];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC
     [group_mult_def; decode_fib_dest_def; group_mult_sub_def;
      LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
   REWRITE_TAC
     [group_sub_def; group_neg_neg; GSYM group_neg_add;
      GSYM group_mult_add] THEN
   SUBST1_TAC (SPECL [`p : num`; `f : num`] ADD_SYM) THEN
   ASM_REWRITE_TAC [] THEN
   BOOL_CASES_TAC `h : bool` THEN
   REWRITE_TAC
     [group_mult_add; group_sub_def; group_add_assoc; group_add_left_cancel;
      group_neg_add; group_neg_neg]

; group_neg_add] THEN
   REWRITE_TAC [group_sub_def; group_neg_neg; group_neg_add] THEN


   SUBGOAL_THEN
     `group_sub (group_neg (group_mult x p)) (group_mult x f) =
      group_neg (group_mult x (f + p))` SUBST1_TAC THENL
   [REWRITE_TAC [group_sub_def; GSYM group_neg_add; group_mult_add];
    ALL_TAC] THEN
   CONJ_TAC THENL


   [REWRITE_TAC [
SUBGOAL_THEN
      `group_sub n (group_neg (group_mult x (f + p))) =
       group_add n (group_mult x (f + p))` SUBST1_TAC THENL
    [MP_TAC (SPECL [`group_neg (group_mult x (f + p))`; `n : group`] group_sub_inv) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC group_neg_nonzero THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [group_add_left_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC group_neg_inv THEN
     ASM_REWRITE_TAC [group_mult_eq_zero];
     ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`d : group`; `if h then group_add n (group_mult x (f + p)) else n`;
       `f + p : num`; `f : num`]) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     BOOL_CASES_TAC `h : bool` THEN
     ASM_REWRITE_TAC [group_add_eq_zero; group_mult_eq_zero];
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
    BOOL_CASES_TAC `h : bool` THENL
    [ASM_REWRITE_TAC [] THEN
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM group_mult_add])) THEN
     REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC group_add_right_cancel_imp THEN
     EXISTS_TAC `d : group` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `group_add n (group_mult x (f + p))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC group_sub_right_mult THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC EQ_SYM THEN
      REWRITE_TAC [group_add_assoc] THEN
      CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [group_add_comm]))) THEN
      REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
      DISJ2_TAC THEN
      MATCH_MP_TAC group_sub_right_mult THEN
      FIRST_ASSUM ACCEPT_TAC];
     ASM_REWRITE_TAC []];
    SUBGOAL_THEN
      `group_sub (group_mult x p) (group_neg (group_mult x f)) =
       group_mult x (f + p)` SUBST1_TAC THENL
    [MP_TAC (SPECL [`group_neg (group_mult x f)`; `group_mult x p`] group_sub_inv) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC group_neg_nonzero THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     REWRITE_TAC [GSYM group_mult_add; group_add_left_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC group_neg_inv THEN
     ASM_REWRITE_TAC [group_mult_eq_zero];
     ALL_TAC] THEN
    FIRST_X_ASSUM (MP_TAC o SPECL
      [`d : group`; `if h then group_sub n (group_mult x (f + p)) else n`;
       `f + p : num`; `f : num`]) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     BOOL_CASES_TAC `h : bool` THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC group_sub_nonzero THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
    BOOL_CASES_TAC `h : bool` THENL
    [ASM_REWRITE_TAC [] THEN
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM group_mult_add])) THEN
     REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
     DISJ2_TAC THEN
     MATCH_MP_TAC group_add_left_cancel_imp THEN
     EXISTS_TAC `group_sub n (group_mult x (f + p))` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC group_sub_nonzero THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      ALL_TAC] THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `d : group` THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC group_sub_left_mult THEN
      MATCH_MP_TAC group_sub_nonzero THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      ALL_TAC] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `group_add n (group_sub d n)` THEN
     CONJ_TAC THENL
     [CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [group_add_comm]))) THEN
      REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
      DISJ2_TAC THEN
      MATCH_MP_TAC group_sub_right_mult THEN
      ASM_REWRITE_TAC [group_mult_eq_zero];
      MATCH_MP_TAC group_sub_left_mult THEN
      FIRST_ASSUM ACCEPT_TAC];
     ASM_REWRITE_TAC []]]);;

export_thm group_mult_sub_invariant;;

(*PARAMETRIC
let group_mult_sub_invariant = new_axiom
   `!x n d f p l.
      ~(x = num_to_group 0) /\ ~(n = num_to_group 0) /\ ~(d = num_to_group 0) ==>
      (group_mult_sub T n d (group_mult x f) (group_neg (group_mult x p)) l =
       group_add (group_sub n d) (group_mult x (decode_fib_dest f p l))) /\
      (group_mult_sub F n d (group_neg (group_mult x f)) (group_mult x p) l =
       group_add (group_sub d n) (group_mult x (decode_fib_dest f p l)))`;;
*)

let group_mult_sub = prove
  (`!x n.
      group_mult x n =
      (if n = 0 then group_zero
       else if x = num_to_group 0 then num_to_group 0
       else group_mult_sub T (group_zero) (group_zero) x (group_zero)
              (encode_fib n))`,
   REPEAT GEN_TAC THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [group_mult_def];
    ALL_TAC] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [group_mult_eq_zero];
    ALL_TAC] THEN
   MP_TAC (SPECL [`x : group`; `group_zero`; `group_zero`; `1`; `0`;
                  `encode_fib n`] group_mult_sub_invariant) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [group_one_nonzero];
    ALL_TAC] THEN
   DISCH_THEN
     (SUBST1_TAC o REWRITE_RULE [group_mult_def; group_neg_one; group_mult_one] o
      CONJUNCT1) THEN
   REWRITE_TAC
     [group_sub_one; group_add_left_one; GSYM decode_fib_def; encode_decode_fib]);;

export_thm group_mult_sub;;

(*PARAMETRIC
let group_mult_sub = new_axiom
   `!x n.
      group_mult x n =
      (if n = 0 then group_zero
       else if x = num_to_group 0 then num_to_group 0
       else group_mult_sub T (group_zero) (group_zero) x (group_zero)
              (encode_fib n))`;;
*)
***)

logfile "group-elgamal-def";;

(*PARAMETRIC
(* group-elgamal-def *)
*)

let group_elgamal_encrypt_def = new_definition
  `!g h m k.
     group_elgamal_encrypt g h m k =
     (group_mult g k, group_add (group_mult h k) m)`;;

(*PARAMETRIC
new_constant
  ("group_elgamal_encrypt",
   `:group -> group -> group -> num -> group # group`);;
*)

export_thm group_elgamal_encrypt_def;;

(*PARAMETRIC
let group_elgamal_encrypt_def = new_axiom
  `!g h m k.
     group_elgamal_encrypt g h m k =
     (group_mult g k, group_add (group_mult h k) m)`;;
*)

let group_elgamal_decrypt_def = new_definition
  `!x a b.
     group_elgamal_decrypt x (a,b) =
     group_add (group_neg (group_mult a x)) b`;;

(*PARAMETRIC
new_constant
  ("group_elgamal_decrypt",
   `:num -> group # group -> group`);;
*)

export_thm group_elgamal_decrypt_def;;

(*PARAMETRIC
let group_elgamal_decrypt_def = new_axiom
  `!x a b.
     group_elgamal_decrypt x (a,b) =
     group_add (group_neg (group_mult a x)) b`;;
*)

logfile "group-elgamal-thm";;

(*PARAMETRIC
(* group-elgamal-thm *)
*)

let group_elgamal_correctness = prove
  (`!g h m k x.
      (h = group_mult g x) ==>
      (group_elgamal_decrypt x (group_elgamal_encrypt g h m k) = m)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC
     [group_elgamal_encrypt_def; group_elgamal_decrypt_def;
      group_mult_mult] THEN
   CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM]))) THEN
   MATCH_ACCEPT_TAC group_add_left_neg');;

(*PARAMETRIC
let group_elgamal_correctness = new_axiom
   `!g h m k x.
      (h = group_mult g x) ==>
      (group_elgamal_decrypt x (group_elgamal_encrypt g h m k) = m)`;;
*)

logfile_end ();;

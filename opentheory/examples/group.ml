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

let group_sub_def = new_definition
  `!(x : group) (y : group).
     group_sub x y = group_add x (group_neg y)`;;

let (group_mult_zero,group_mult_suc) =
    let def = new_recursive_definition num_RECURSION
          `(!(x : group). group_mult x 0 = group_zero) /\
           (!(x : group) n.
              group_mult x (SUC n) = group_add x (group_mult x n))` in
    CONJ_PAIR def;;

let group_mult_def = CONJ group_mult_zero group_mult_suc;;

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

(***
val group_lcancel = store_thm
  ("group_lcancel",
   ``!g :: Group. !x y z :: (g.carrier). (group_add x y = group_add x z) = (y = z)``,
   RW_TAC resq_ss []
   ++ REVERSE EQ_TAC >> RW_TAC std_ss []
   ++ RW_TAC std_ss []
   ++ Suff `group_add group_zero y = group_add group_zero z`
   >> METIS_TAC [group_lid]
   ++ Suff `group_add (group_add (group_neg x) x) y = group_add (group_add (group_neg x) x) z`
   >> METIS_TAC [group_linv]
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `group_add (group_neg x) (group_add x y)`
   ++ CONJ_TAC
   >> (match_tac group_assoc ++ METIS_TAC [group_inv_carrier])
   ++ MATCH_MP_TAC EQ_TRANS
   ++ Q.EXISTS_TAC `group_add (group_neg x) (group_add x z)`
   ++ REVERSE CONJ_TAC
   >> (match_tac (GSYM group_assoc) ++ METIS_TAC [group_inv_carrier])
   ++ RW_TAC std_ss []);
***)

logfile_end ();;

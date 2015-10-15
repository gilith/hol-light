(* ========================================================================= *)
(* PARAMETRIC THEORY WITNESS FOR GROUPS                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "group-witness";;

let (group_add_left_zero,
     group_add_left_neg,
     group_add_assoc,
     group_add_comm,
     group_finite) =
  let tybij = define_newtype ("x","group") ("u",`:1`) in
  let _ = new_definition `group_zero = mk_group one` in
  let _ = new_definition `!x : group. group_neg x = group_zero` in
  let _ = new_definition
    `!(x : group) (y : group). group_add x y = group_zero` in
  let th = prove
    (`!x : group. x = group_zero`,
     GEN_TAC THEN
     ONCE_REWRITE_TAC [GSYM (CONJUNCT1 tybij)] THEN
     ONCE_REWRITE_TAC [one] THEN
     REFL_TAC) in
  let prove_eq tm =
    prove (tm, REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [th] THEN REFL_TAC) in
  let add_left_zero = prove_eq `!x. group_add group_zero x = x` in
  let add_left_neg = prove_eq `!x. group_add (group_neg x) x = group_zero` in
  let add_assoc = prove_eq
    `!x y z. group_add (group_add x y) z = group_add x (group_add y z)` in
  let add_comm = prove_eq `!x y. group_add x y = group_add y x` in
  let finite = prove
    (`FINITE (UNIV : group set)`,
     SUBGOAL_THEN `UNIV = group_zero INSERT EMPTY` SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      ACCEPT_TAC th;
      MATCH_ACCEPT_TAC FINITE_SING]) in
  (add_left_zero,add_left_neg,add_assoc,add_comm,finite);;

export_thm group_add_left_zero;;
export_thm group_add_left_neg;;
export_thm group_add_assoc;;
export_thm group_add_comm;;
export_thm group_finite;;

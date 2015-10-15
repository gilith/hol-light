(* ========================================================================= *)
(* PARAMETRIC THEORY WITNESS FOR COMMUTATIVE MONOIDS                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "monoid-comm-witness";;

let (monoid_add_left_zero,
     _,
     monoid_add_assoc,
     monoid_add_comm,
     _) =
  let tybij = define_newtype ("x","monoid") ("u",`:1`) in
  let _ = new_definition `monoid_zero = mk_monoid one` in
  let _ = new_definition
    `!(x : monoid) (y : monoid). monoid_add x y = monoid_zero` in
  let th = prove
    (`!x : monoid. x = monoid_zero`,
     GEN_TAC THEN
     ONCE_REWRITE_TAC [GSYM (CONJUNCT1 tybij)] THEN
     ONCE_REWRITE_TAC [one] THEN
     REFL_TAC) in
  let prove_eq tm =
    prove (tm, REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [th] THEN REFL_TAC) in
  let add_left_zero = prove_eq `!x. monoid_add monoid_zero x = x` in
  let add_right_zero = prove_eq `!x. monoid_add x monoid_zero = x` in
  let add_assoc = prove_eq
    `!x y z. monoid_add (monoid_add x y) z = monoid_add x (monoid_add y z)` in
  let add_comm = prove_eq `!x y. monoid_add x y = monoid_add y x` in
  let finite = prove
    (`FINITE (UNIV : monoid set)`,
     SUBGOAL_THEN `UNIV = monoid_zero INSERT EMPTY` SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      ACCEPT_TAC th;
      MATCH_ACCEPT_TAC FINITE_SING]) in
  (add_left_zero,add_right_zero,add_assoc,add_comm,finite);;

export_thm monoid_add_left_zero;;
export_thm monoid_add_assoc;;
export_thm monoid_add_comm;;

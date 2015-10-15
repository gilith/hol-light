(* ========================================================================= *)
(* CONSEQUENCES OF THE COMMUTATIVE MONOID AXIOMS                             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "monoid-comm-thm";;

export_thm monoid_add_right_zero;;

let monoid_add_comm' = prove
  (`!x y z. monoid_add x (monoid_add y z) = monoid_add y (monoid_add x z)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [GSYM monoid_add_assoc] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC monoid_add_comm);;

export_thm monoid_add_comm';;

(*PARAMETRIC
let monoid_add_comm' = new_axiom
   `!x y z. monoid_add x (monoid_add y z) = monoid_add y (monoid_add x z)`;;
*)

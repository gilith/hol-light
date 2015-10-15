(* ========================================================================= *)
(* PARAMETRIC THEORY WITNESS FOR MONOIDS                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "monoid-witness";;

export_thm monoid_add_left_zero;;
export_thm monoid_add_assoc;;

let monoid_add_right_zero = prove
 (`!x. monoid_add x monoid_zero = x`,
  ONCE_REWRITE_TAC [monoid_add_comm] THEN
  ACCEPT_TAC monoid_add_left_zero);;

export_thm monoid_add_right_zero;;

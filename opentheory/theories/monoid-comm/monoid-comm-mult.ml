(* ========================================================================= *)
(* COMMUTATIVE MONOID MULTIPLICATION                                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of commutative monoid multiplication.                          *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-comm-mult-def";;

export_thm monoid_mult_right_zero;;
export_thm monoid_mult_right_suc;;

(* ------------------------------------------------------------------------- *)
(* Properties of commutative monoid multiplication.                          *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-comm-mult-thm";;

export_thm monoid_mult_left_zero;;
export_thm monoid_mult_right_one;;
export_thm monoid_mult_right_two;;
export_thm monoid_mult_right_add;;
export_thm monoid_mult_right_suc';;
export_thm monoid_mult_right_mult;;

(* ------------------------------------------------------------------------- *)
(* Commutative monoid multiplication by repeated addition.                   *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-comm-mult-add";;

(* Definition *)

export_thm monoid_mult_add_nil;;
export_thm monoid_mult_add_cons;;

(* Correctness *)

export_thm monoid_mult_add_invariant;;
export_thm monoid_mult_add_correct;;

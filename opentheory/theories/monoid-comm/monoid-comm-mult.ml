(* ========================================================================= *)
(* COMMUTATIVE MONOID MULTIPLICATION                                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Properties of commutative monoid multiplication.                          *)
(* ------------------------------------------------------------------------- *)

logfile "monoid-comm-mult-thm";;

export_thm monoid_mult_left_zero;;
export_thm monoid_mult_right_one;;
export_thm monoid_mult_right_two;;
export_thm monoid_mult_right_add;;
export_thm monoid_mult_right_suc';;
export_thm monoid_mult_right_mult;;

logfile_end ();;

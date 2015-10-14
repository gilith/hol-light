(* ========================================================================= *)
(* PARAMETRIC THEORY OF COMMUTATIVE MONOIDS                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for a parametric theory of commutative monoids.           *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/monoid-comm/monoid-comm.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness for commutative monoids.                        *)
(* ------------------------------------------------------------------------- *)

(* This is defined before the general monoid theory
loads "opentheory/theories/monoid-comm/monoid-comm-witness.ml";;
*)

(* ------------------------------------------------------------------------- *)
(* Consequences of the commutative monoid axioms.                            *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/monoid-comm/monoid-comm-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* Commutative monoid multiplication.                                        *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/monoid-comm/monoid-comm-mult.ml";;

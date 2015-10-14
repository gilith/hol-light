(* ========================================================================= *)
(* PARAMETRIC THEORY OF MONOIDS                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for a parametric theory of monoids.                       *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/monoid/monoid.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness for monoids.                                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/monoid-comm/monoid-comm-witness.ml";;

loads "opentheory/theories/monoid/monoid-witness.ml";;

(* ------------------------------------------------------------------------- *)
(* Consequences of the monoid axioms.                                        *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/monoid/monoid-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* Monoid multiplication.                                                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/monoid/monoid-mult.ml";;

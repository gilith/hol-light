(* ------------------------------------------------------------------------- *)
(* A parametric theory of GF(p).                                             *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* gfp *)
*)

(* The theory parameters *)

new_constant ("oddprime", `:num`);;

let oddprime_odd = new_axiom `ODD oddprime`;;

let oddprime_prime = new_axiom `prime oddprime`;;

(* Parametric theory instantiation: modular *)

loads "opentheory/examples/gfp-modular.ml";;

logfile "gfp-inverse-def";;

(*PARAMETRIC
(* gfp-inverse-def *)
*)

let gfp_inverse_exists = prove
  `!n : gfp. ~(n = num_to_gfp 0) ==> ?m. gfp_mult m n = num_to_gfp 1`;;

let gfp_inverse_def =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inverse_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inverse"] th1;;

(*PARAMETRIC
new_constant ("gfp_inverse", `:gfp -> gfp`);;
*)

export_thm gfp_inverse_def;;

logfile_end ();;

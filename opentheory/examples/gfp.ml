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

logfile "gfp-def";;

(*PARAMETRIC
(* gfp-def *)
*)

let oddprime_nonzero = prove
  (`~(oddprime = 0)`,
   STRIP_TAC THEN
   MP_TAC oddprime_prime THEN
   ASM_REWRITE_TAC [prime_zero]);;

export_thm oddprime_nonzero;;

(*PARAMETRIC
let oddprime_nonzero = new_axiom
  `~(oddprime = 0)`;;
*)

(* Parametric theory instantiation: modular *)

loads "opentheory/examples/gfp-modular.ml";;

(***
logfile "gfp-inverse-def";;

(*PARAMETRIC
(* gfp-inverse-def *)
*)

let gfp_inverse_exists = prove
  (`!n : gfp. ~(n = num_to_gfp 0) ==> ?m. gfp_mult m n = num_to_gfp 1`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`oddprime`; `gfp_to_num n`] gcd_prime) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [oddprime_prime] THEN
    MP_TAC (SPECL [`oddprime`; `gfp_to_num n`] divides_mod) THEN
    REWRITE_TAC [oddprime_nonzero] THEN
    DISCH_THEN SUBST1_TAC ...


let gfp_inverse_def =
    let th0 = ONCE_REWRITE_RULE [RIGHT_IMP_EXISTS_THM] gfp_inverse_exists in
    let th1 = REWRITE_RULE [SKOLEM_THM] th0 in
    new_specification ["gfp_inverse"] th1;;

(*PARAMETRIC
new_constant ("gfp_inverse", `:gfp -> gfp`);;
*)

export_thm gfp_inverse_def;;
***)

logfile_end ();;

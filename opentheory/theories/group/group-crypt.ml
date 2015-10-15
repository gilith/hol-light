(* ========================================================================= *)
(* GROUP CRYPTOGRAPHY                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of group cryptography.                                         *)
(* ------------------------------------------------------------------------- *)

export_theory "group-crypt-def";;

let group_elgamal_encrypt_def = new_definition
  `!g h m k.
     group_elgamal_encrypt g h m k =
     (group_mult g k, group_add (group_mult h k) m)`;;

(*PARAMETRIC
new_constant
  ("group_elgamal_encrypt",
   `:group -> group -> group -> num -> group # group`);;
*)

export_thm group_elgamal_encrypt_def;;

(*PARAMETRIC
let group_elgamal_encrypt_def = new_axiom
  `!g h m k.
     group_elgamal_encrypt g h m k =
     (group_mult g k, group_add (group_mult h k) m)`;;
*)

let group_elgamal_decrypt_def = new_definition
  `!x a b.
     group_elgamal_decrypt x (a,b) =
     group_add (group_neg (group_mult a x)) b`;;

(*PARAMETRIC
new_constant
  ("group_elgamal_decrypt",
   `:num -> group # group -> group`);;
*)

export_thm group_elgamal_decrypt_def;;

(*PARAMETRIC
let group_elgamal_decrypt_def = new_axiom
  `!x a b.
     group_elgamal_decrypt x (a,b) =
     group_add (group_neg (group_mult a x)) b`;;
*)

(* ------------------------------------------------------------------------- *)
(* Properties of group cryptography.                                         *)
(* ------------------------------------------------------------------------- *)

export_theory "group-crypt-thm";;

let group_elgamal_correct = prove
  (`!g h m k x.
      (h = group_mult g x) ==>
      (group_elgamal_decrypt x (group_elgamal_encrypt g h m k) = m)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC
     [group_elgamal_encrypt_def; group_elgamal_decrypt_def;
      GSYM group_mult_right_mult] THEN
   CONV_TAC (LAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM]))) THEN
   MATCH_ACCEPT_TAC group_add_left_neg');;

export_thm group_elgamal_correct;;

(*PARAMETRIC
let group_elgamal_correct = new_axiom
   `!g h m k x.
      (h = group_mult g x) ==>
      (group_elgamal_decrypt x (group_elgamal_encrypt g h m k) = m)`;;
*)

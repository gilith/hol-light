(* ========================================================================= *)
(* GROUP SUBTRACTION                                                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of group subtraction.                                          *)
(* ------------------------------------------------------------------------- *)

export_theory "group-sub-def";;

let group_sub_def = new_definition
  `!(x : group) (y : group). group_sub x y = group_add x (group_neg y)`;;

(*PARAMETRIC
new_constant ("group_sub", `:group -> group -> group`);;
*)

export_thm group_sub_def;;

(*PARAMETRIC
let group_sub_def = new_axiom
  `!(x : group) (y : group). group_sub x y = group_add x (group_neg y)`;;
*)

(* ------------------------------------------------------------------------- *)
(* Properties of group subtraction.                                          *)
(* ------------------------------------------------------------------------- *)

export_theory "group-sub-thm";;

let group_sub_left_zero = prove
  (`!x. group_sub group_zero x = group_neg x`,
   REWRITE_TAC [group_sub_def; group_add_left_zero]);;

(*PARAMETRIC
let group_sub_left_zero = new_axiom
   `!x. group_sub group_zero x = group_neg x`;;
*)

let group_sub_right_zero = prove
  (`!x. group_sub x group_zero = x`,
   REWRITE_TAC [group_sub_def; group_neg_zero; group_add_right_zero]);;

(*PARAMETRIC
let group_sub_right_zero = new_axiom
   `!x. group_sub x group_zero = x`;;
*)

let group_sub_refl = prove
  (`!x. group_sub x x = group_zero`,
   REWRITE_TAC [group_sub_def; group_add_right_neg]);;

(*PARAMETRIC
let group_sub_refl = new_axiom
   `!x. group_sub x x = group_zero`;;
*)

let group_neg_sub = prove
  (`!x y. group_neg (group_sub x y) = group_sub y x`,
   REWRITE_TAC [group_sub_def; group_neg_add; group_neg_neg]);;

(*PARAMETRIC
let group_neg_sub = new_axiom
   `!x y. group_neg (group_sub x y) = group_sub y x`;;
*)

let group_comm_left_sub = prove
  (`!x y z.
      group_add x z = group_add z x /\
      group_add y z = group_add z y ==>
      group_add (group_sub x y) z = group_add z (group_sub x y)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [group_sub_def] THEN
   MATCH_MP_TAC group_comm_left_add THEN
   ASM_REWRITE_TAC [group_comm_left_neg]);;

(*PARAMETRIC
let group_comm_left_sub = new_axiom
   `!x y z.
      group_add x z = group_add z x /\
      group_add y z = group_add z y ==>
      group_add (group_sub x y) z = group_add z (group_sub x y)`;;
*)

let group_comm_right_sub = prove
  (`!x y z.
      group_add z x = group_add x z /\
      group_add z y = group_add y z ==>
      group_add z (group_sub x y) = group_add (group_sub x y) z`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   MATCH_ACCEPT_TAC group_comm_left_sub);;

(*PARAMETRIC
let group_comm_right_sub = new_axiom
   `!x y z.
      group_add z x = group_add x z /\
      group_add z y = group_add y z ==>
      group_add z (group_sub x y) = group_add (group_sub x y) z`;;
*)

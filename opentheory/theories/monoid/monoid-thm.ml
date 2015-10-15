(* ========================================================================= *)
(* CONSEQUENCES OF THE MONOID AXIOMS                                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "monoid-thm";;

let monoid_comm_left_zero = prove
  (`!x. monoid_add monoid_zero x = monoid_add x monoid_zero`,
   REWRITE_TAC [monoid_add_left_zero; monoid_add_right_zero]);;

export_thm monoid_comm_left_zero;;

(*PARAMETRIC
let monoid_comm_left_zero = new_axiom
   `!x. monoid_add monoid_zero x = monoid_add x monoid_zero`;;
*)

let monoid_comm_right_zero = prove
  (`!x. monoid_add x monoid_zero = monoid_add monoid_zero x`,
   GEN_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_ACCEPT_TAC monoid_comm_left_zero);;

export_thm monoid_comm_right_zero;;

(*PARAMETRIC
let monoid_comm_right_zero = new_axiom
   `!x. monoid_add x monoid_zero = monoid_add monoid_zero x`;;
*)

let monoid_comm_left_add = prove
  (`!x y z.
      monoid_add x z = monoid_add z x /\
      monoid_add y z = monoid_add z y ==>
      monoid_add (monoid_add x y) z = monoid_add z (monoid_add x y)`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [monoid_add_assoc] THEN
   ASM_REWRITE_TAC [GSYM monoid_add_assoc]);;

export_thm monoid_comm_left_add;;

(*PARAMETRIC
let monoid_comm_left_add = new_axiom
   `!x y z.
      monoid_add x z = monoid_add z x /\
      monoid_add y z = monoid_add z y ==>
      monoid_add (monoid_add x y) z = monoid_add z (monoid_add x y)`;;
*)

let monoid_comm_right_add = prove
  (`!x y z.
      monoid_add z x = monoid_add x z /\
      monoid_add z y = monoid_add y z ==>
      monoid_add z (monoid_add x y) = monoid_add (monoid_add x y) z`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   MATCH_ACCEPT_TAC monoid_comm_left_add);;

export_thm monoid_comm_right_add;;

(*PARAMETRIC
let monoid_comm_right_add = new_axiom
   `!x y z.
      monoid_add z x = monoid_add x z /\
      monoid_add z y = monoid_add y z ==>
      monoid_add z (monoid_add x y) = monoid_add (monoid_add x y) z`;;
*)

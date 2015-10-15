(* ========================================================================= *)
(* THE ADDITIVE GROUP OF THE RING                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: non-commutative additive group.          *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-add-group.ml";;

(* ------------------------------------------------------------------------- *)
(* Selectively export group theorems and prove commutativity.                *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-add-thm";;

let ring_add_comm =
  let th =
      let tm = `ring_mult (ring_add ring_one ring_one) (ring_add x y)` in
      let th1 =
          (REWRITE_CONV [ring_add_left_distrib] THENC
           REWRITE_CONV [ring_add_right_distrib; ring_mult_left_one]) tm in
      let th2 =
          (REWRITE_CONV [ring_add_right_distrib] THENC
           REWRITE_CONV [ring_add_left_distrib; ring_mult_left_one]) tm in
      TRANS (SYM th1) th2 in
  prove
  (`!x y. ring_add x y = ring_add y x`,
   REPEAT GEN_TAC THEN
   MP_TAC th THEN
   REWRITE_TAC [ring_add_assoc; ring_add_left_cancel] THEN
   REWRITE_TAC [GSYM ring_add_assoc; ring_add_right_cancel]);;

export_thm ring_add_comm;;

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: commutative additive group.              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-add-comm.ml";;

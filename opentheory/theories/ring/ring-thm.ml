(* ========================================================================= *)
(* PROPERTIES OF THE RING AXIOMS, ADDITIVE GROUP AND MULTIPLICATIVE MONOID   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "ring-thm";;

let ring_mult_left_zero = prove
  (`!x. ring_mult ring_zero x = ring_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC ring_add_left_cancel_zero_imp THEN
   EXISTS_TAC `ring_mult ring_zero x` THEN
   REWRITE_TAC [GSYM ring_add_right_distrib; ring_add_left_zero]);;

export_thm ring_mult_left_zero;;

let ring_mult_right_zero = prove
  (`!x. ring_mult x ring_zero = ring_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC ring_add_right_cancel_zero_imp THEN
   EXISTS_TAC `ring_mult x ring_zero` THEN
   REWRITE_TAC [GSYM ring_add_left_distrib; ring_add_right_zero]);;

export_thm ring_mult_right_zero;;

let ring_mult_left_neg = prove
  (`!x y. ring_mult (ring_neg x) y = ring_neg (ring_mult x y)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC ring_add_left_cancel_imp THEN
   EXISTS_TAC `ring_mult x y` THEN
   REWRITE_TAC
     [ring_add_right_neg; GSYM ring_add_right_distrib;
      ring_mult_left_zero]);;

export_thm ring_mult_left_neg;;

let ring_mult_right_neg = prove
  (`!x y. ring_mult y (ring_neg x) = ring_neg (ring_mult y x)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC ring_add_right_cancel_imp THEN
   EXISTS_TAC `ring_mult y x` THEN
   REWRITE_TAC
     [ring_add_left_neg; GSYM ring_add_left_distrib;
      ring_mult_right_zero]);;

export_thm ring_mult_right_neg;;

let ring_sub_left_distrib = prove
  (`!x y z.
      ring_mult x (ring_sub y z) =
      ring_sub (ring_mult x y) (ring_mult x z)`,
   REWRITE_TAC [ring_sub_def; ring_add_left_distrib; ring_mult_right_neg]);;

export_thm ring_sub_left_distrib;;

let ring_sub_right_distrib = prove
  (`!x y z.
      ring_mult (ring_sub y z) x =
      ring_sub (ring_mult y x) (ring_mult z x)`,
   REWRITE_TAC [ring_sub_def; ring_add_right_distrib; ring_mult_left_neg]);;

export_thm ring_sub_right_distrib;;

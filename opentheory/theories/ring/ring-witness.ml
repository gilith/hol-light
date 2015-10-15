(* ========================================================================= *)
(* PARAMETRIC THEORY WITNESS FOR RINGS                                       *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "ring-witness";;

let (ring_add_left_zero,
     ring_add_left_neg,
     ring_add_assoc,
     ring_mult_left_one,
     ring_mult_assoc,
     ring_add_left_distrib,
     ring_add_right_distrib,
     ring_one_nonzero,
     ring_mult_comm,
     ring_finite) =
  let tybij = define_newtype ("x","ring") ("b",`:bool`) in
  let zero_def = new_definition `ring_zero = mk_ring F` in
  let neg_def = new_definition `!x : ring. ring_neg x = x` in
  let add_def = new_definition
    `!(x : ring) (y : ring).
       ring_add x y = mk_ring (dest_ring x <=> ~dest_ring y)` in
  let one_def = new_definition `ring_one = mk_ring T` in
  let mult_def = new_definition
    `!(x : ring) (y : ring).
       ring_mult x y = mk_ring (dest_ring x /\ dest_ring y)` in
  let cases = prove
    (`!x : ring. x = mk_ring F \/ x = mk_ring T`,
     GEN_TAC THEN
     ASM_CASES_TAC `dest_ring x` THENL
     [DISJ2_TAC;
      DISJ1_TAC] THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM (CONJUNCT1 tybij)))) THEN
     ASM_REWRITE_TAC []) in
  let induct = prove
    (`!p. p (mk_ring F) /\ p (mk_ring T) ==> !x. p x`,
     REPEAT STRIP_TAC THEN
     MP_TAC (SPEC `x : ring` cases) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC []) in
  let ring_tactic =
     REPEAT (MATCH_MP_TAC induct THEN STRIP_TAC) THEN
     ASM_REWRITE_TAC
       [tybij; zero_def; neg_def; add_def; one_def; mult_def] in
  let ring_prove goal = prove (goal,ring_tactic) in
  let add_left_zero = ring_prove `!x. ring_add ring_zero x = x` in
  let add_left_neg = ring_prove `!x. ring_add (ring_neg x) x = ring_zero` in
  let add_assoc = ring_prove
    `!x y z. ring_add (ring_add x y) z = ring_add x (ring_add y z)` in
  let mult_left_one = ring_prove `!x. ring_mult ring_one x = x` in
  let mult_comm = ring_prove `!x y. ring_mult x y = ring_mult y x` in
  let mult_assoc = ring_prove
    `!x y z. ring_mult (ring_mult x y) z = ring_mult x (ring_mult y z)` in
  let add_left_distrib = ring_prove
    `!x y z.
       ring_mult x (ring_add y z) =
       ring_add (ring_mult x y) (ring_mult x z)` in
  let add_right_distrib = ONCE_REWRITE_RULE [mult_comm] add_left_distrib in
  let one_nonzero = prove
    (`~(ring_one = ring_zero)`,
     REWRITE_TAC [one_def; zero_def] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `F <=> T` SUBST1_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM (CONJUNCT2 tybij)))) THEN
     CONV_TAC (RAND_CONV (REWR_CONV (GSYM (CONJUNCT2 tybij)))) THEN
     ASM_REWRITE_TAC []) in
  let finite = prove
    (`FINITE (UNIV : ring set)`,
     SUBGOAL_THEN `UNIV = ring_zero INSERT ring_one INSERT EMPTY`
       SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      ring_tactic;
      REWRITE_TAC [FINITE_INSERT; FINITE_EMPTY]]) in
  (add_left_zero, add_left_neg, add_assoc,
   mult_left_one, mult_assoc,
   add_left_distrib, add_right_distrib, one_nonzero,
   mult_comm, finite);;

export_thm ring_add_left_zero;;
export_thm ring_add_left_neg;;
export_thm ring_add_assoc;;
export_thm ring_mult_left_one;;
export_thm ring_mult_assoc;;
export_thm ring_add_left_distrib;;
export_thm ring_add_right_distrib;;
export_thm ring_one_nonzero;;
export_thm ring_mult_comm;;
export_thm ring_finite;;

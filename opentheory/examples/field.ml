(* ------------------------------------------------------------------------- *)
(* A parametric theory of fields.                                            *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* field *)
*)

(* The theory parameters *)

logfile "field-witness";;

let (field_add_left_zero,
     field_add_left_neg,
     field_add_assoc,
     field_add_comm,
     field_mult_left_one,
     field_mult_left_inv,
     field_mult_assoc,
     field_mult_comm,
     field_add_left_distrib,
     field_one_nonzero,
     field_finite) =
  let tybij = define_newtype ("x","field") ("b",`:bool`) in
  let zero_def = new_definition `field_zero = mk_field F` in
  let neg_def = new_definition `!x : field. field_neg x = x` in
  let add_def = new_definition
    `!(x : field) (y : field).
       field_add x y = mk_field (dest_field x <=> ~dest_field y)` in
  let one_def = new_definition `field_one = mk_field T` in
  let inv_def = new_definition `!x : field. field_inv x = x` in
  let mult_def = new_definition
    `!(x : field) (y : field).
       field_mult x y = mk_field (dest_field x /\ dest_field y)` in
  let cases = prove
    (`!x : field. x = mk_field F \/ x = mk_field T`,
     GEN_TAC THEN
     ASM_CASES_TAC `dest_field x` THENL
     [DISJ2_TAC;
      DISJ1_TAC] THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM (CONJUNCT1 tybij)))) THEN
     ASM_REWRITE_TAC []) in
  let induct = prove
    (`!p. p (mk_field F) /\ p (mk_field T) ==> !x. p x`,
     REPEAT STRIP_TAC THEN
     MP_TAC (SPEC `x : field` cases) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC []) in
  let field_tactic =
     REPEAT (MATCH_MP_TAC induct THEN STRIP_TAC) THEN
     ASM_REWRITE_TAC
       [tybij; zero_def; neg_def; add_def; one_def; inv_def; mult_def] in
  let field_prove goal = prove (goal,field_tactic) in
  let add_left_zero = field_prove `!x. field_add field_zero x = x` in
  let add_left_neg = field_prove `!x. field_add (field_neg x) x = field_zero` in
  let add_assoc = field_prove
    `!x y z. field_add (field_add x y) z = field_add x (field_add y z)` in
  let add_comm = field_prove `!x y. field_add x y = field_add y x` in
  let mult_left_one = field_prove
    `!x. ~(x = field_zero) ==> field_mult field_one x = x` in
  let mult_left_inv = field_prove
    `!x. ~(x = field_zero) ==> field_mult (field_inv x) x = field_one` in
  let mult_assoc = field_prove
    `!x y z. field_mult (field_mult x y) z = field_mult x (field_mult y z)` in
  let mult_comm = field_prove `!x y. field_mult x y = field_mult y x` in
  let mult_left_zero = field_prove
    `!x. field_mult field_zero x = field_zero` in
  let mult_left_zero = field_prove
    `!x. field_mult field_zero x = field_zero` in
  let add_left_distrib = field_prove
    `!x y z.
       field_mult x (field_add y z) =
       field_add (field_mult x y) (field_mult x z)` in
  let one_nonzero = prove
    (`~(field_one = field_zero)`,
     REWRITE_TAC [one_def; zero_def] THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `F <=> T` SUBST1_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV (GSYM (CONJUNCT2 tybij)))) THEN
     CONV_TAC (RAND_CONV (REWR_CONV (GSYM (CONJUNCT2 tybij)))) THEN
     ASM_REWRITE_TAC []) in
  let finite = prove
    (`FINITE (UNIV : field set)`,
     SUBGOAL_THEN `UNIV = field_zero INSERT field_one INSERT EMPTY`
       SUBST1_TAC THENL
     [REWRITE_TAC [EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
      field_tactic;
      REWRITE_TAC [FINITE_INSERT; FINITE_EMPTY]]) in
  (add_left_zero, add_left_neg, add_assoc, add_comm,
   mult_left_one, mult_left_inv, mult_assoc, mult_comm,
   add_left_distrib, one_nonzero, finite);;

(* Parametric theory instantiation: additive group *)

loads "opentheory/examples/field-group.ml";;

logfile "field-star-def";;

(*PARAMETRIC
(* field-star-def *)
*)

let field_star_exists = prove
  (`?x. ~(x = field_zero)`,
   EXISTS_TAC `field_one` THEN
   ACCEPT_TAC field_one_nonzero);;

let (mk_dest_field_star,dest_mk_field_star) =
  let tybij =
    new_type_definition "field_star" ("mk_field_star","dest_field_star") field_star_exists in
  CONJ_PAIR tybij;;

export_thm mk_dest_field_star;;
export_thm dest_mk_field_star;;

let field_star_tybij = CONJ mk_dest_field_star dest_mk_field_star;;

let field_star_zero_def = new_definition
  `field_star_zero = mk_field_star field_one`;;

export_thm field_star_zero_def;;

let field_star_neg_def = new_definition
  `!x. field_star_neg x = mk_field_star (field_inv (dest_field_star x))`;;

export_thm field_star_neg_def;;

let field_star_add_def = new_definition
  `!x y.
     field_star_add x y =
     mk_field_star (field_mult (dest_field_star x) (dest_field_star y))`;;

export_thm field_star_add_def;;

logfile "field-star-thm";;

(*PARAMETRIC
(* field-star-thm *)
*)

let dest_field_star_inj = prove
  (`!x y. dest_field_star x = dest_field_star y <=> x = y`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM mk_dest_field_star] THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm dest_field_star_inj;;

let dest_field_star_zero = prove
  (`dest_field_star field_star_zero = field_one`,
   REWRITE_TAC [field_star_zero_def; GSYM dest_mk_field_star] THEN
   ACCEPT_TAC field_one_nonzero);;

export_thm dest_field_star_zero;;

(***   
let dest_field_star_neg = prove
  (`!x. dest_field_star (field_star_neg x) = field_inv (dest_field_star x)`,
   GEN_TAC THEN
   REWRITE_TAC [field_star_neg_def; GSYM dest_mk_field_star] THEN
   ***
   ACCEPT_TAC field_one_nonzero);;

export_thm dest_field_star_neg;;

let dest_field_star_add = prove
  (`!x y.
      dest_field_star (field_star_add x y) =
      field_mult (dest_field_star x) (dest_field_star y)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [field_star_add_def; GSYM dest_mk_field_star]
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM mk_dest_field_star] THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm dest_field_star_add;;

let field_star_add_left_zero = prove
  (`!x. field_star_add field_star_zero x = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_field_star_inj]
   REWRITE_TAC [field_star_add_def; field_star_zero_def]

val field_mult_left_inv : thm =
  |- !x. ~(x = field_zero) ==> field_mult (field_inv x) x = field_one
val field_mult_assoc : thm =
  |- !x y z. field_mult (field_mult x y) z = field_mult x (field_mult y z)
val field_mult_comm : thm = |- !x y. field_mult x y = field_mult y x

(* Parametric theory instantiation: multiplicative group *)

loads "opentheory/examples/field-star-group.ml";;
***)

logfile_end ();;

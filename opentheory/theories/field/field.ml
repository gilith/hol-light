(* ========================================================================= *)
(* PARAMETRIC THEORY OF FIELDS                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for a parametric theory of fields.                        *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/field/field.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness for fields.                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "field-witness";;

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

export_thm field_add_left_zero;;
export_thm field_add_left_neg;;
export_thm field_add_assoc;;
export_thm field_add_comm;;
export_thm field_mult_left_one;;
export_thm field_mult_left_inv;;
export_thm field_mult_assoc;;
export_thm field_mult_comm;;
export_thm field_add_left_distrib;;
export_thm field_one_nonzero;;
export_thm field_finite;;

(* ------------------------------------------------------------------------- *)
(* Definition of field characteristic.                                       *)
(* ------------------------------------------------------------------------- *)

export_theory "field-def";;

let (num_to_field_zero,num_to_field_suc) =
    let def = new_recursive_definition num_RECURSION
          `(num_to_field 0 = field_zero) /\
           (!n. num_to_field (SUC n) = field_add field_one (num_to_field n))` in
    CONJ_PAIR def;;

(*PARAMETRIC
new_constant ("num_to_field", `:num -> field`);;
*)

export_thm num_to_field_zero;;
export_thm num_to_field_suc;;

(*PARAMETRIC
let num_to_field_zero = new_axiom
  `num_to_field 0 = field_zero`;;

let num_to_field_suc = new_axiom
  `!n. num_to_field (SUC n) = field_add field_one (num_to_field n)`;;
*)

(*BEGIN-PARAMETRIC*)
let num_to_field_def = CONJ num_to_field_zero num_to_field_suc;;
(*END-PARAMETRIC*)

let field_char_def = new_definition
  `field_char =
   if (?n. ~(n = 0) /\ num_to_field n = field_zero) then
     (minimal n. ~(n = 0) /\ num_to_field n = field_zero)
   else 0`;;

export_thm field_char_def;;

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: additive group.                          *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/field/field-group.ml";;

(* ------------------------------------------------------------------------- *)
(* Consequences of the field axioms and the additive group.                  *)
(* ------------------------------------------------------------------------- *)

export_theory "field-thm";;

let field_add_right_distrib = prove
  (`!x y z.
      field_mult (field_add y z) x =
      field_add (field_mult y x) (field_mult z x)`,
   ONCE_REWRITE_TAC [field_mult_comm] THEN
   ACCEPT_TAC field_add_left_distrib);;

export_thm field_add_right_distrib;;

let field_mult_left_zero = prove
  (`!x. field_mult field_zero x = field_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC field_add_left_cancel_zero_imp THEN
   EXISTS_TAC `field_mult field_zero x` THEN
   REWRITE_TAC [GSYM field_add_right_distrib; field_add_left_zero]);;

export_thm field_mult_left_zero;;

let field_mult_right_zero = prove
  (`!x. field_mult x field_zero = field_zero`,
   ONCE_REWRITE_TAC [field_mult_comm] THEN
   ACCEPT_TAC field_mult_left_zero);;

export_thm field_mult_left_zero;;

let field_mult_left_neg = prove
  (`!x y. field_mult (field_neg x) y = field_neg (field_mult x y)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC field_add_left_cancel_imp THEN
   EXISTS_TAC `field_mult x y` THEN
   REWRITE_TAC
     [field_add_right_neg; GSYM field_add_right_distrib;
      field_mult_left_zero]);;

export_thm field_mult_left_neg;;

let field_mult_right_neg = prove
  (`!x y. field_mult y (field_neg x) = field_neg (field_mult y x)`,
   ONCE_REWRITE_TAC [field_mult_comm] THEN
   ACCEPT_TAC field_mult_left_neg);;

export_thm field_mult_right_neg;;

let field_sub_left_distrib = prove
  (`!x y z.
      field_mult x (field_sub y z) =
      field_sub (field_mult x y) (field_mult x z)`,
   REWRITE_TAC [field_sub_def; field_add_left_distrib; field_mult_right_neg]);;

export_thm field_sub_left_distrib;;

let field_sub_right_distrib = prove
  (`!x y z.
      field_mult (field_sub y z) x =
      field_sub (field_mult y x) (field_mult z x)`,
   ONCE_REWRITE_TAC [field_mult_comm] THEN
   ACCEPT_TAC field_sub_left_distrib);;

export_thm field_sub_right_distrib;;

let field_inv_nonzero = prove
  (`!x. ~(x = field_zero) ==> ~(field_inv x = field_zero)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `x : field` field_mult_left_inv) THEN
   ASM_REWRITE_TAC [field_mult_left_zero; field_one_nonzero]);;

export_thm field_inv_nonzero;;

let field_mult_nonzero = prove
  (`!x y.
      ~(x = field_zero) /\ ~(y = field_zero) ==>
      ~(field_mult x y = field_zero)`,
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`field_inv x`; `x : field`; `y : field`]
        field_mult_assoc) THEN
   MP_TAC (SPEC `x : field` field_mult_left_inv) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [field_mult_right_zero] THEN
    MP_TAC (SPEC `y : field` field_mult_left_one) THEN
    ANTS_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     DISCH_THEN SUBST1_TAC THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm field_mult_nonzero;;

(* ------------------------------------------------------------------------- *)
(* Definition of the multiplicative group of the field.                      *)
(* ------------------------------------------------------------------------- *)

export_theory "field-star-def";;

let (mk_dest_field_star,dest_mk_field_star) =
  let exists = prove
    (`?x. ~(x = field_zero)`,
     EXISTS_TAC `field_one` THEN
     ACCEPT_TAC field_one_nonzero) in
  let tybij =
    new_type_definition "field_star"
     ("mk_field_star","dest_field_star") exists in
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

(* ------------------------------------------------------------------------- *)
(* Properties of the multiplicative group of the field.                      *)
(* ------------------------------------------------------------------------- *)

export_theory "field-star-thm";;

let dest_field_star_nonzero = prove
  (`!x. ~(dest_field_star x = field_zero)`,
   GEN_TAC THEN
   REWRITE_TAC [dest_mk_field_star] THEN
   REWRITE_TAC [mk_dest_field_star]);;

export_thm dest_field_star_nonzero;;

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

let dest_field_star_induct = prove
  (`!p. p field_zero /\ (!x. p (dest_field_star x)) ==> !x. p x`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `x = field_zero` THENL
   [ASM_REWRITE_TAC [];
    POP_ASSUM (SUBST1_TAC o SYM o REWRITE_RULE [dest_mk_field_star]) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

export_thm dest_field_star_induct;;

let dest_field_star_zero = prove
  (`dest_field_star field_star_zero = field_one`,
   REWRITE_TAC [field_star_zero_def; GSYM dest_mk_field_star] THEN
   ACCEPT_TAC field_one_nonzero);;

export_thm dest_field_star_zero;;

let dest_field_star_neg = prove
  (`!x. dest_field_star (field_star_neg x) = field_inv (dest_field_star x)`,
   GEN_TAC THEN
   REWRITE_TAC [field_star_neg_def; GSYM dest_mk_field_star] THEN
   MATCH_MP_TAC field_inv_nonzero THEN
   REWRITE_TAC [field_star_tybij]);;

export_thm dest_field_star_neg;;

let dest_field_star_add = prove
  (`!x y.
      dest_field_star (field_star_add x y) =
      field_mult (dest_field_star x) (dest_field_star y)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [field_star_add_def; GSYM dest_mk_field_star] THEN
   MATCH_MP_TAC field_mult_nonzero THEN
   REWRITE_TAC [field_star_tybij]);;

export_thm dest_field_star_add;;

let field_star_add_left_zero = prove
  (`!x. field_star_add field_star_zero x = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_field_star_inj] THEN
   REWRITE_TAC [dest_field_star_add; dest_field_star_zero] THEN
   MATCH_MP_TAC field_mult_left_one THEN
   REWRITE_TAC [field_star_tybij]);;

export_thm field_star_add_left_zero;;

let field_star_add_left_neg = prove
  (`!x. field_star_add (field_star_neg x) x = field_star_zero`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_field_star_inj] THEN
   REWRITE_TAC
     [dest_field_star_add; dest_field_star_neg; dest_field_star_zero] THEN
   MATCH_MP_TAC field_mult_left_inv THEN
   REWRITE_TAC [field_star_tybij]);;

export_thm field_star_add_left_neg;;

let field_star_add_assoc = prove
  (`!x y z.
      field_star_add (field_star_add x y) z =
      field_star_add x (field_star_add y z)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_field_star_inj] THEN
   REWRITE_TAC [dest_field_star_add] THEN
   MATCH_ACCEPT_TAC field_mult_assoc);;

export_thm field_star_add_assoc;;

let field_star_add_comm = prove
  (`!x y. field_star_add x y = field_star_add y x`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_field_star_inj] THEN
   REWRITE_TAC [dest_field_star_add] THEN
   MATCH_ACCEPT_TAC field_mult_comm);;

export_thm field_star_add_comm;;

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: multiplicative group.                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/field/field-star-group.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of field division and exponentiation.                          *)
(* ------------------------------------------------------------------------- *)

export_theory "field-mult-def";;

let field_div_def =
  let def = new_definition
    `!x y.
       field_div x y =
       if x = field_zero then field_zero else
       dest_field_star (field_star_sub (mk_field_star x) (mk_field_star y))` in
  prove
  (`!x y.
      ~(y = field_zero) ==>
      field_div x y =
      if x = field_zero then field_zero else
      dest_field_star (field_star_sub (mk_field_star x) (mk_field_star y))`,
   REWRITE_TAC [def]);;

export_thm field_div_def;;

let field_exp_def = new_definition
  `!x n.
     field_exp x n =
     if n = 0 then field_one else
     if x = field_zero then field_zero else
     dest_field_star (field_star_scale (mk_field_star x) n)`;;

export_thm field_exp_def;;

let field_mult_add_def = new_definition
  `!z x l.
     field_mult_add z x l =
     if n = 0 then field_one else
     if x = field_zero then field_zero else
     dest_field_star (field_star_scale (mk_field_star x) n)`;;

export_thm field_exp_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of field division and exponentiation.                          *)
(* ------------------------------------------------------------------------- *)

export_theory "field-mult-thm";;

let field_div_left_zero = prove
  (`!x.
      ~(x = field_zero) ==>
      field_div field_zero x = field_zero`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`field_zero`; `x : field`] field_div_def) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC []]);;

export_thm field_div_left_zero;;

let field_div_left_zero' = prove
  (`!x. field_div field_zero (dest_field_star x) = field_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC field_div_left_zero THEN
   MATCH_ACCEPT_TAC dest_field_star_nonzero);;

export_thm field_div_left_zero';;

let dest_field_star_sub = prove
  (`!x y.
      dest_field_star (field_star_sub x y) =
      field_div (dest_field_star x) (dest_field_star y)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`dest_field_star x`; `dest_field_star y`] field_div_def) THEN
   ANTS_TAC THENL
   [MATCH_ACCEPT_TAC dest_field_star_nonzero;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [dest_field_star_nonzero; mk_dest_field_star]]);;

export_thm dest_field_star_sub;;

let field_exp_left_zero = prove
  (`!n. field_exp field_zero n = if n = 0 then field_one else field_zero`,
   GEN_TAC THEN
   REWRITE_TAC [field_exp_def]);;

export_thm field_exp_left_zero;;

let dest_field_star_exp = prove
  (`!x n.
      dest_field_star (field_star_scale x n) =
      field_exp (dest_field_star x) n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [field_exp_def] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [field_star_scale_right_zero; dest_field_star_zero];
    REWRITE_TAC [dest_field_star_nonzero; mk_dest_field_star]]);;

export_thm dest_field_star_exp;;

let field_star_tactic =
    let basic =
        [mk_dest_field_star;
         dest_field_star_inj;
         dest_field_star_nonzero;
         GSYM dest_field_star_zero;
         GSYM dest_field_star_neg;
         GSYM dest_field_star_add;
         GSYM dest_field_star_sub;
         GSYM dest_field_star_exp;
         field_mult_left_zero;
         field_mult_right_zero;
         field_div_left_zero';
         field_exp_left_zero] in
    fun custom ->
      let ths = custom @ basic in
      let rewr = REWRITE_TAC ths in
      let induct =
          MATCH_MP_TAC dest_field_star_induct THEN
          CONJ_TAC THENL [rewr; GEN_TAC THEN rewr] in
      (induct THEN REPEAT induct) ORELSE rewr;;

let field_mult_left_inv' = prove
  (`!x y.
      ~(x = field_zero) ==>
      field_mult (field_inv x) (field_mult x y) = y`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_left_neg');;

export_thm field_mult_left_inv';;

let field_mult_right_inv = prove
  (`!x.
      ~(x = field_zero) ==>
      field_mult x (field_inv x) = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_neg);;

export_thm field_mult_right_inv;;

let field_mult_right_inv' = prove
  (`!x y.
      ~(x = field_zero) ==>
      field_mult x (field_mult (field_inv x) y) = y`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_neg');;

export_thm field_mult_right_inv';;

let field_mult_right_one = prove
  (`!x. field_mult x field_one = x`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_zero);;

export_thm field_mult_right_one;;

let field_mult_left_cancel_imp = prove
  (`!x y z.
      ~(x = field_zero) /\ field_mult x y = field_mult x z ==>
      y = z`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_left_cancel_imp);;

export_thm field_mult_left_cancel_imp;;

let field_mult_left_cancel = prove
  (`!x y z.
      field_mult x y = field_mult x z <=>
      x = field_zero \/ y = z`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_left_cancel);;

export_thm field_mult_left_cancel;;

let field_mult_left_cancel_one_imp = prove
  (`!x y.
      ~(x = field_zero) /\ field_mult x y = x ==>
      y = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_left_cancel_zero_imp);;

export_thm field_mult_left_cancel_one_imp;;

let field_mult_left_cancel_one = prove
  (`!x y.
      field_mult x y = x <=>
      x = field_zero \/ y = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_left_cancel_zero);;

export_thm field_mult_left_cancel_one;;

let field_mult_right_cancel_imp = prove
  (`!x y z.
      ~(x = field_zero) /\ field_mult y x = field_mult z x ==>
      y = z`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_cancel_imp);;

export_thm field_mult_right_cancel_imp;;

let field_mult_right_cancel = prove
  (`!x y z.
      field_mult y x = field_mult z x <=>
      x = field_zero \/ y = z`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_cancel);;

export_thm field_mult_right_cancel;;

let field_mult_right_cancel_one_imp = prove
  (`!x y.
     ~(x = field_zero) /\ field_mult y x = x ==>
     y = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_cancel_zero_imp);;

export_thm field_mult_right_cancel_one_imp;;

let field_mult_right_cancel_one = prove
  (`!x y. field_mult y x = x <=> x = field_zero \/ y = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_add_right_cancel_zero);;

export_thm field_mult_right_cancel_one;;

let field_inv_inj_imp = prove
  (`!x y.
      ~(x = field_zero) /\
      ~(y = field_zero) /\
      field_inv x = field_inv y ==>
      x = y`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_inj_imp);;

export_thm field_inv_inj_imp;;

let field_inv_inj = prove
  (`!x y.
      (x = field_zero <=> y = field_zero) /\
      field_inv x = field_inv y <=>
      x = y`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_inj);;

export_thm field_inv_inj;;

let field_inv_one = prove
  (`field_inv field_one = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_zero);;

export_thm field_inv_one;;

let field_inv_inv = prove
  (`!x. ~(x = field_zero) ==> field_inv (field_inv x) = x`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_neg);;

export_thm field_inv_inv;;

let field_inv_mult = prove
  (`!x y.
      ~(x = field_zero) /\
      ~(y = field_zero) ==>
      field_inv (field_mult x y) = field_mult (field_inv y) (field_inv x)`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_add);;

export_thm field_inv_mult;;

let field_div_left_one = prove
  (`!x.
      ~(x = field_zero) ==>
      field_div field_one x = field_inv x`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_sub_left_zero);;

export_thm field_div_left_one;;

let field_div_right_one = prove
  (`!x. field_div x field_one = x`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_sub_right_zero);;

export_thm field_div_right_one;;

let field_div_refl = prove
  (`!x.
      ~(x = field_zero) ==>
      field_div x x = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_sub_refl);;

export_thm field_div_refl;;

let field_inv_div = prove
  (`!x y.
      ~(x = field_zero) /\ ~(y = field_zero) ==>
      field_inv (field_div x y) = field_div y x`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_neg_sub);;

export_thm field_inv_div;;

let field_exp_right_zero = prove
  (`!x. field_exp x 0 = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_scale_right_zero);;

export_thm field_exp_right_zero;;

let field_exp_right_suc = prove
  (`!x n. field_exp x (SUC n) = field_mult x (field_exp x n)`,
   field_star_tactic [NOT_SUC] THEN
   MATCH_ACCEPT_TAC field_star_scale_right_suc);;

export_thm field_exp_right_suc;;

let field_exp_left_one = prove
  (`!n. field_exp field_one n = field_one`,
   field_star_tactic [] THEN
   MATCH_ACCEPT_TAC field_star_scale_left_zero);;

export_thm field_exp_left_one;;

let field_exp_right_one = prove
  (`!x. field_exp x 1 = x`,
   field_star_tactic [] THEN
   NUM_REDUCE_TAC THEN
   MATCH_ACCEPT_TAC field_star_scale_right_one);;

export_thm field_exp_right_one;;

let field_exp_right_two = prove
  (`!x. field_exp x 2 = field_mult x x`,
   field_star_tactic [] THEN
   NUM_REDUCE_TAC THEN
   MATCH_ACCEPT_TAC field_star_scale_right_two);;

export_thm field_exp_right_two;;

let field_exp_right_add = prove
  (`!x m n.
      field_exp x (m + n) = field_mult (field_exp x m) (field_exp x n)`,
   field_star_tactic [] THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC [ADD_EQ_0] THEN
    BOOL_CASES_TAC `m = 0` THEN
    BOOL_CASES_TAC `n = 0` THEN
    field_star_tactic [field_star_add_left_zero];
    MATCH_ACCEPT_TAC field_star_scale_right_add]);;

export_thm field_exp_right_add;;

let field_exp_right_suc' = prove
  (`!x n. field_exp x (SUC n) = field_mult (field_exp x n) x`,
   field_star_tactic [NOT_SUC] THEN
   MATCH_ACCEPT_TAC field_star_scale_right_suc');;

export_thm field_exp_right_suc';;

let field_exp_right_mult = prove
  (`!x m n. field_exp x (m * n) = field_exp (field_exp x m) n`,
   field_star_tactic [] THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC [MULT_EQ_0; field_exp_def] THEN
    BOOL_CASES_TAC `m = 0` THEN
    BOOL_CASES_TAC `n = 0` THEN
    field_star_tactic [field_star_scale_left_zero];
    MATCH_ACCEPT_TAC field_star_scale_right_mult]);;

export_thm field_exp_right_mult;;

(***

(* field_star-mult-mult-def *)

new_constant ("field_exp_mult", `:field_star -> field_star -> bool list -> field_star`);;

let field_exp_mult_nil = new_axiom
    `!z x. field_exp_mult z x [] = z`;;

let field_exp_mult_cons = new_axiom
     `!z x h t.
        field_exp_mult z x (CONS h t) =
        field_exp_mult (if h then field_mult z x else z) (field_mult x x) t`;;

let field_exp_mult_def = CONJ field_exp_mult_nil field_exp_mult_cons;;

(* field_star-mult-mult-thm *)

let field_exp_mult_invariant = new_axiom
   `!z x l.
      field_exp_mult z x l =
      field_mult z (field_exp x (bits_to_num l))`;;

let field_exp_mult_correct = new_axiom
   `!x n.
      field_exp x n =
      field_exp_mult field_one x (num_to_bits n)`;;

(* field_star-mult-div-def *)

new_constant
  ("field_exp_div",
   `:bool -> field_star -> field_star -> field_star -> field_star -> bool list -> field_star`);;

let field_exp_div_nil = new_axiom
    `(!b n d f p.
        field_exp_div b n d f p [] =
        if b then field_div n d else field_div d n)`;;

let field_exp_div_cons = new_axiom
    `(!b n d f p h t.
        field_exp_div b n d f p (CONS h t) =
        let s = field_div p f in
        field_exp_div (~b) d (if h then field_div n s else n) s f t)`;;

let field_exp_div_def = CONJ field_exp_div_nil field_exp_div_cons;;

(* field_star-mult-div-thm *)

let field_exp_div_invariant = new_axiom
   `!x n d f p l.
      field_mult x n = field_mult n x /\
      field_mult x d = field_mult d x ==>
      field_exp_div T n d (field_exp x f) (field_inv (field_exp x p)) l =
      field_mult (field_div n d) (field_exp x (decode_fib_dest f p l)) /\
      field_exp_div F n d (field_inv (field_exp x f)) (field_exp x p) l =
      field_mult (field_div d n) (field_exp x (decode_fib_dest f p l))`;;

let field_exp_div_correct = new_axiom
   `!x n.
      field_exp x n =
      field_exp_div T field_one field_one x field_one (encode_fib n)`;;

(* field_star-crypt-def *)

new_constant
  ("field_star_elgamal_encrypt",
   `:field_star -> field_star -> field_star -> num -> field_star # field_star`);;

let field_star_elgamal_encrypt_def = new_axiom
  `!g h m k.
     field_star_elgamal_encrypt g h m k =
     (field_exp g k, field_mult (field_exp h k) m)`;;

new_constant
  ("field_star_elgamal_decrypt",
   `:num -> field_star # field_star -> field_star`);;

let field_star_elgamal_decrypt_def = new_axiom
  `!x a b.
     field_star_elgamal_decrypt x (a,b) =
     field_mult (field_inv (field_exp a x)) b`;;

(* field_star-crypt-thm *)

let field_star_elgamal_correct = new_axiom
   `!g h m k x.
      (h = field_exp g x) ==>
      (field_star_elgamal_decrypt x (field_star_elgamal_encrypt g h m k) = m)`;;

(* field_star-abelian *)

let field_mult_comm' = new_axiom
   `!x y z. field_mult x (field_mult y z) = field_mult y (field_mult x z)`;;
***)

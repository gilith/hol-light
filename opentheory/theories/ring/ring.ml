(* ========================================================================= *)
(* PARAMETRIC THEORY OF RINGS                                                *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for a parametric theory of rings.                         *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/ring/ring.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness for rings.                                      *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-witness.ml";;

(* ------------------------------------------------------------------------- *)
(* The additive group of the ring.                                           *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-add.ml";;

(* ------------------------------------------------------------------------- *)
(* The multiplicative monoid of the ring.                                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-mult.ml";;

(* ------------------------------------------------------------------------- *)
(* Properties of the ring axioms, additive group and multiplicative monoid.  *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* The characteristic of the ring.                                           *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-char.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of the multiplicative group of ring units.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-unit-def";;

let is_ring_unit_def = new_definition
  `!x. is_ring_unit x <=> ?y. ring_mult y x = ring_one`;;

export_thm is_ring_unit_def;;

let (mk_dest_ring_unit,dest_mk_ring_unit) =
  let exists = prove
    (`?x. is_ring_unit x`,
     EXISTS_TAC `ring_one` THEN
     REWRITE_TAC [is_ring_unit_def] THEN
     EXISTS_TAC `ring_one` THEN
     MATCH_ACCEPT_TAC ring_mult_left_one) in
  let tybij =
    new_type_definition "ring_unit"
     ("mk_ring_unit","dest_ring_unit") exists in
  CONJ_PAIR tybij;;

export_thm mk_dest_ring_unit;;
export_thm dest_mk_ring_unit;;

let ring_unit_tybij = CONJ mk_dest_ring_unit dest_mk_ring_unit;;

let ring_unit_zero_def = new_definition
  `ring_unit_zero = mk_ring_unit ring_one`;;

export_thm ring_unit_zero_def;;

let ring_unit_add_def = new_definition
  `!x y.
     ring_unit_add x y =
     mk_ring_unit (ring_mult (dest_ring_unit x) (dest_ring_unit y))`;;

export_thm ring_unit_add_def;;

let ring_unit_neg_def =
  let exists = prove
    (`!x. ?y. ring_unit_add y x = ring_unit_zero`,
     GEN_TAC THEN
     REWRITE_TAC [ring_unit_add_def; ring_unit_zero_def] THEN
     MP_TAC ((REWRITE_RULE [is_ring_unit_def; mk_dest_ring_unit] o
              SPEC `dest_ring_unit x`) dest_mk_ring_unit) THEN
     STRIP_TAC THEN
     EXISTS_TAC `mk_ring_unit y` THEN
     AP_TERM_TAC THEN
     SUBGOAL_THEN `dest_ring_unit (mk_ring_unit y) = y`
       (fun th -> ASM_REWRITE_TAC [th]) THEN
     REWRITE_TAC [GSYM dest_mk_ring_unit; is_ring_unit_def] THEN
     EXISTS_TAC `dest_ring_unit x` THEN
     ONCE_REWRITE_TAC [ring_mult_comm] THEN
     FIRST_ASSUM ACCEPT_TAC) in
  new_specification ["ring_unit_neg"]
    (REWRITE_RULE [SKOLEM_THM] exists);;

export_thm ring_unit_neg_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the multiplicative group of ring units.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-unit-thm";;

let is_ring_unit_one = prove
  (`is_ring_unit ring_one`,
   REWRITE_TAC [is_ring_unit_def] THEN
   EXISTS_TAC `ring_one` THEN
   MATCH_MP_TAC ring_mult_left_one THEN
   ACCEPT_TAC ring_one_nonzero);;

export_thm is_ring_unit_one;;

let is_ring_unit_mult = prove
  (`!x y.
      is_ring_unit x /\ is_ring_unit y ==>
      is_ring_unit (ring_mult x y)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_ring_unit_def] THEN
   DISCH_THEN
     (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x' : ring` ASSUME_TAC)
        (X_CHOOSE_THEN `y' : ring` ASSUME_TAC)) THEN
   EXISTS_TAC `ring_mult x' y'` THEN
   CONV_TAC
     (LAND_CONV
       ((RAND_CONV (REWR_CONV ring_mult_comm)) THENC
        REWR_CONV ring_mult_assoc THENC
        RAND_CONV (REWR_CONV (GSYM ring_mult_assoc)))) THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC
     (LAND_CONV
       (REWR_CONV (GSYM ring_mult_assoc) THENC
        LAND_CONV (REWR_CONV ring_mult_comm) THENC
        REWR_CONV ring_mult_assoc)) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC ring_mult_left_one THEN
   ACCEPT_TAC ring_one_nonzero);;

export_thm is_ring_unit_mult;;

(***
let dest_ring_unit_nonzero = prove
  (`!x. ~(dest_ring_unit x = ring_zero)`,
   GEN_TAC THEN
   REWRITE_TAC [dest_mk_ring_unit] THEN
   REWRITE_TAC [mk_dest_ring_unit]);;

export_thm dest_ring_unit_nonzero;;

let dest_ring_unit_inj = prove
  (`!x y. dest_ring_unit x = dest_ring_unit y <=> x = y`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM mk_dest_ring_unit] THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]);;

export_thm dest_ring_unit_inj;;

let dest_ring_unit_induct = prove
  (`!p. p ring_zero /\ (!x. p (dest_ring_unit x)) ==> !x. p x`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `x = ring_zero` THENL
   [ASM_REWRITE_TAC [];
    POP_ASSUM (SUBST1_TAC o SYM o REWRITE_RULE [dest_mk_ring_unit]) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC]);;

export_thm dest_ring_unit_induct;;

let dest_ring_unit_zero = prove
  (`dest_ring_unit ring_unit_zero = ring_one`,
   REWRITE_TAC [ring_unit_zero_def; GSYM dest_mk_ring_unit] THEN
   ACCEPT_TAC ring_one_nonzero);;

export_thm dest_ring_unit_zero;;

let dest_ring_unit_neg = prove
  (`!x. dest_ring_unit (ring_unit_neg x) = ring_inv (dest_ring_unit x)`,
   GEN_TAC THEN
   REWRITE_TAC [ring_unit_neg_def; GSYM dest_mk_ring_unit] THEN
   MATCH_MP_TAC ring_inv_nonzero THEN
   REWRITE_TAC [ring_unit_tybij]);;

export_thm dest_ring_unit_neg;;

let dest_ring_unit_add = prove
  (`!x y.
      dest_ring_unit (ring_unit_add x y) =
      ring_mult (dest_ring_unit x) (dest_ring_unit y)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [ring_unit_add_def; GSYM dest_mk_ring_unit] THEN
   MATCH_MP_TAC ring_mult_nonzero THEN
   REWRITE_TAC [ring_unit_tybij]);;

export_thm dest_ring_unit_add;;

let ring_unit_add_left_zero = prove
  (`!x. ring_unit_add ring_unit_zero x = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_ring_unit_inj] THEN
   REWRITE_TAC [dest_ring_unit_add; dest_ring_unit_zero] THEN
   MATCH_MP_TAC ring_mult_left_one THEN
   REWRITE_TAC [ring_unit_tybij]);;

export_thm ring_unit_add_left_zero;;

let ring_unit_add_left_neg = prove
  (`!x. ring_unit_add (ring_unit_neg x) x = ring_unit_zero`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_ring_unit_inj] THEN
   REWRITE_TAC
     [dest_ring_unit_add; dest_ring_unit_neg; dest_ring_unit_zero] THEN
   MATCH_MP_TAC ring_mult_left_inv THEN
   REWRITE_TAC [ring_unit_tybij]);;

export_thm ring_unit_add_left_neg;;

let ring_unit_add_assoc = prove
  (`!x y z.
      ring_unit_add (ring_unit_add x y) z =
      ring_unit_add x (ring_unit_add y z)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_ring_unit_inj] THEN
   REWRITE_TAC [dest_ring_unit_add] THEN
   MATCH_ACCEPT_TAC ring_mult_assoc);;

export_thm ring_unit_add_assoc;;

let ring_unit_add_comm = prove
  (`!x y. ring_unit_add x y = ring_unit_add y x`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM dest_ring_unit_inj] THEN
   REWRITE_TAC [dest_ring_unit_add] THEN
   MATCH_ACCEPT_TAC ring_mult_comm);;

export_thm ring_unit_add_comm;;

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: multiplicative group.                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/ring/ring-unit-group.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of ring division and exponentiation.                           *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-mult-def";;

let ring_div_def =
  let def = new_definition
    `!x y.
       ring_div x y =
       if x = ring_zero then ring_zero else
       dest_ring_unit (ring_unit_sub (mk_ring_unit x) (mk_ring_unit y))` in
  prove
  (`!x y.
      ~(y = ring_zero) ==>
      ring_div x y =
      if x = ring_zero then ring_zero else
      dest_ring_unit (ring_unit_sub (mk_ring_unit x) (mk_ring_unit y))`,
   REWRITE_TAC [def]);;

export_thm ring_div_def;;

let ring_exp_def = new_definition
  `!x n.
     ring_exp x n =
     if n = 0 then ring_one else
     if x = ring_zero then ring_zero else
     dest_ring_unit (ring_unit_scale (mk_ring_unit x) n)`;;

export_thm ring_exp_def;;

let ring_mult_add_def = new_definition
  `!z x l.
     ring_mult_add z x l =
     if n = 0 then ring_one else
     if x = ring_zero then ring_zero else
     dest_ring_unit (ring_unit_scale (mk_ring_unit x) n)`;;

export_thm ring_exp_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of ring division and exponentiation.                           *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-mult-thm";;

let ring_div_left_zero = prove
  (`!x.
      ~(x = ring_zero) ==>
      ring_div ring_zero x = ring_zero`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`ring_zero`; `x : ring`] ring_div_def) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC []]);;

export_thm ring_div_left_zero;;

let ring_div_left_zero' = prove
  (`!x. ring_div ring_zero (dest_ring_unit x) = ring_zero`,
   GEN_TAC THEN
   MATCH_MP_TAC ring_div_left_zero THEN
   MATCH_ACCEPT_TAC dest_ring_unit_nonzero);;

export_thm ring_div_left_zero';;

let dest_ring_unit_sub = prove
  (`!x y.
      dest_ring_unit (ring_unit_sub x y) =
      ring_div (dest_ring_unit x) (dest_ring_unit y)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`dest_ring_unit x`; `dest_ring_unit y`] ring_div_def) THEN
   ANTS_TAC THENL
   [MATCH_ACCEPT_TAC dest_ring_unit_nonzero;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [dest_ring_unit_nonzero; mk_dest_ring_unit]]);;

export_thm dest_ring_unit_sub;;

let ring_exp_left_zero = prove
  (`!n. ring_exp ring_zero n = if n = 0 then ring_one else ring_zero`,
   GEN_TAC THEN
   REWRITE_TAC [ring_exp_def]);;

export_thm ring_exp_left_zero;;

let dest_ring_unit_exp = prove
  (`!x n.
      dest_ring_unit (ring_unit_scale x n) =
      ring_exp (dest_ring_unit x) n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [ring_exp_def] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [ring_unit_scale_right_zero; dest_ring_unit_zero];
    REWRITE_TAC [dest_ring_unit_nonzero; mk_dest_ring_unit]]);;

export_thm dest_ring_unit_exp;;

let ring_unit_tactic =
    let basic =
        [mk_dest_ring_unit;
         dest_ring_unit_inj;
         dest_ring_unit_nonzero;
         GSYM dest_ring_unit_zero;
         GSYM dest_ring_unit_neg;
         GSYM dest_ring_unit_add;
         GSYM dest_ring_unit_sub;
         GSYM dest_ring_unit_exp;
         ring_mult_left_zero;
         ring_mult_right_zero;
         ring_div_left_zero';
         ring_exp_left_zero] in
    fun custom ->
      let ths = custom @ basic in
      let rewr = REWRITE_TAC ths in
      let induct =
          MATCH_MP_TAC dest_ring_unit_induct THEN
          CONJ_TAC THENL [rewr; GEN_TAC THEN rewr] in
      (induct THEN REPEAT induct) ORELSE rewr;;

let ring_mult_left_inv' = prove
  (`!x y.
      ~(x = ring_zero) ==>
      ring_mult (ring_inv x) (ring_mult x y) = y`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_left_neg');;

export_thm ring_mult_left_inv';;

let ring_mult_right_inv = prove
  (`!x.
      ~(x = ring_zero) ==>
      ring_mult x (ring_inv x) = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_neg);;

export_thm ring_mult_right_inv;;

let ring_mult_right_inv' = prove
  (`!x y.
      ~(x = ring_zero) ==>
      ring_mult x (ring_mult (ring_inv x) y) = y`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_neg');;

export_thm ring_mult_right_inv';;

let ring_mult_right_one = prove
  (`!x. ring_mult x ring_one = x`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_zero);;

export_thm ring_mult_right_one;;

let ring_mult_left_cancel_imp = prove
  (`!x y z.
      ~(x = ring_zero) /\ ring_mult x y = ring_mult x z ==>
      y = z`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_left_cancel_imp);;

export_thm ring_mult_left_cancel_imp;;

let ring_mult_left_cancel = prove
  (`!x y z.
      ring_mult x y = ring_mult x z <=>
      x = ring_zero \/ y = z`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_left_cancel);;

export_thm ring_mult_left_cancel;;

let ring_mult_left_cancel_one_imp = prove
  (`!x y.
      ~(x = ring_zero) /\ ring_mult x y = x ==>
      y = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_left_cancel_zero_imp);;

export_thm ring_mult_left_cancel_one_imp;;

let ring_mult_left_cancel_one = prove
  (`!x y.
      ring_mult x y = x <=>
      x = ring_zero \/ y = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_left_cancel_zero);;

export_thm ring_mult_left_cancel_one;;

let ring_mult_right_cancel_imp = prove
  (`!x y z.
      ~(x = ring_zero) /\ ring_mult y x = ring_mult z x ==>
      y = z`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_cancel_imp);;

export_thm ring_mult_right_cancel_imp;;

let ring_mult_right_cancel = prove
  (`!x y z.
      ring_mult y x = ring_mult z x <=>
      x = ring_zero \/ y = z`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_cancel);;

export_thm ring_mult_right_cancel;;

let ring_mult_right_cancel_one_imp = prove
  (`!x y.
     ~(x = ring_zero) /\ ring_mult y x = x ==>
     y = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_cancel_zero_imp);;

export_thm ring_mult_right_cancel_one_imp;;

let ring_mult_right_cancel_one = prove
  (`!x y. ring_mult y x = x <=> x = ring_zero \/ y = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_add_right_cancel_zero);;

export_thm ring_mult_right_cancel_one;;

let ring_inv_inj_imp = prove
  (`!x y.
      ~(x = ring_zero) /\
      ~(y = ring_zero) /\
      ring_inv x = ring_inv y ==>
      x = y`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_inj_imp);;

export_thm ring_inv_inj_imp;;

let ring_inv_inj = prove
  (`!x y.
      (x = ring_zero <=> y = ring_zero) /\
      ring_inv x = ring_inv y <=>
      x = y`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_inj);;

export_thm ring_inv_inj;;

let ring_inv_one = prove
  (`ring_inv ring_one = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_zero);;

export_thm ring_inv_one;;

let ring_inv_inv = prove
  (`!x. ~(x = ring_zero) ==> ring_inv (ring_inv x) = x`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_neg);;

export_thm ring_inv_inv;;

let ring_inv_mult = prove
  (`!x y.
      ~(x = ring_zero) /\
      ~(y = ring_zero) ==>
      ring_inv (ring_mult x y) = ring_mult (ring_inv y) (ring_inv x)`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_add);;

export_thm ring_inv_mult;;

let ring_div_left_one = prove
  (`!x.
      ~(x = ring_zero) ==>
      ring_div ring_one x = ring_inv x`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_sub_left_zero);;

export_thm ring_div_left_one;;

let ring_div_right_one = prove
  (`!x. ring_div x ring_one = x`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_sub_right_zero);;

export_thm ring_div_right_one;;

let ring_div_refl = prove
  (`!x.
      ~(x = ring_zero) ==>
      ring_div x x = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_sub_refl);;

export_thm ring_div_refl;;

let ring_inv_div = prove
  (`!x y.
      ~(x = ring_zero) /\ ~(y = ring_zero) ==>
      ring_inv (ring_div x y) = ring_div y x`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_neg_sub);;

export_thm ring_inv_div;;

let ring_exp_right_zero = prove
  (`!x. ring_exp x 0 = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_scale_right_zero);;

export_thm ring_exp_right_zero;;

let ring_exp_right_suc = prove
  (`!x n. ring_exp x (SUC n) = ring_mult x (ring_exp x n)`,
   ring_unit_tactic [NOT_SUC] THEN
   MATCH_ACCEPT_TAC ring_unit_scale_right_suc);;

export_thm ring_exp_right_suc;;

let ring_exp_left_one = prove
  (`!n. ring_exp ring_one n = ring_one`,
   ring_unit_tactic [] THEN
   MATCH_ACCEPT_TAC ring_unit_scale_left_zero);;

export_thm ring_exp_left_one;;

let ring_exp_right_one = prove
  (`!x. ring_exp x 1 = x`,
   ring_unit_tactic [] THEN
   NUM_REDUCE_TAC THEN
   MATCH_ACCEPT_TAC ring_unit_scale_right_one);;

export_thm ring_exp_right_one;;

let ring_exp_right_two = prove
  (`!x. ring_exp x 2 = ring_mult x x`,
   ring_unit_tactic [] THEN
   NUM_REDUCE_TAC THEN
   MATCH_ACCEPT_TAC ring_unit_scale_right_two);;

export_thm ring_exp_right_two;;

let ring_exp_right_add = prove
  (`!x m n.
      ring_exp x (m + n) = ring_mult (ring_exp x m) (ring_exp x n)`,
   ring_unit_tactic [] THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC [ADD_EQ_0] THEN
    BOOL_CASES_TAC `m = 0` THEN
    BOOL_CASES_TAC `n = 0` THEN
    ring_unit_tactic [ring_unit_add_left_zero];
    MATCH_ACCEPT_TAC ring_unit_scale_right_add]);;

export_thm ring_exp_right_add;;

let ring_exp_right_suc' = prove
  (`!x n. ring_exp x (SUC n) = ring_mult (ring_exp x n) x`,
   ring_unit_tactic [NOT_SUC] THEN
   MATCH_ACCEPT_TAC ring_unit_scale_right_suc');;

export_thm ring_exp_right_suc';;

let ring_exp_right_mult = prove
  (`!x m n. ring_exp x (m * n) = ring_exp (ring_exp x m) n`,
   ring_unit_tactic [] THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC [MULT_EQ_0; ring_exp_def] THEN
    BOOL_CASES_TAC `m = 0` THEN
    BOOL_CASES_TAC `n = 0` THEN
    ring_unit_tactic [ring_unit_scale_left_zero];
    MATCH_ACCEPT_TAC ring_unit_scale_right_mult]);;

export_thm ring_exp_right_mult;;

(***

(* ring_unit-mult-mult-def *)

new_constant ("ring_exp_mult", `:ring_unit -> ring_unit -> bool list -> ring_unit`);;

let ring_exp_mult_nil = new_axiom
    `!z x. ring_exp_mult z x [] = z`;;

let ring_exp_mult_cons = new_axiom
     `!z x h t.
        ring_exp_mult z x (CONS h t) =
        ring_exp_mult (if h then ring_mult z x else z) (ring_mult x x) t`;;

let ring_exp_mult_def = CONJ ring_exp_mult_nil ring_exp_mult_cons;;

(* ring_unit-mult-mult-thm *)

let ring_exp_mult_invariant = new_axiom
   `!z x l.
      ring_exp_mult z x l =
      ring_mult z (ring_exp x (bits_to_num l))`;;

let ring_exp_mult_correct = new_axiom
   `!x n.
      ring_exp x n =
      ring_exp_mult ring_one x (num_to_bits n)`;;

(* ring_unit-mult-div-def *)

new_constant
  ("ring_exp_div",
   `:bool -> ring_unit -> ring_unit -> ring_unit -> ring_unit -> bool list -> ring_unit`);;

let ring_exp_div_nil = new_axiom
    `(!b n d f p.
        ring_exp_div b n d f p [] =
        if b then ring_div n d else ring_div d n)`;;

let ring_exp_div_cons = new_axiom
    `(!b n d f p h t.
        ring_exp_div b n d f p (CONS h t) =
        let s = ring_div p f in
        ring_exp_div (~b) d (if h then ring_div n s else n) s f t)`;;

let ring_exp_div_def = CONJ ring_exp_div_nil ring_exp_div_cons;;

(* ring_unit-mult-div-thm *)

let ring_exp_div_invariant = new_axiom
   `!x n d f p l.
      ring_mult x n = ring_mult n x /\
      ring_mult x d = ring_mult d x ==>
      ring_exp_div T n d (ring_exp x f) (ring_inv (ring_exp x p)) l =
      ring_mult (ring_div n d) (ring_exp x (decode_fib_dest f p l)) /\
      ring_exp_div F n d (ring_inv (ring_exp x f)) (ring_exp x p) l =
      ring_mult (ring_div d n) (ring_exp x (decode_fib_dest f p l))`;;

let ring_exp_div_correct = new_axiom
   `!x n.
      ring_exp x n =
      ring_exp_div T ring_one ring_one x ring_one (encode_fib n)`;;

(* ring_unit-crypt-def *)

new_constant
  ("ring_unit_elgamal_encrypt",
   `:ring_unit -> ring_unit -> ring_unit -> num -> ring_unit # ring_unit`);;

let ring_unit_elgamal_encrypt_def = new_axiom
  `!g h m k.
     ring_unit_elgamal_encrypt g h m k =
     (ring_exp g k, ring_mult (ring_exp h k) m)`;;

new_constant
  ("ring_unit_elgamal_decrypt",
   `:num -> ring_unit # ring_unit -> ring_unit`);;

let ring_unit_elgamal_decrypt_def = new_axiom
  `!x a b.
     ring_unit_elgamal_decrypt x (a,b) =
     ring_mult (ring_inv (ring_exp a x)) b`;;

(* ring_unit-crypt-thm *)

let ring_unit_elgamal_correct = new_axiom
   `!g h m k x.
      (h = ring_exp g x) ==>
      (ring_unit_elgamal_decrypt x (ring_unit_elgamal_encrypt g h m k) = m)`;;

(* ring-unit-abelian *)

let ring_mult_comm' = new_axiom
   `!x y z. ring_mult x (ring_mult y z) = ring_mult y (ring_mult x z)`;;
***)
***)

(* ========================================================================= *)
(* GROUP MULTIPLICATION                                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Parametric theory instantiation: group multiplication is monoid           *)
(* multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/group/group-mult-monoid.ml";;

(* ------------------------------------------------------------------------- *)
(* Properties of group multiplication.                                       *)
(* ------------------------------------------------------------------------- *)

export_theory "group-mult-thm";;

let group_neg_mult = prove
  (`!x n. group_neg (group_mult x n) = group_mult (group_neg x) n`,
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [group_mult_right_zero; group_neg_zero];
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV group_mult_right_suc)) THENC
              RAND_CONV (REWR_CONV group_mult_right_suc')) THEN
    ASM_REWRITE_TAC [group_neg_add]]);;

(*PARAMETRIC
let group_neg_mult = new_axiom
   `!x n. group_neg (group_mult x n) = group_mult (group_neg x) n`;;
*)

(* ------------------------------------------------------------------------- *)
(* Definition of group multiplication by repeated subtraction.               *)
(* ------------------------------------------------------------------------- *)

export_theory "group-mult-sub-def";;

let (group_mult_sub_nil,group_mult_sub_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!b n d f p.
        group_mult_sub b n d f p [] =
        if b then group_sub n d else group_sub d n) /\
     (!b n d f p h t.
        group_mult_sub b n d f p (CONS h t) =
        let s = group_sub p f in
        group_mult_sub (~b) d (if h then group_sub n s else n) s f t)` in
  CONJ_PAIR def;;

(*PARAMETRIC
new_constant
  ("group_mult_sub",
   `:bool -> group -> group -> group -> group -> bool list -> group`);;
*)

export_thm group_mult_sub_nil;;
export_thm group_mult_sub_cons;;

(*PARAMETRIC
let group_mult_sub_nil = new_axiom
    `(!b n d f p.
        group_mult_sub b n d f p [] =
        if b then group_sub n d else group_sub d n)`;;

let group_mult_sub_cons = new_axiom
    `(!b n d f p h t.
        group_mult_sub b n d f p (CONS h t) =
        let s = group_sub p f in
        group_mult_sub (~b) d (if h then group_sub n s else n) s f t)`;;
*)

(*BEGIN-PARAMETRIC*)
let group_mult_sub_def = CONJ group_mult_sub_nil group_mult_sub_cons;;
(*END-PARAMETRIC*)

(* ------------------------------------------------------------------------- *)
(* Correctness of group multiplication by repeated subtraction.              *)
(* ------------------------------------------------------------------------- *)

export_theory "group-mult-sub-thm";;

let group_mult_sub_invariant = prove
  (`!x n d f p l.
      group_add x n = group_add n x /\
      group_add x d = group_add d x ==>
      group_mult_sub T n d (group_mult x f) (group_neg (group_mult x p)) l =
      group_add (group_sub n d) (group_mult x (decode_fib_dest f p l)) /\
      group_mult_sub F n d (group_neg (group_mult x f)) (group_mult x p) l =
      group_add (group_sub d n) (group_mult x (decode_fib_dest f p l))`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`p : num`, `p : num`) THEN
   SPEC_TAC (`f : num`, `f : num`) THEN
   SPEC_TAC (`d : group`, `d : group`) THEN
   SPEC_TAC (`n : group`, `n : group`) THEN
   SPEC_TAC (`l : bool list`, `l : bool list`) THEN
   LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC
      [group_mult_def; decode_fib_dest_def; group_mult_sub_def;
       group_add_right_zero];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [group_mult_def; decode_fib_dest_def; group_mult_sub_def;
      LET_DEF; LET_END_DEF; ADD_CLAUSES] THEN
   REWRITE_TAC
     [group_sub_def; group_neg_neg; GSYM group_neg_add;
      GSYM group_mult_right_add] THEN
   SUBST1_TAC (SPECL [`p : num`; `f : num`] ADD_SYM) THEN
   SPEC_TAC (`f + p : num`, `p : num`) THEN
   GEN_TAC THEN
   BOOL_CASES_TAC `h : bool` THENL
   [REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM
       (MP_TAC o
        SPECL
          [`d : group`;
           `group_add n (group_mult x p)`;
           `p : num`;
           `f : num`]) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC group_comm_right_add THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC group_comm_right_mult THEN
      REFL_TAC;
      DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
      REWRITE_TAC
        [group_add_assoc; group_sub_def; group_mult_right_add;
         group_add_left_cancel] THEN
      REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
      MATCH_MP_TAC group_comm_right_neg_imp THEN
      MATCH_MP_TAC group_comm_left_mult THEN
      FIRST_ASSUM ACCEPT_TAC];
     FIRST_X_ASSUM
       (MP_TAC o
        SPECL
          [`d : group`;
           `group_add n (group_neg (group_mult x p))`;
           `p : num`;
           `f : num`]) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC group_comm_right_add THEN
      ASM_REWRITE_TAC [group_comm_right_neg] THEN
      MATCH_MP_TAC group_comm_right_mult THEN
      REFL_TAC;
      DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
      REWRITE_TAC
        [group_add_assoc; group_sub_def; group_mult_right_add;
         group_add_left_cancel; group_neg_add; group_neg_neg] THEN
      REWRITE_TAC [GSYM group_add_assoc; group_add_right_cancel] THEN
      MATCH_MP_TAC group_comm_right_neg_imp THEN
      MATCH_MP_TAC group_comm_left_mult THEN
      FIRST_ASSUM ACCEPT_TAC]];
    REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM
       (MP_TAC o
        SPECL
          [`d : group`;
           `n : group`;
           `p : num`;
           `f : num`]) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      DISCH_THEN (SUBST1_TAC o CONJUNCT2) THEN
      REWRITE_TAC [group_sub_def]];
     FIRST_X_ASSUM
       (MP_TAC o
        SPECL
          [`d : group`;
           `n : group`;
           `p : num`;
           `f : num`]) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
      REWRITE_TAC [group_sub_def]]]]);;

export_thm group_mult_sub_invariant;;

(*PARAMETRIC
let group_mult_sub_invariant = new_axiom
   `!x n d f p l.
      group_add x n = group_add n x /\
      group_add x d = group_add d x ==>
      group_mult_sub T n d (group_mult x f) (group_neg (group_mult x p)) l =
      group_add (group_sub n d) (group_mult x (decode_fib_dest f p l)) /\
      group_mult_sub F n d (group_neg (group_mult x f)) (group_mult x p) l =
      group_add (group_sub d n) (group_mult x (decode_fib_dest f p l))`;;
*)

let group_mult_sub_correct = prove
  (`!x n.
      group_mult x n =
      group_mult_sub T group_zero group_zero x group_zero (encode_fib n)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`x : group`; `group_zero`; `group_zero`; `1`; `0`;
                  `encode_fib n`] group_mult_sub_invariant) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [group_comm_right_zero];
    DISCH_THEN
      (SUBST1_TAC o
       REWRITE_RULE
         [group_mult_right_zero; group_mult_right_one; group_neg_zero] o
       CONJUNCT1) THEN
    REWRITE_TAC
      [group_sub_refl; group_add_left_zero; GSYM decode_fib_def;
       encode_decode_fib]]);;

export_thm group_mult_sub_correct;;

(*PARAMETRIC
let group_mult_sub_correct = new_axiom
   `!x n.
      group_mult x n =
      group_mult_sub T group_zero group_zero x group_zero (encode_fib n)`;;
*)

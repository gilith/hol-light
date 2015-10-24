(* ========================================================================= *)
(* THE MAP REDUCE 3x3 BIT MATRIX EXAMPLE                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base"];;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation
  "opentheory/theories/map-reduce-bit3x3/map-reduce-bit3x3.int";;

(* ------------------------------------------------------------------------- *)
(* Proof tools for the map reduce bit matrix examples.                       *)
(* ------------------------------------------------------------------------- *)

(* Custom tactic for splitting deeply nested pairs *)

let split_pair_tac =
    let split (_,g) =
        let (v,_) = dest_forall g in
        X_GEN_TAC v THEN
        MP_TAC (ISPEC v PAIR_SURJECTIVE) THEN
        CONV_TAC (REWR_CONV LEFT_IMP_EXISTS_THM THENC
                  RAND_CONV (ABS_CONV (REWR_CONV LEFT_IMP_EXISTS_THM))) in
    W split ORELSE GEN_TAC ORELSE DISCH_THEN SUBST_VAR_TAC;;

(* Setting up the SAT solver *)

#use "Minisat/make.ml";;

let SAT_TAC =
    let sat (_,g) = ACCEPT_TAC (SAT_PROVE g) in
    REWRITE_TAC [TAUT `~(a <=> b) <=> (a <=> ~b)`] THEN
    REPEAT (CONJ_TAC ORELSE EQ_TAC) THEN
    W sat;;

(* ------------------------------------------------------------------------- *)
(* SAT proof for the map reduce 3x3 bit matrix example.                      *)
(* ------------------------------------------------------------------------- *)

export_theory "map-reduce-bit3x3-sat";;

let bit3x3_sat_goal =
`((~(a11 /\ ~(a11' /\ a11'' <=> ~(a12' /\ a21'' <=> a13' /\ a31'')) <=>
     ~(a12 /\ ~(a21' /\ a11'' <=> ~(a22' /\ a21'' <=> a23' /\ a31'')) <=>
       a13 /\ ~(a31' /\ a11'' <=> ~(a32' /\ a21'' <=> a33' /\ a31'')))) <=>
   ~(~(a11 /\ a11' <=> ~(a12 /\ a21' <=> a13 /\ a31')) /\ a11'' <=>
     ~(~(a11 /\ a12' <=> ~(a12 /\ a22' <=> a13 /\ a32')) /\ a21'' <=>
       ~(a11 /\ a13' <=> ~(a12 /\ a23' <=> a13 /\ a33')) /\ a31''))) /\
  (~(a11 /\ ~(a11' /\ a12'' <=> ~(a12' /\ a22'' <=> a13' /\ a32'')) <=>
     ~(a12 /\ ~(a21' /\ a12'' <=> ~(a22' /\ a22'' <=> a23' /\ a32'')) <=>
       a13 /\ ~(a31' /\ a12'' <=> ~(a32' /\ a22'' <=> a33' /\ a32'')))) <=>
   ~(~(a11 /\ a11' <=> ~(a12 /\ a21' <=> a13 /\ a31')) /\ a12'' <=>
     ~(~(a11 /\ a12' <=> ~(a12 /\ a22' <=> a13 /\ a32')) /\ a22'' <=>
       ~(a11 /\ a13' <=> ~(a12 /\ a23' <=> a13 /\ a33')) /\ a32''))) /\
  (~(a11 /\ ~(a11' /\ a13'' <=> ~(a12' /\ a23'' <=> a13' /\ a33'')) <=>
     ~(a12 /\ ~(a21' /\ a13'' <=> ~(a22' /\ a23'' <=> a23' /\ a33'')) <=>
       a13 /\ ~(a31' /\ a13'' <=> ~(a32' /\ a23'' <=> a33' /\ a33'')))) <=>
   ~(~(a11 /\ a11' <=> ~(a12 /\ a21' <=> a13 /\ a31')) /\ a13'' <=>
     ~(~(a11 /\ a12' <=> ~(a12 /\ a22' <=> a13 /\ a32')) /\ a23'' <=>
       ~(a11 /\ a13' <=> ~(a12 /\ a23' <=> a13 /\ a33')) /\ a33'')))) /\
 ((~(a21 /\ ~(a11' /\ a11'' <=> ~(a12' /\ a21'' <=> a13' /\ a31'')) <=>
     ~(a22 /\ ~(a21' /\ a11'' <=> ~(a22' /\ a21'' <=> a23' /\ a31'')) <=>
       a23 /\ ~(a31' /\ a11'' <=> ~(a32' /\ a21'' <=> a33' /\ a31'')))) <=>
   ~(~(a21 /\ a11' <=> ~(a22 /\ a21' <=> a23 /\ a31')) /\ a11'' <=>
     ~(~(a21 /\ a12' <=> ~(a22 /\ a22' <=> a23 /\ a32')) /\ a21'' <=>
       ~(a21 /\ a13' <=> ~(a22 /\ a23' <=> a23 /\ a33')) /\ a31''))) /\
  (~(a21 /\ ~(a11' /\ a12'' <=> ~(a12' /\ a22'' <=> a13' /\ a32'')) <=>
     ~(a22 /\ ~(a21' /\ a12'' <=> ~(a22' /\ a22'' <=> a23' /\ a32'')) <=>
       a23 /\ ~(a31' /\ a12'' <=> ~(a32' /\ a22'' <=> a33' /\ a32'')))) <=>
   ~(~(a21 /\ a11' <=> ~(a22 /\ a21' <=> a23 /\ a31')) /\ a12'' <=>
     ~(~(a21 /\ a12' <=> ~(a22 /\ a22' <=> a23 /\ a32')) /\ a22'' <=>
       ~(a21 /\ a13' <=> ~(a22 /\ a23' <=> a23 /\ a33')) /\ a32''))) /\
  (~(a21 /\ ~(a11' /\ a13'' <=> ~(a12' /\ a23'' <=> a13' /\ a33'')) <=>
     ~(a22 /\ ~(a21' /\ a13'' <=> ~(a22' /\ a23'' <=> a23' /\ a33'')) <=>
       a23 /\ ~(a31' /\ a13'' <=> ~(a32' /\ a23'' <=> a33' /\ a33'')))) <=>
   ~(~(a21 /\ a11' <=> ~(a22 /\ a21' <=> a23 /\ a31')) /\ a13'' <=>
     ~(~(a21 /\ a12' <=> ~(a22 /\ a22' <=> a23 /\ a32')) /\ a23'' <=>
       ~(a21 /\ a13' <=> ~(a22 /\ a23' <=> a23 /\ a33')) /\ a33'')))) /\
 (~(a31 /\ ~(a11' /\ a11'' <=> ~(a12' /\ a21'' <=> a13' /\ a31'')) <=>
    ~(a32 /\ ~(a21' /\ a11'' <=> ~(a22' /\ a21'' <=> a23' /\ a31'')) <=>
      a33 /\ ~(a31' /\ a11'' <=> ~(a32' /\ a21'' <=> a33' /\ a31'')))) <=>
  ~(~(a31 /\ a11' <=> ~(a32 /\ a21' <=> a33 /\ a31')) /\ a11'' <=>
    ~(~(a31 /\ a12' <=> ~(a32 /\ a22' <=> a33 /\ a32')) /\ a21'' <=>
      ~(a31 /\ a13' <=> ~(a32 /\ a23' <=> a33 /\ a33')) /\ a31''))) /\
 (~(a31 /\ ~(a11' /\ a12'' <=> ~(a12' /\ a22'' <=> a13' /\ a32'')) <=>
    ~(a32 /\ ~(a21' /\ a12'' <=> ~(a22' /\ a22'' <=> a23' /\ a32'')) <=>
      a33 /\ ~(a31' /\ a12'' <=> ~(a32' /\ a22'' <=> a33' /\ a32'')))) <=>
  ~(~(a31 /\ a11' <=> ~(a32 /\ a21' <=> a33 /\ a31')) /\ a12'' <=>
    ~(~(a31 /\ a12' <=> ~(a32 /\ a22' <=> a33 /\ a32')) /\ a22'' <=>
      ~(a31 /\ a13' <=> ~(a32 /\ a23' <=> a33 /\ a33')) /\ a32''))) /\
 (~(a31 /\ ~(a11' /\ a13'' <=> ~(a12' /\ a23'' <=> a13' /\ a33'')) <=>
    ~(a32 /\ ~(a21' /\ a13'' <=> ~(a22' /\ a23'' <=> a23' /\ a33'')) <=>
      a33 /\ ~(a31' /\ a13'' <=> ~(a32' /\ a23'' <=> a33' /\ a33'')))) <=>
  ~(~(a31 /\ a11' <=> ~(a32 /\ a21' <=> a33 /\ a31')) /\ a13'' <=>
    ~(~(a31 /\ a12' <=> ~(a32 /\ a22' <=> a33 /\ a32')) /\ a23'' <=>
      ~(a31 /\ a13' <=> ~(a32 /\ a23' <=> a33 /\ a33')) /\ a33'')))`;;

let bit3x3_sat_thm = prove (bit3x3_sat_goal, SAT_TAC);;

export_thm bit3x3_sat_thm;;

(* ------------------------------------------------------------------------- *)
(* Correctness of the map reduce 3x3 bit matrix example.                     *)
(* ------------------------------------------------------------------------- *)

export_theory "map-reduce-bit3x3-def";;

new_type_abbrev("bit3",`:bool # bool # bool`);;

new_type_abbrev("bit3x3",`:bit3 # bit3 # bit3`);;

let bit_add_def = new_definition
  `!a b. bit_add a b <=> ~(a <=> b)`;;

export_thm bit_add_def;;

let bit_mult_def = new_definition
  `!a b. bit_mult a b <=> (a /\ b)`;;

export_thm bit_mult_def;;

let bit3x3_identity_def = new_definition
  `bit3x3_identity =
     ((T,F,F),
      (F,T,F),
      (F,F,T))`;;

export_thm bit3x3_identity_def;;

let bit3_dot_def = new_definition
  `!a1 a2 a3.
   !b1 b2 b3.
      bit3_dot (a1,a2,a3) (b1,b2,b3) <=>
        bit_add (bit_mult a1 b1) (bit_add (bit_mult a2 b2) (bit_mult a3 b3))`;;

export_thm bit3_dot_def;;

let bit3x3_mult_def = new_definition
  `!a11 a12 a13
    a21 a22 a23
    a31 a32 a33.
   !b11 b12 b13
    b21 b22 b23
    b31 b32 b33.
      bit3x3_mult
        ((a11,a12,a13),
         (a21,a22,a23),
         (a31,a32,a33))
                        ((b11,b12,b13),
                         (b21,b22,b23),
                         (b31,b32,b33)) =
        ((bit3_dot (a11,a12,a13) (b11,b21,b31),
          bit3_dot (a11,a12,a13) (b12,b22,b32),
          bit3_dot (a11,a12,a13) (b13,b23,b33)),
         (bit3_dot (a21,a22,a23) (b11,b21,b31),
          bit3_dot (a21,a22,a23) (b12,b22,b32),
          bit3_dot (a21,a22,a23) (b13,b23,b33)),
         (bit3_dot (a31,a32,a33) (b11,b21,b31),
          bit3_dot (a31,a32,a33) (b12,b22,b32),
          bit3_dot (a31,a32,a33) (b13,b23,b33)))`;;

export_thm bit3x3_mult_def;;

let bit3x3_product_def = new_definition
  `bit3x3_product = foldl bit3x3_mult bit3x3_identity`;;

export_thm bit3x3_product_def;;

export_theory "map-reduce-bit3x3-thm";;

let bit3x3_cases = prove
  (`!a : bit3x3. ?a11 a12 a13
                  a21 a22 a23
                  a31 a32 a33.
      a = ((a11,a12,a13),
           (a21,a22,a23),
           (a31,a32,a33))`,
   REPEAT split_pair_tac THEN
   REWRITE_TAC
     [PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1;
      ONCE_REWRITE_RULE [EQ_SYM_EQ] EXISTS_REFL]);;

export_thm bit3x3_cases;;

let bit3x3_product_parallel = prove
  (`!l1 l2.
      bit3x3_product (APPEND l1 l2) =
      bit3x3_mult (bit3x3_product l1) (bit3x3_product l2)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bit3x3_product_def] THEN
   MATCH_MP_TAC foldl_append_assoc THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC (SPEC `s : bit3x3` bit3x3_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [bit3x3_identity_def] THEN
    REWRITE_TAC [bit3x3_mult_def; bit3_dot_def; bit_mult_def; bit_add_def];
    REPEAT GEN_TAC THEN
    MP_TAC (SPEC `s1 : bit3x3` bit3x3_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `s2 : bit3x3` bit3x3_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `x : bit3x3` bit3x3_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC
      [bit3x3_mult_def; bit3_dot_def; bit_mult_def; bit_add_def; PAIR_EQ] THEN
    ACCEPT_TAC bit3x3_sat_thm]);;

export_thm bit3x3_product_parallel;;

(* ------------------------------------------------------------------------- *)
(* Other map reduce examples.                                                *)
(* ------------------------------------------------------------------------- *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The map reduce example for natural number addition *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let natural_sum_def = new_definition
  `natural_sum = foldl (+) 0`;;

let natural_sum_parallel = prove
  (`!l1 l2.
      natural_sum (APPEND l1 l2) = natural_sum l1 + natural_sum l2`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [natural_sum_def] THEN
   MATCH_MP_TAC foldl_append_assoc THEN
   REWRITE_TAC [ADD_ASSOC; ADD_CLAUSES]);;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The map reduce example for byte addition *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let byte_sum_def = new_definition
  `byte_sum = foldl byte_add (num_to_byte 0)`;;

let byte_sum_parallel = prove
  (`!l1 l2.
      byte_sum (APPEND l1 l2) = byte_add (byte_sum l1) (byte_sum l2)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [byte_sum_def] THEN
   MATCH_MP_TAC foldl_append_assoc THEN
   REWRITE_TAC [byte_add_assoc; byte_add_right_zero]);;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* The map reduce 4x4 bit matrix example *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* SAT proof for the map reduce 4x4 bit matrix example *)

let bit4x4_sat_goal =
`((~(a11 /\
     ~(a11' /\ a11'' <=> a12' /\ a21'' <=> a13' /\ a31'' <=> a14' /\ a41'') <=>
     a12 /\
     ~(a21' /\ a11'' <=> a22' /\ a21'' <=> a23' /\ a31'' <=> a24' /\ a41'') <=>
     a13 /\
     ~(a31' /\ a11'' <=> a32' /\ a21'' <=> a33' /\ a31'' <=> a34' /\ a41'') <=>
     a14 /\
     ~(a41' /\ a11'' <=> a42' /\ a21'' <=> a43' /\ a31'' <=> a44' /\ a41'')) <=>
   ~(~(a11 /\ a11' <=> a12 /\ a21' <=> a13 /\ a31' <=> a14 /\ a41') /\ a11'' <=>
     ~(a11 /\ a12' <=> a12 /\ a22' <=> a13 /\ a32' <=> a14 /\ a42') /\ a21'' <=>
     ~(a11 /\ a13' <=> a12 /\ a23' <=> a13 /\ a33' <=> a14 /\ a43') /\ a31'' <=>
     ~(a11 /\ a14' <=> a12 /\ a24' <=> a13 /\ a34' <=> a14 /\ a44') /\ a41'')) /\
  (~(a11 /\
     ~(a11' /\ a12'' <=> a12' /\ a22'' <=> a13' /\ a32'' <=> a14' /\ a42'') <=>
     a12 /\
     ~(a21' /\ a12'' <=> a22' /\ a22'' <=> a23' /\ a32'' <=> a24' /\ a42'') <=>
     a13 /\
     ~(a31' /\ a12'' <=> a32' /\ a22'' <=> a33' /\ a32'' <=> a34' /\ a42'') <=>
     a14 /\
     ~(a41' /\ a12'' <=> a42' /\ a22'' <=> a43' /\ a32'' <=> a44' /\ a42'')) <=>
   ~(~(a11 /\ a11' <=> a12 /\ a21' <=> a13 /\ a31' <=> a14 /\ a41') /\ a12'' <=>
     ~(a11 /\ a12' <=> a12 /\ a22' <=> a13 /\ a32' <=> a14 /\ a42') /\ a22'' <=>
     ~(a11 /\ a13' <=> a12 /\ a23' <=> a13 /\ a33' <=> a14 /\ a43') /\ a32'' <=>
     ~(a11 /\ a14' <=> a12 /\ a24' <=> a13 /\ a34' <=> a14 /\ a44') /\ a42'')) /\
  (~(a11 /\
     ~(a11' /\ a13'' <=> a12' /\ a23'' <=> a13' /\ a33'' <=> a14' /\ a43'') <=>
     a12 /\
     ~(a21' /\ a13'' <=> a22' /\ a23'' <=> a23' /\ a33'' <=> a24' /\ a43'') <=>
     a13 /\
     ~(a31' /\ a13'' <=> a32' /\ a23'' <=> a33' /\ a33'' <=> a34' /\ a43'') <=>
     a14 /\
     ~(a41' /\ a13'' <=> a42' /\ a23'' <=> a43' /\ a33'' <=> a44' /\ a43'')) <=>
   ~(~(a11 /\ a11' <=> a12 /\ a21' <=> a13 /\ a31' <=> a14 /\ a41') /\ a13'' <=>
     ~(a11 /\ a12' <=> a12 /\ a22' <=> a13 /\ a32' <=> a14 /\ a42') /\ a23'' <=>
     ~(a11 /\ a13' <=> a12 /\ a23' <=> a13 /\ a33' <=> a14 /\ a43') /\ a33'' <=>
     ~(a11 /\ a14' <=> a12 /\ a24' <=> a13 /\ a34' <=> a14 /\ a44') /\ a43'')) /\
  (~(a11 /\
     ~(a11' /\ a14'' <=> a12' /\ a24'' <=> a13' /\ a34'' <=> a14' /\ a44'') <=>
     a12 /\
     ~(a21' /\ a14'' <=> a22' /\ a24'' <=> a23' /\ a34'' <=> a24' /\ a44'') <=>
     a13 /\
     ~(a31' /\ a14'' <=> a32' /\ a24'' <=> a33' /\ a34'' <=> a34' /\ a44'') <=>
     a14 /\
     ~(a41' /\ a14'' <=> a42' /\ a24'' <=> a43' /\ a34'' <=> a44' /\ a44'')) <=>
   ~(~(a11 /\ a11' <=> a12 /\ a21' <=> a13 /\ a31' <=> a14 /\ a41') /\ a14'' <=>
     ~(a11 /\ a12' <=> a12 /\ a22' <=> a13 /\ a32' <=> a14 /\ a42') /\ a24'' <=>
     ~(a11 /\ a13' <=> a12 /\ a23' <=> a13 /\ a33' <=> a14 /\ a43') /\ a34'' <=>
     ~(a11 /\ a14' <=> a12 /\ a24' <=> a13 /\ a34' <=> a14 /\ a44') /\ a44''))) /\
 ((~(a21 /\
     ~(a11' /\ a11'' <=> a12' /\ a21'' <=> a13' /\ a31'' <=> a14' /\ a41'') <=>
     a22 /\
     ~(a21' /\ a11'' <=> a22' /\ a21'' <=> a23' /\ a31'' <=> a24' /\ a41'') <=>
     a23 /\
     ~(a31' /\ a11'' <=> a32' /\ a21'' <=> a33' /\ a31'' <=> a34' /\ a41'') <=>
     a24 /\
     ~(a41' /\ a11'' <=> a42' /\ a21'' <=> a43' /\ a31'' <=> a44' /\ a41'')) <=>
   ~(~(a21 /\ a11' <=> a22 /\ a21' <=> a23 /\ a31' <=> a24 /\ a41') /\ a11'' <=>
     ~(a21 /\ a12' <=> a22 /\ a22' <=> a23 /\ a32' <=> a24 /\ a42') /\ a21'' <=>
     ~(a21 /\ a13' <=> a22 /\ a23' <=> a23 /\ a33' <=> a24 /\ a43') /\ a31'' <=>
     ~(a21 /\ a14' <=> a22 /\ a24' <=> a23 /\ a34' <=> a24 /\ a44') /\ a41'')) /\
  (~(a21 /\
     ~(a11' /\ a12'' <=> a12' /\ a22'' <=> a13' /\ a32'' <=> a14' /\ a42'') <=>
     a22 /\
     ~(a21' /\ a12'' <=> a22' /\ a22'' <=> a23' /\ a32'' <=> a24' /\ a42'') <=>
     a23 /\
     ~(a31' /\ a12'' <=> a32' /\ a22'' <=> a33' /\ a32'' <=> a34' /\ a42'') <=>
     a24 /\
     ~(a41' /\ a12'' <=> a42' /\ a22'' <=> a43' /\ a32'' <=> a44' /\ a42'')) <=>
   ~(~(a21 /\ a11' <=> a22 /\ a21' <=> a23 /\ a31' <=> a24 /\ a41') /\ a12'' <=>
     ~(a21 /\ a12' <=> a22 /\ a22' <=> a23 /\ a32' <=> a24 /\ a42') /\ a22'' <=>
     ~(a21 /\ a13' <=> a22 /\ a23' <=> a23 /\ a33' <=> a24 /\ a43') /\ a32'' <=>
     ~(a21 /\ a14' <=> a22 /\ a24' <=> a23 /\ a34' <=> a24 /\ a44') /\ a42'')) /\
  (~(a21 /\
     ~(a11' /\ a13'' <=> a12' /\ a23'' <=> a13' /\ a33'' <=> a14' /\ a43'') <=>
     a22 /\
     ~(a21' /\ a13'' <=> a22' /\ a23'' <=> a23' /\ a33'' <=> a24' /\ a43'') <=>
     a23 /\
     ~(a31' /\ a13'' <=> a32' /\ a23'' <=> a33' /\ a33'' <=> a34' /\ a43'') <=>
     a24 /\
     ~(a41' /\ a13'' <=> a42' /\ a23'' <=> a43' /\ a33'' <=> a44' /\ a43'')) <=>
   ~(~(a21 /\ a11' <=> a22 /\ a21' <=> a23 /\ a31' <=> a24 /\ a41') /\ a13'' <=>
     ~(a21 /\ a12' <=> a22 /\ a22' <=> a23 /\ a32' <=> a24 /\ a42') /\ a23'' <=>
     ~(a21 /\ a13' <=> a22 /\ a23' <=> a23 /\ a33' <=> a24 /\ a43') /\ a33'' <=>
     ~(a21 /\ a14' <=> a22 /\ a24' <=> a23 /\ a34' <=> a24 /\ a44') /\ a43'')) /\
  (~(a21 /\
     ~(a11' /\ a14'' <=> a12' /\ a24'' <=> a13' /\ a34'' <=> a14' /\ a44'') <=>
     a22 /\
     ~(a21' /\ a14'' <=> a22' /\ a24'' <=> a23' /\ a34'' <=> a24' /\ a44'') <=>
     a23 /\
     ~(a31' /\ a14'' <=> a32' /\ a24'' <=> a33' /\ a34'' <=> a34' /\ a44'') <=>
     a24 /\
     ~(a41' /\ a14'' <=> a42' /\ a24'' <=> a43' /\ a34'' <=> a44' /\ a44'')) <=>
   ~(~(a21 /\ a11' <=> a22 /\ a21' <=> a23 /\ a31' <=> a24 /\ a41') /\ a14'' <=>
     ~(a21 /\ a12' <=> a22 /\ a22' <=> a23 /\ a32' <=> a24 /\ a42') /\ a24'' <=>
     ~(a21 /\ a13' <=> a22 /\ a23' <=> a23 /\ a33' <=> a24 /\ a43') /\ a34'' <=>
     ~(a21 /\ a14' <=> a22 /\ a24' <=> a23 /\ a34' <=> a24 /\ a44') /\ a44''))) /\
 ((~(a31 /\
     ~(a11' /\ a11'' <=> a12' /\ a21'' <=> a13' /\ a31'' <=> a14' /\ a41'') <=>
     a32 /\
     ~(a21' /\ a11'' <=> a22' /\ a21'' <=> a23' /\ a31'' <=> a24' /\ a41'') <=>
     a33 /\
     ~(a31' /\ a11'' <=> a32' /\ a21'' <=> a33' /\ a31'' <=> a34' /\ a41'') <=>
     a34 /\
     ~(a41' /\ a11'' <=> a42' /\ a21'' <=> a43' /\ a31'' <=> a44' /\ a41'')) <=>
   ~(~(a31 /\ a11' <=> a32 /\ a21' <=> a33 /\ a31' <=> a34 /\ a41') /\ a11'' <=>
     ~(a31 /\ a12' <=> a32 /\ a22' <=> a33 /\ a32' <=> a34 /\ a42') /\ a21'' <=>
     ~(a31 /\ a13' <=> a32 /\ a23' <=> a33 /\ a33' <=> a34 /\ a43') /\ a31'' <=>
     ~(a31 /\ a14' <=> a32 /\ a24' <=> a33 /\ a34' <=> a34 /\ a44') /\ a41'')) /\
  (~(a31 /\
     ~(a11' /\ a12'' <=> a12' /\ a22'' <=> a13' /\ a32'' <=> a14' /\ a42'') <=>
     a32 /\
     ~(a21' /\ a12'' <=> a22' /\ a22'' <=> a23' /\ a32'' <=> a24' /\ a42'') <=>
     a33 /\
     ~(a31' /\ a12'' <=> a32' /\ a22'' <=> a33' /\ a32'' <=> a34' /\ a42'') <=>
     a34 /\
     ~(a41' /\ a12'' <=> a42' /\ a22'' <=> a43' /\ a32'' <=> a44' /\ a42'')) <=>
   ~(~(a31 /\ a11' <=> a32 /\ a21' <=> a33 /\ a31' <=> a34 /\ a41') /\ a12'' <=>
     ~(a31 /\ a12' <=> a32 /\ a22' <=> a33 /\ a32' <=> a34 /\ a42') /\ a22'' <=>
     ~(a31 /\ a13' <=> a32 /\ a23' <=> a33 /\ a33' <=> a34 /\ a43') /\ a32'' <=>
     ~(a31 /\ a14' <=> a32 /\ a24' <=> a33 /\ a34' <=> a34 /\ a44') /\ a42'')) /\
  (~(a31 /\
     ~(a11' /\ a13'' <=> a12' /\ a23'' <=> a13' /\ a33'' <=> a14' /\ a43'') <=>
     a32 /\
     ~(a21' /\ a13'' <=> a22' /\ a23'' <=> a23' /\ a33'' <=> a24' /\ a43'') <=>
     a33 /\
     ~(a31' /\ a13'' <=> a32' /\ a23'' <=> a33' /\ a33'' <=> a34' /\ a43'') <=>
     a34 /\
     ~(a41' /\ a13'' <=> a42' /\ a23'' <=> a43' /\ a33'' <=> a44' /\ a43'')) <=>
   ~(~(a31 /\ a11' <=> a32 /\ a21' <=> a33 /\ a31' <=> a34 /\ a41') /\ a13'' <=>
     ~(a31 /\ a12' <=> a32 /\ a22' <=> a33 /\ a32' <=> a34 /\ a42') /\ a23'' <=>
     ~(a31 /\ a13' <=> a32 /\ a23' <=> a33 /\ a33' <=> a34 /\ a43') /\ a33'' <=>
     ~(a31 /\ a14' <=> a32 /\ a24' <=> a33 /\ a34' <=> a34 /\ a44') /\ a43'')) /\
  (~(a31 /\
     ~(a11' /\ a14'' <=> a12' /\ a24'' <=> a13' /\ a34'' <=> a14' /\ a44'') <=>
     a32 /\
     ~(a21' /\ a14'' <=> a22' /\ a24'' <=> a23' /\ a34'' <=> a24' /\ a44'') <=>
     a33 /\
     ~(a31' /\ a14'' <=> a32' /\ a24'' <=> a33' /\ a34'' <=> a34' /\ a44'') <=>
     a34 /\
     ~(a41' /\ a14'' <=> a42' /\ a24'' <=> a43' /\ a34'' <=> a44' /\ a44'')) <=>
   ~(~(a31 /\ a11' <=> a32 /\ a21' <=> a33 /\ a31' <=> a34 /\ a41') /\ a14'' <=>
     ~(a31 /\ a12' <=> a32 /\ a22' <=> a33 /\ a32' <=> a34 /\ a42') /\ a24'' <=>
     ~(a31 /\ a13' <=> a32 /\ a23' <=> a33 /\ a33' <=> a34 /\ a43') /\ a34'' <=>
     ~(a31 /\ a14' <=> a32 /\ a24' <=> a33 /\ a34' <=> a34 /\ a44') /\ a44''))) /\
 (~(a41 /\
    ~(a11' /\ a11'' <=> a12' /\ a21'' <=> a13' /\ a31'' <=> a14' /\ a41'') <=>
    a42 /\
    ~(a21' /\ a11'' <=> a22' /\ a21'' <=> a23' /\ a31'' <=> a24' /\ a41'') <=>
    a43 /\
    ~(a31' /\ a11'' <=> a32' /\ a21'' <=> a33' /\ a31'' <=> a34' /\ a41'') <=>
    a44 /\
    ~(a41' /\ a11'' <=> a42' /\ a21'' <=> a43' /\ a31'' <=> a44' /\ a41'')) <=>
  ~(~(a41 /\ a11' <=> a42 /\ a21' <=> a43 /\ a31' <=> a44 /\ a41') /\ a11'' <=>
    ~(a41 /\ a12' <=> a42 /\ a22' <=> a43 /\ a32' <=> a44 /\ a42') /\ a21'' <=>
    ~(a41 /\ a13' <=> a42 /\ a23' <=> a43 /\ a33' <=> a44 /\ a43') /\ a31'' <=>
    ~(a41 /\ a14' <=> a42 /\ a24' <=> a43 /\ a34' <=> a44 /\ a44') /\ a41'')) /\
 (~(a41 /\
    ~(a11' /\ a12'' <=> a12' /\ a22'' <=> a13' /\ a32'' <=> a14' /\ a42'') <=>
    a42 /\
    ~(a21' /\ a12'' <=> a22' /\ a22'' <=> a23' /\ a32'' <=> a24' /\ a42'') <=>
    a43 /\
    ~(a31' /\ a12'' <=> a32' /\ a22'' <=> a33' /\ a32'' <=> a34' /\ a42'') <=>
    a44 /\
    ~(a41' /\ a12'' <=> a42' /\ a22'' <=> a43' /\ a32'' <=> a44' /\ a42'')) <=>
  ~(~(a41 /\ a11' <=> a42 /\ a21' <=> a43 /\ a31' <=> a44 /\ a41') /\ a12'' <=>
    ~(a41 /\ a12' <=> a42 /\ a22' <=> a43 /\ a32' <=> a44 /\ a42') /\ a22'' <=>
    ~(a41 /\ a13' <=> a42 /\ a23' <=> a43 /\ a33' <=> a44 /\ a43') /\ a32'' <=>
    ~(a41 /\ a14' <=> a42 /\ a24' <=> a43 /\ a34' <=> a44 /\ a44') /\ a42'')) /\
 (~(a41 /\
    ~(a11' /\ a13'' <=> a12' /\ a23'' <=> a13' /\ a33'' <=> a14' /\ a43'') <=>
    a42 /\
    ~(a21' /\ a13'' <=> a22' /\ a23'' <=> a23' /\ a33'' <=> a24' /\ a43'') <=>
    a43 /\
    ~(a31' /\ a13'' <=> a32' /\ a23'' <=> a33' /\ a33'' <=> a34' /\ a43'') <=>
    a44 /\
    ~(a41' /\ a13'' <=> a42' /\ a23'' <=> a43' /\ a33'' <=> a44' /\ a43'')) <=>
  ~(~(a41 /\ a11' <=> a42 /\ a21' <=> a43 /\ a31' <=> a44 /\ a41') /\ a13'' <=>
    ~(a41 /\ a12' <=> a42 /\ a22' <=> a43 /\ a32' <=> a44 /\ a42') /\ a23'' <=>
    ~(a41 /\ a13' <=> a42 /\ a23' <=> a43 /\ a33' <=> a44 /\ a43') /\ a33'' <=>
    ~(a41 /\ a14' <=> a42 /\ a24' <=> a43 /\ a34' <=> a44 /\ a44') /\ a43'')) /\
 (~(a41 /\
    ~(a11' /\ a14'' <=> a12' /\ a24'' <=> a13' /\ a34'' <=> a14' /\ a44'') <=>
    a42 /\
    ~(a21' /\ a14'' <=> a22' /\ a24'' <=> a23' /\ a34'' <=> a24' /\ a44'') <=>
    a43 /\
    ~(a31' /\ a14'' <=> a32' /\ a24'' <=> a33' /\ a34'' <=> a34' /\ a44'') <=>
    a44 /\
    ~(a41' /\ a14'' <=> a42' /\ a24'' <=> a43' /\ a34'' <=> a44' /\ a44'')) <=>
  ~(~(a41 /\ a11' <=> a42 /\ a21' <=> a43 /\ a31' <=> a44 /\ a41') /\ a14'' <=>
    ~(a41 /\ a12' <=> a42 /\ a22' <=> a43 /\ a32' <=> a44 /\ a42') /\ a24'' <=>
    ~(a41 /\ a13' <=> a42 /\ a23' <=> a43 /\ a33' <=> a44 /\ a43') /\ a34'' <=>
    ~(a41 /\ a14' <=> a42 /\ a24' <=> a43 /\ a34' <=> a44 /\ a44') /\ a44''))`;;

(* Too large for MiniSat-p v1.14 on telperion
let bit4x4_sat_thm = prove (bit4x4_sat_goal, SAT_TAC);;
*)

(* Correctness of the map reduce 4x4 bit matrix example *)

new_type_abbrev("bit4",`:bool # bool # bool # bool`);;

new_type_abbrev("bit4x4",`:bit4 # bit4 # bit4 # bit4`);;

let bit4x4_identity_def = new_definition
  `bit4x4_identity =
     ((T,F,F,F),
      (F,T,F,F),
      (F,F,T,F),
      (F,F,F,T))`;;

let bit4_dot_def = new_definition
  `!a1 a2 a3 a4.
   !b1 b2 b3 b4.
      bit4_dot (a1,a2,a3,a4) (b1,b2,b3,b4) <=>
        ~((a1 /\ b1) <=> (a2 /\ b2) <=> (a3 /\ b3) <=> (a4 /\ b4))`;;

let bit4x4_mult_def = new_definition
  `!a11 a12 a13 a14
    a21 a22 a23 a24
    a31 a32 a33 a34
    a41 a42 a43 a44.
   !b11 b12 b13 b14
    b21 b22 b23 b24
    b31 b32 b33 b34
    b41 b42 b43 b44.
      bit4x4_mult
        ((a11,a12,a13,a14),
         (a21,a22,a23,a24),
         (a31,a32,a33,a34),
         (a41,a42,a43,a44))
                            ((b11,b12,b13,b14),
                             (b21,b22,b23,b24),
                             (b31,b32,b33,b34),
                             (b41,b42,b43,b44)) =
        ((bit4_dot (a11,a12,a13,a14) (b11,b21,b31,b41),
          bit4_dot (a11,a12,a13,a14) (b12,b22,b32,b42),
          bit4_dot (a11,a12,a13,a14) (b13,b23,b33,b43),
          bit4_dot (a11,a12,a13,a14) (b14,b24,b34,b44)),
         (bit4_dot (a21,a22,a23,a24) (b11,b21,b31,b41),
          bit4_dot (a21,a22,a23,a24) (b12,b22,b32,b42),
          bit4_dot (a21,a22,a23,a24) (b13,b23,b33,b43),
          bit4_dot (a21,a22,a23,a24) (b14,b24,b34,b44)),
         (bit4_dot (a31,a32,a33,a34) (b11,b21,b31,b41),
          bit4_dot (a31,a32,a33,a34) (b12,b22,b32,b42),
          bit4_dot (a31,a32,a33,a34) (b13,b23,b33,b43),
          bit4_dot (a31,a32,a33,a34) (b14,b24,b34,b44)),
         (bit4_dot (a41,a42,a43,a44) (b11,b21,b31,b41),
          bit4_dot (a41,a42,a43,a44) (b12,b22,b32,b42),
          bit4_dot (a41,a42,a43,a44) (b13,b23,b33,b43),
          bit4_dot (a41,a42,a43,a44) (b14,b24,b34,b44)))`;;

let bit4x4_product_def = new_definition
  `bit4x4_product = foldl bit4x4_mult bit4x4_identity`;;

let bit4x4_cases = prove
  (`!a : bit4x4. ?a11 a12 a13 a14
                  a21 a22 a23 a24
                  a31 a32 a33 a34
                  a41 a42 a43 a44.
      a = ((a11,a12,a13,a14),
           (a21,a22,a23,a24),
           (a31,a32,a33,a34),
           (a41,a42,a43,a44))`,
   REPEAT split_pair_tac THEN
   REWRITE_TAC
     [PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE [CONJ_SYM] UNWIND_THM1;
      ONCE_REWRITE_RULE [EQ_SYM_EQ] EXISTS_REFL]);;

(* Requires the large SAT proof above
let bit4x4_product_parallel = prove
  (`!l1 l2.
      bit4x4_product (APPEND l1 l2) =
      bit4x4_mult (bit4x4_product l1) (bit4x4_product l2)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bit4x4_product_def] THEN
   MATCH_MP_TAC foldl_append_assoc THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    MP_TAC (SPEC `s : bit4x4` bit4x4_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [bit4x4_identity_def] THEN
    REWRITE_TAC [bit4x4_mult_def; bit4_dot_def];
    REPEAT GEN_TAC THEN
    MP_TAC (SPEC `s1 : bit4x4` bit4x4_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `s2 : bit4x4` bit4x4_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `x : bit4x4` bit4x4_cases) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [bit4x4_mult_def; bit4_dot_def; PAIR_EQ] THEN
    ACCEPT_TAC bit4x4_sat_thm]);;
*)

(* ------------------------------------------------------------------------- *)
(* HOL Light bindings for the map reduce 3x3 bit matrix example.             *)
(* ------------------------------------------------------------------------- *)

export_theory "map-reduce-bit3x3-hol-light-thm";;

export_theory_thm_names "map-reduce-bit3x3"
  ["map-reduce-bit3x3-def";
   "map-reduce-bit3x3-thm"];;

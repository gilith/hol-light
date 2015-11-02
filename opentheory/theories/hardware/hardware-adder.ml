(* ========================================================================= *)
(* HARDWARE ADDER DEVICES                                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware adder devices.                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-adder-def";;

(* ~~~~~~~~~~~~~~~~~~ *)
(* Wire adder devices *)
(* ~~~~~~~~~~~~~~~~~~ *)

let adder2_def = new_definition
  `!x y s c.
     adder2 x y s c <=>
     xor2 x y s /\
     and2 x y c`;;

export_thm adder2_def;;

let adder3_def = new_definition
  `!x y z s c.
     adder3 x y z s c <=>
     xor3 x y z s /\
     majority3 x y z c`;;

export_thm adder3_def;;

(* ~~~~~~~~~~~~~~~~~ *)
(* Bus adder devices *)
(* ~~~~~~~~~~~~~~~~~ *)

let badder2_def = new_definition
  `!x y s c.
     badder2 x y s c <=>
     bxor2 x y s /\
     band2 x y c`;;

export_thm badder2_def;;

let badder3_def = new_definition
  `!x y z s c.
     badder3 x y z s c <=>
     bxor3 x y z s /\
     bmajority3 x y z c`;;

export_thm badder3_def;;

(*       n+1  n  n-1 n-2  ...  2   1   0  *)
(*  w =   -   X   X   X   ...  X   X   X  *)
(*  x =   -   X   X   X   ...  X   X   X  *)
(*  y =   -   X   X   X   ...  X   X   X  *)
(*  z =   -   X   X   X   ...  X   X   X  *)
(*  p =   -   X   X   X   ...  X   X   X  *)
(*  q =   X   X   X   X   ...  X   X   -  *)
(*  s =   X   X   X   X   ...  X   X   X  *)
(*  c =   X   X   X   X   ...  X   X   -  *)

let badder4_def = new_definition
  `!w x y z s c.
     badder4 w x y z s c <=>
     ?n p q z0 z1 s0 s1 s2 c0 c1 p0 p1 q1 q2.
       width w = n + 1 /\
       width x = n + 1 /\
       width y = n + 1 /\
       width z = n + 1 /\
       width s = n + 2 /\
       width c = n + 1 /\
       width p = n + 1 /\
       width q = n + 1
       /\
       wire z 0 z0 /\
       bsub z 1 n z1 /\
       wire s 0 s0 /\
       bsub s 1 n s1 /\
       wire s (n + 1) s2 /\
       wire c 0 c0 /\
       bsub c 1 n c1 /\
       wire p 0 p0 /\
       bsub p 1 n p1 /\
       bsub q 0 n q1 /\
       wire q n q2
       /\
       badder3 w x y p q /\
       adder2 p0 z0 s0 c0 /\
       badder3 p1 q1 z1 s1 c1 /\
       connect q2 s2`;;

export_thm badder4_def;;

let scshiftr_def = new_definition
  `!ld xs xc xb.
     scshiftr ld xs xc xb <=>
     ?r sp sq sr cp cq cr xs0 xs1 sq0 sq1 sq2 sq3 cp0 cp1 cq0 cq1.
       width xs = r + 1 /\
       width xc = r + 1 /\
       width sp = r /\
       width sq = r + 1 /\
       width sr = r /\
       width cp = r + 1 /\
       width cq = r + 1 /\
       width cr = r + 1
       /\
       wire xs 0 xs0 /\
       bsub xs 1 r xs1 /\
       wire sq 0 sq0 /\
       bsub sq 0 r sq1 /\
       bsub sq 1 r sq2 /\
       wire sq r sq3 /\
       bsub cp 0 r cp0 /\
       wire cp r cp1 /\
       bsub cq 0 r cq0 /\
       wire cq r cq1
       /\
       badder2 sp cp0 sq1 cq0 /\
       connect cp1 sq3 /\
       connect ground cq1 /\
       case1 ld xs0 sq0 xb /\
       bcase1 ld xs1 sq2 sr /\
       bcase1 ld xc cq cr
       /\
       bdelay sr sp /\
       bdelay cr cp`;;

export_thm scshiftr_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware adder devices.                                     *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-adder-thm";;

(* ~~~~~~~~~~~~~~~~~~ *)
(* Wire adder devices *)
(* ~~~~~~~~~~~~~~~~~~ *)

let adder2_exists = prove
 (`!x y. ?s c. adder2 x y s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def] THEN
  X_CHOOSE_THEN `s : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`] xor2_exists) THEN
  X_CHOOSE_THEN `c : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`] and2_exists) THEN
  EXISTS_TAC `s : wire` THEN
  EXISTS_TAC `c : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm adder2_exists;;

let adder3_exists = prove
 (`!x y z. ?s c. adder3 x y z s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def] THEN
  X_CHOOSE_THEN `s : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`; `z : wire`] xor3_exists) THEN
  X_CHOOSE_THEN `c : wire` STRIP_ASSUME_TAC
    (SPECL [`x : wire`; `y : wire`; `z : wire`] majority3_exists) THEN
  EXISTS_TAC `s : wire` THEN
  EXISTS_TAC `c : wire` THEN
  ASM_REWRITE_TAC []);;

export_thm adder3_exists;;

let adder3_right_ground = prove
 (`!x y s c. adder2 x y s c ==> adder3 x y ground s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def; adder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC xor3_right_ground THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC majority3_right_ground THEN
   ASM_REWRITE_TAC []]);;

export_thm adder3_right_ground;;

let adder3_bit_to_num = prove
 (`!x y z s c t.
     adder3 x y z s c ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) +
     bit_to_num (signal z t) =
     bit_to_num (signal s t) + 2 * bit_to_num (signal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `s : wire`; `t : cycle`]
       xor3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `c : wire`; `t : cycle`]
       majority3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x t` THEN
  BOOL_CASES_TAC `signal y t` THEN
  BOOL_CASES_TAC `signal z t` THEN
  REWRITE_TAC [bit_to_num_def; MULT_1; ADD_0; ZERO_ADD; MULT_0] THEN
  REWRITE_TAC [TWO; ONE; ADD_SUC; ADD_0]);;

export_thm adder3_bit_to_num;;

let adder2_bit_to_num = prove
 (`!x y s c t.
     adder2 x y s c ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) =
     bit_to_num (signal s t) + 2 * bit_to_num (signal c t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `s : wire`; `c : wire`]
            adder3_right_ground) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `y : wire`; `ground`;
            `s : wire`; `c : wire`; `t : cycle`]
       adder3_bit_to_num) THEN
  ASM_REWRITE_TAC [bit_to_num_ground; ADD_0]);;

export_thm adder2_bit_to_num;;

(* ~~~~~~~~~~~~~~~~~ *)
(* Bus adder devices *)
(* ~~~~~~~~~~~~~~~~~ *)

let badder2_width = prove
 (`!x y s c.
     badder2 x y s c ==>
     ?n.
       width x = n /\
       width y = n /\
       width s = n /\
       width c = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `s : bus`] bxor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `c : bus`] band2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_width;;

let badder2_width_out1 = prove
 (`!x y s c n.
     badder2 x y s c /\ width x = n ==>
     width s = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
      [`x : bus`; `y : bus`; `s : bus`; `c : bus`] badder2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_width_out1;;

let badder2_width_out2 = prove
 (`!x y s c n.
     badder2 x y s c /\ width x = n ==>
     width c = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
      [`x : bus`; `y : bus`; `s : bus`; `c : bus`] badder2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_width_out2;;

let badder2_bnil = prove
 (`badder2 bnil bnil bnil bnil`,
  REWRITE_TAC [badder2_def; bxor2_bnil; band2_bnil]);;

export_thm badder2_bnil;;

let badder2_bwire = prove
 (`!x y s c.
     badder2 (bwire x) (bwire y) (bwire s) (bwire c) <=>
     adder2 x y s c`,
  REWRITE_TAC [badder2_def; adder2_def; bxor2_bwire; band2_bwire]);;

export_thm badder2_bwire;;

let badder2_bappend = prove
 (`!x1 x2 y1 y2 s1 s2 c1 c2.
     badder2 x1 y1 s1 c1 /\ badder2 x2 y2 s2 c2 ==>
     badder2 (bappend x1 x2) (bappend y1 y2) (bappend s1 s2) (bappend c1 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_bappend THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_bappend THEN
   ASM_REWRITE_TAC []]);;

export_thm badder2_bappend;;

let badder2_bsub = prove
 (`!x y s c k n xs ys ss cs.
     badder2 x y s c /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub s k n ss /\
     bsub c k n cs ==>
     badder2 xs ys ss cs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_bsub THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `s : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `c : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm badder2_bsub;;

let badder2_wire = prove
 (`!x y s c i xi yi si ci.
     badder2 x y s c /\
     wire x i xi /\ wire y i yi /\ wire s i si /\ wire c i ci ==>
     adder2 xi yi si ci`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM badder2_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC badder2_bsub THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `s : bus` THEN
  EXISTS_TAC `c : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_wire;;

let badder2_bappend_bwire = prove
 (`!xh xt yh yt sh st ch ct.
     badder2
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire sh) st)
       (bappend (bwire ch) ct) <=>
     adder2 xh yh sh ch /\ badder2 xt yt st ct`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM badder2_bwire] THEN
   MATCH_ACCEPT_TAC badder2_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC badder2_wire THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire sh) st` THEN
   EXISTS_TAC `bappend (bwire ch) ct` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire sh) st`;
        `bappend (bwire ch) ct`]
       badder2_width) THEN
  ASM_REWRITE_TAC [bappend_width; bwire_width; ONE; SUC_ADD; ZERO_ADD] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` MP_TAC) THEN
  MP_TAC (SPEC `m : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST1_TAC
       (X_CHOOSE_THEN `n : num` SUBST1_TAC)) THENL
  [REWRITE_TAC [NOT_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [SUC_INJ] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC badder2_bsub THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire sh) st` THEN
  EXISTS_TAC `bappend (bwire ch) ct` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire ch) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire sh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire yh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm badder2_bappend_bwire;;

let badder2_exists = prove
 (`!x y. width x = width y ==> ?s c. badder2 x y s c`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`] bxor2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `s : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`] band2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `c : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s : bus` THEN
  EXISTS_TAC `c : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_exists;;

let badder3_width = prove
 (`!x y z s c.
     badder3 x y z s c ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       width s = n /\
       width c = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `y : bus`; `z : bus`; `s : bus`]
       bxor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `y : bus`; `z : bus`; `c : bus`]
       bmajority3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_width;;

let badder3_width_out1 = prove
 (`!x y z s c n.
     badder3 x y z s c /\ width x = n ==>
     width s = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
      [`x : bus`; `y : bus`; `z : bus`; `s : bus`; `c : bus`]
      badder3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_width_out1;;

let badder3_width_out2 = prove
 (`!x y z s c n.
     badder3 x y z s c /\ width x = n ==>
     width c = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
      [`x : bus`; `y : bus`; `z : bus`; `s : bus`; `c : bus`]
      badder3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_width_out2;;

let badder3_bnil = prove
 (`badder3 bnil bnil bnil bnil bnil`,
  REWRITE_TAC [badder3_def; bxor3_bnil; bmajority3_bnil]);;

export_thm badder3_bnil;;

let badder3_bwire = prove
 (`!x y z s c.
     badder3 (bwire x) (bwire y) (bwire z) (bwire s) (bwire c) <=>
     adder3 x y z s c`,
  REWRITE_TAC [badder3_def; adder3_def; bxor3_bwire; bmajority3_bwire]);;

export_thm badder3_bwire;;

let badder3_bappend = prove
 (`!x1 x2 y1 y2 z1 z2 s1 s2 c1 c2.
     badder3 x1 y1 z1 s1 c1 /\ badder3 x2 y2 z2 s2 c2 ==>
     badder3
       (bappend x1 x2)
       (bappend y1 y2)
       (bappend z1 z2)
       (bappend s1 s2)
       (bappend c1 c2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor3_bappend THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bmajority3_bappend THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_bappend;;

let badder3_bsub = prove
 (`!x y z s c k n xs ys zs ss cs.
     badder3 x y z s c /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs /\
     bsub s k n ss /\
     bsub c k n cs ==>
     badder3 xs ys zs ss cs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor3_bsub THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `s : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bmajority3_bsub THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `c : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_bsub;;

let badder3_wire = prove
 (`!x y z s c i xi yi zi si ci.
     badder3 x y z s c /\
     wire x i xi /\ wire y i yi /\ wire z i zi /\
     wire s i si /\ wire c i ci ==>
     adder3 xi yi zi si ci`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM badder3_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC badder3_bsub THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `s : bus` THEN
  EXISTS_TAC `c : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_wire;;

let badder3_bappend_bwire = prove
 (`!xh xt yh yt zh zt sh st ch ct.
     badder3
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt)
       (bappend (bwire sh) st)
       (bappend (bwire ch) ct) <=>
     adder3 xh yh zh sh ch /\ badder3 xt yt zt st ct`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM badder3_bwire] THEN
   MATCH_ACCEPT_TAC badder3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC badder3_wire THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `bappend (bwire sh) st` THEN
   EXISTS_TAC `bappend (bwire ch) ct` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`;
        `bappend (bwire sh) st`;
        `bappend (bwire ch) ct`]
       badder3_width) THEN
  ASM_REWRITE_TAC [bappend_width; bwire_width; ONE; SUC_ADD; ZERO_ADD] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` MP_TAC) THEN
  MP_TAC (SPEC `m : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST1_TAC
       (X_CHOOSE_THEN `n : num` SUBST1_TAC)) THENL
  [REWRITE_TAC [NOT_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [SUC_INJ] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC badder3_bsub THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `bappend (bwire sh) st` THEN
  EXISTS_TAC `bappend (bwire ch) ct` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire ch) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire sh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire zh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire yh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm badder3_bappend_bwire;;

let badder3_exists = prove
 (`!x y z. width x = width y /\ width x = width z ==> ?s c. badder3 x y z s c`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `z : bus`] bxor3_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `s : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `z : bus`] bmajority3_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `c : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s : bus` THEN
  EXISTS_TAC `c : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_exists;;

let badder3_right_bground = prove
 (`!x y n s c.
     width x = n /\ badder2 x y s c ==>
     badder3 x y (bground n) s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def; badder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor3_right_bground THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bmajority3_right_bground THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_right_bground;;

let badder3_bits_to_num = prove
 (`!x y z s c t.
     badder3 x y z s c ==>
     bits_to_num (bsignal x t) +
     bits_to_num (bsignal y t) +
     bits_to_num (bsignal z t) =
     bits_to_num (bsignal s t) +
     2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`x : bus`; `y : bus`; `z : bus`; `s : bus`; `c : bus`]
      badder3_width) THEN
  ASM_REWRITE_TAC [GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [IMP_IMP] THEN
  SPEC_TAC (`c : bus`, `c : bus`) THEN
  SPEC_TAC (`s : bus`, `s : bus`) THEN
  SPEC_TAC (`z : bus`, `z : bus`) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [bnil_bsignal; bits_to_num_nil; ADD_0; MULT_0];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; GSYM IMP_IMP] THEN
  STRIP_TAC THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zh : wire`
      (X_CHOOSE_THEN `zt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `sh : wire`
      (X_CHOOSE_THEN `st : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch : wire`
      (X_CHOOSE_THEN `ct : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  FIRST_X_ASSUM
    (STRIP_ASSUME_TAC o
     CONV_RULE (REWR_CONV badder3_bappend_bwire)) THEN
  REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
     ((2 * bits_to_num (bsignal xt t)) +
      (2 * bits_to_num (bsignal yt t)) +
      (2 * bits_to_num (bsignal zt t)))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM)))) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal sh t) +
      2 * bit_to_num (signal ch t)) +
     ((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t))))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
     ((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t))))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_LCANCEL; GSYM LEFT_ADD_DISTRIB] THEN
   AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   MATCH_MP_TAC adder3_bit_to_num THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_bits_to_num;;

let badder2_bits_to_num = prove
 (`!x y s c t.
     badder2 x y s c ==>
     bits_to_num (bsignal x t) +
     bits_to_num (bsignal y t) =
     bits_to_num (bsignal s t) +
     2 * bits_to_num (bsignal c t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `width x`; `s : bus`; `c : bus`]
                badder3_right_bground) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `y : bus`; `bground (width x)`; `s : bus`; `c : bus`]
       badder3_bits_to_num) THEN
  ASM_REWRITE_TAC [bground_bits_to_num; ADD_0] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm badder2_bits_to_num;;

let badder4_width = prove
 (`!w x y z s c.
     badder4 w x y z s c ==>
     ?n.
       width w = n + 1 /\
       width x = n + 1 /\
       width y = n + 1 /\
       width z = n + 1 /\
       width s = n + 2 /\
       width c = n + 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder4_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC []);;

export_thm badder4_width;;

let badder4_width_out1 = prove
 (`!w x y z s c n.
     badder4 w x y z s c /\ width w = n + 1 ==>
     width s = n + 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`w : bus`; `x : bus`; `y : bus`; `z : bus`; `s : bus`; `c : bus`]
      badder4_width) THEN
  ASM_REWRITE_TAC [EQ_ADD_RCANCEL] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
  ASM_REWRITE_TAC []);;

export_thm badder4_width_out1;;

let badder4_width_out2 = prove
 (`!w x y z s c n.
     badder4 w x y z s c /\ width w = n + 1 ==>
     width c = n + 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`w : bus`; `x : bus`; `y : bus`; `z : bus`; `s : bus`; `c : bus`]
      badder4_width) THEN
  ASM_REWRITE_TAC [EQ_ADD_RCANCEL] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
  ASM_REWRITE_TAC []);;

export_thm badder4_width_out2;;

let badder4_exists = prove
 (`!w x y z.
     ~(width w = 0) /\
     width w = width x /\
     width w = width y /\
     width w = width z ==>
     ?s c. badder4 w x y z s c`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [badder4_def] THEN
  MP_TAC (SPEC `width w` num_CASES) THEN
  ASM_REWRITE_TAC [ADD1] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?z0. wire z 0 z0` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
   ALL_TAC] THEN
  SUBGOAL_THEN `?z1. bsub z 1 n z1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `width z1 = n` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `y : bus`] badder3_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `p : bus`
      (X_CHOOSE_THEN `q : bus` STRIP_ASSUME_TAC)) THEN
  MP_TAC
   (SPECL [`w : bus`; `x : bus`; `y : bus`; `p : bus`; `q : bus`; `width w`]
      badder3_width_out1) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
   (SPECL [`w : bus`; `x : bus`; `y : bus`; `p : bus`; `q : bus`; `width w`]
      badder3_width_out2) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?p0. wire p 0 p0` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
   ALL_TAC] THEN
  SUBGOAL_THEN `?p1. bsub p 1 n p1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `width p1 = n` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `p : bus` THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?q1. bsub q 0 n q1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [LE_ADD_LCANCEL; LE_0];
   ALL_TAC] THEN
  SUBGOAL_THEN `width q1 = n` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `q : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?q2. wire q n q2` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [LT_ADD; LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
   ALL_TAC] THEN
  MP_TAC (SPECL [`p0 : wire`; `z0 : wire`] adder2_exists) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s0 : wire`
      (X_CHOOSE_THEN `c0 : wire` STRIP_ASSUME_TAC)) THEN
  MP_TAC (SPECL [`p1 : bus`; `q1 : bus`; `z1 : bus`] badder3_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s1 : bus`
      (X_CHOOSE_THEN `c1 : bus` STRIP_ASSUME_TAC)) THEN
  MP_TAC
   (SPECL [`p1 : bus`; `q1 : bus`; `z1 : bus`; `s1 : bus`; `c1 : bus`; `n : num`]
      badder3_width_out1) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
   (SPECL [`p1 : bus`; `q1 : bus`; `z1 : bus`; `s1 : bus`; `c1 : bus`; `n : num`]
      badder3_width_out2) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `q2 : wire` connect_exists) THEN
  DISCH_THEN (X_CHOOSE_THEN `s2 : wire` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `bappend (bwire s0) (bappend s1 (bwire s2))` THEN
  EXISTS_TAC `bappend (bwire c0) c1` THEN
  EXISTS_TAC `n : num` THEN
  EXISTS_TAC `p : bus` THEN
  EXISTS_TAC `q : bus` THEN
  EXISTS_TAC `z0 : wire` THEN
  EXISTS_TAC `z1 : bus` THEN
  EXISTS_TAC `s0 : wire` THEN
  EXISTS_TAC `s1 : bus` THEN
  EXISTS_TAC `s2 : wire` THEN
  EXISTS_TAC `c0 : wire` THEN
  EXISTS_TAC `c1 : bus` THEN
  EXISTS_TAC `p0 : wire` THEN
  EXISTS_TAC `p1 : bus` THEN
  EXISTS_TAC `q1 : bus` THEN
  EXISTS_TAC `q2 : wire` THEN
  ASM_REWRITE_TAC
    [wire_zero; bappend_width; bwire_width; ONE; TWO; ADD_SUC;
     SUC_ADD; ADD_0; ZERO_ADD; wire_suc] THEN
  REPEAT CONJ_TAC THENL
  [SUBGOAL_THEN `SUC 0 = width (bwire s0) + 0` SUBST1_TAC THENL
   [REWRITE_TAC [bwire_width; ONE; ADD_0];
    ALL_TAC] THEN
   REWRITE_TAC [bsub_in_suffix] THEN
   SUBGOAL_THEN `n = width s1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [bsub_prefix];
   SUBGOAL_THEN `n = width s1 + 0` SUBST1_TAC THENL
   [ASM_REWRITE_TAC [ADD_0];
    ALL_TAC] THEN
   REWRITE_TAC [wire_in_suffix; bwire_wire];
   SUBGOAL_THEN `SUC 0 = width (bwire c0) + 0` SUBST1_TAC THENL
   [REWRITE_TAC [bwire_width; ONE; ADD_0];
    ALL_TAC] THEN
   REWRITE_TAC [bsub_in_suffix] THEN
   SUBGOAL_THEN `n = width c1` SUBST1_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [bsub_all]]);;

export_thm badder4_exists;;

let badder4_bits_to_num = prove
 (`!w x y z s c t.
     badder4 w x y z s c ==>
     bits_to_num (bsignal w t) + bits_to_num (bsignal x t) +
     bits_to_num (bsignal y t) + bits_to_num (bsignal z t) =
     bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder4_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : bus`; `x : bus`; `y : bus`;
        `p : bus`; `q : bus`; `t : cycle`]
       badder3_bits_to_num) THEN
  ASM_REWRITE_TAC [ADD_ASSOC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `bappend (bwire z0) z1 = z` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend (bwire p0) p1 = p` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend q1 (bwire q2) = q` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend (bwire s0) (bappend s1 (bwire s2)) = s`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN `n + 2 = 1 + (n + 1)` SUBST1_TAC THENL
   [REWRITE_TAC [TWO; ONE; ADD_SUC; SUC_ADD; ZERO_ADD; ADD_0];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM wire_def] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend (bwire c0) c1 = c` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal p0 t) +
      bit_to_num (signal z0 t)) +
     (2 * bits_to_num (bsignal p1 t) +
      2 * bits_to_num (bsignal (bappend q1 (bwire q2)) t) +
      2 * bits_to_num (bsignal z1 t))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal s0 t) +
      2 * bit_to_num (signal c0 t)) +
     (2 * bits_to_num (bsignal (bappend s1 (bwire s2)) t) +
      2 * (2 * bits_to_num (bsignal c1 t)))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL; LEFT_ADD_DISTRIB] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal s0 t) +
      2 * bit_to_num (signal c0 t)) +
     (2 * bits_to_num (bsignal p1 t) +
      2 * bits_to_num (bsignal (bappend q1 (bwire q2)) t) +
      2 * bits_to_num (bsignal z1 t))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   MATCH_MP_TAC adder2_bit_to_num THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  REWRITE_TAC [GSYM LEFT_ADD_DISTRIB] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [bappend_bits_to_num; bwire_bsignal; bits_to_num_sing] THEN
  SUBGOAL_THEN `width q1 = n` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `q : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width s1 = n` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `s : bus` THEN
   EXISTS_TAC `1` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal p1 t) +
      bits_to_num (bsignal q1 t) +
      bits_to_num (bsignal z1 t)) +
     bit_shl (bit_to_num (signal q2 t)) n` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal s1 t) + 2 * bits_to_num (bsignal c1 t)) +
     bit_shl (bit_to_num (signal s2 t)) n` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal s1 t) + 2 * bits_to_num (bsignal c1 t)) +
     bit_shl (bit_to_num (signal q2 t)) n` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   MATCH_MP_TAC badder3_bits_to_num THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [EQ_ADD_LCANCEL; bit_shl_inj] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC connect_signal THEN
  ASM_REWRITE_TAC []);;

export_thm badder4_bits_to_num;;

let scshiftr_width = prove
 (`!ld xs xc xb.
     scshiftr ld xs xc xb ==>
     ?r.
       width xs = r + 1 /\
       width xc = r + 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scshiftr_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `r : num` THEN
  ASM_REWRITE_TAC []);;

export_thm scshiftr_width;;

let scshiftr_signal = prove
 (`!x ld xs xc xb t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     scshiftr ld xs xc xb ==>
     signal xb (t + k) = bit_nth x k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scshiftr_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC [bit_nth_def] THEN
  REVERSE_TAC
    (SUBGOAL_THEN
       `bit_cons
          (signal xb (t + k))
          (bits_to_num (bsignal sr (t + k)) +
           bits_to_num (bsignal cr (t + k))) =
        bit_shr x k`
       (SUBST1_TAC o SYM)) THENL
  [REWRITE_TAC [bit_hd_cons];
   ALL_TAC] THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  INDUCT_TAC THENL
  [DISCH_THEN (MP_TAC o SPEC `0`) THEN
   REWRITE_TAC [LE_REFL; ADD_0; bit_shr_zero] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
       [`ld : wire`;
        `xs0 : wire`;
        `sq0 : wire`;
        `xb : wire`;
        `t : cycle`]
       case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
       [`ld : wire`;
        `xs1 : bus`;
        `sq2 : bus`;
        `sr : bus`;
        `t : cycle`]
       bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
       [`ld : wire`;
        `xc : bus`;
        `cq : bus`;
        `cr : bus`;
        `t : cycle`]
       bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_THEN
     `bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x`
     (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [bit_cons_def; LEFT_ADD_DISTRIB; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   SUBGOAL_THEN `xs = bappend (bwire xs0) xs1` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    ASM_REWRITE_TAC [GSYM bsub_all] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [GSYM wire_def; ZERO_ADD];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def];
   ALL_TAC] THEN
  DISCH_THEN (fun th -> MP_TAC (SPEC `SUC k` th) THEN ASSUME_TAC th) THEN
  REWRITE_TAC [LE_REFL; NOT_SUC] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`ld : wire`;
       `xs0 : wire`;
       `sq0 : wire`;
       `xb : wire`;
       `t + SUC k : cycle`]
      case1_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
      [`ld : wire`;
       `xs1 : bus`;
       `sq2 : bus`;
       `sr : bus`;
       `t + SUC k : cycle`]
      bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
      [`ld : wire`;
       `xc : bus`;
       `cq : bus`;
       `cr : bus`;
       `t + SUC k : cycle`]
      bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bit_cons_def; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bit_to_num (signal sq0 (t + SUC k)) +
     2 * bits_to_num (bsignal sq2 (t + SUC k)) =
     bits_to_num (bsignal sq1 (t + SUC k)) +
     bit_shl (bit_to_num (signal sq3 (t + SUC k))) r`
    SUBST1_TAC THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `bits_to_num (bsignal sq (t + SUC k))` THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN `sq = bappend (bwire sq0) sq2` SUBST1_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     ASM_REWRITE_TAC [GSYM bsub_all] THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [GSYM wire_def; ZERO_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def];
    SUBGOAL_THEN `sq = bappend sq1 (bwire sq3)` SUBST1_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     ASM_REWRITE_TAC [GSYM bsub_all] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [GSYM wire_def; ZERO_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num; bwire_bsignal; bits_to_num_sing] THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sq : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  SUBGOAL_THEN `cq = bappend cq0 (bwire cq1)` SUBST1_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   ASM_REWRITE_TAC [GSYM bsub_all] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM wire_def; ZERO_ADD];
   ALL_TAC] THEN
  REWRITE_TAC [bappend_bits_to_num; bwire_bsignal; bits_to_num_sing] THEN
  MP_TAC
    (SPECL
      [`cp1 : wire`;
       `sq3 : wire`;
       `t + SUC k : cycle`]
      connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
      [`ground`;
       `cq1 : wire`;
       `t + SUC k : cycle`]
      connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [ground_signal; zero_bit_shl; bit_to_num_false; ADD_0] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal sq1 (t + SUC k)) +
      2 * bits_to_num (bsignal cq0 (t + SUC k))) +
     bit_shl (bit_to_num (signal cp1 (t + SUC k))) r` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`sp : bus`;
        `cp0 : bus`;
        `sq1 : bus`;
        `cq0 : bus`;
        `t + SUC k`]
       badder2_bits_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `bits_to_num (bsignal sp (t + SUC k)) +
     bits_to_num (bsignal cp (t + SUC k))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   SUBGOAL_THEN `cp = bappend cp0 (bwire cp1)` SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    ASM_REWRITE_TAC [GSYM bsub_all] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [GSYM wire_def; ZERO_ADD];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bits_to_num; bwire_bsignal; bits_to_num_sing] THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `cp : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
      [`sr : bus`;
       `sp : bus`;
       `t + k : cycle`]
      bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD1; ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
      [`cr : bus`;
       `cp : bus`;
       `t + k : cycle`]
      bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD1; ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bit_shr_suc] THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [bit_tl_cons]);;

export_thm scshiftr_signal;;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-adder-tools.ml";;

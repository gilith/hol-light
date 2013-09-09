(* ========================================================================= *)
(* ADDER DEVICES                                                             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of adder devices.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-adder-def";;

(* ------------------------------------------------------------------------- *)
(* Wire adder devices.                                                       *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Bus adder devices.                                                        *)
(* ------------------------------------------------------------------------- *)

let badder2_def = new_definition
  `!x y s c.
     badder2 x y s c <=>
     ?n.
       width x = n /\
       width y = n /\
       width s = n /\
       width c = n /\
       bxor2 x y s /\
       band2 x y c`;;

export_thm badder2_def;;

let badder3_def = new_definition
  `!x y z s c.
     badder3 x y z s c <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       width s = n /\
       width c = n /\
       bxor3 x y z s /\
       bmajority3 x y z c`;;

export_thm badder3_def;;

(***
let badder4_def = new_definition
  `!w x y z s c.
     badder4 w x y z s c <=>
     ?n p q p0 p1 q1 z0 z1 s0 s1 s2 c0 c1.
       width w = n + 1 /\
       width x = n + 1 /\
       width y = n + 1 /\
       width z = n + 1 /\
       width s = n + 2 /\
       width c = n + 1 /\
       badder3 w x y p q /\
       bsub p 0 1 p0 /\
       bsub z 0 1 z0 /\
       badder2 p0 z0 s0 c0 /\
       bsub p 1 n p1 /\
       bsub q 0 n q1 /\
       bsub z 1 n z1 /\
       badder3 p1 q1 z1 s1 c1 /\
       bsub q n 1 s2 /\
       s = bappend s0 (bappend s1 s2) /\
       c = bappend c0 c1`;;

export_thm badder4_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties of adder devices.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-adder-thm";;

(* ------------------------------------------------------------------------- *)
(* Wire adder devices.                                                       *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Bus adder devices.                                                        *)
(* ------------------------------------------------------------------------- *)

let badder2_width1 = prove
 (`!x y s c.
     badder2 x y s c ==>
     width s = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bxor2_width THEN
  EXISTS_TAC `y : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_width1;;

let badder2_width2 = prove
 (`!x y s c.
     badder2 x y s c ==>
     width c = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC band2_width THEN
  EXISTS_TAC `y : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder2_width2;;

let badder2_bwire = prove
 (`!x y s c.
     badder2 (bwire x) (bwire y) (bwire s) (bwire c) <=>
     adder2 x y s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def; adder2_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [bwire_width; bxor2_bwire; band2_bwire];
   ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [GSYM bxor2_bwire; GSYM band2_bwire]);;

export_thm badder2_bwire;;

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
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `s : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `c : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
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
     wire x i xi /\ wire y i yi /\
     wire s i si /\ wire c i ci ==>
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

let badder3_width1 = prove
 (`!x y z s c.
     badder3 x y z s c ==>
     width s = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bxor3_width THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_width1;;

let badder3_width2 = prove
 (`!x y z s c.
     badder3 x y z s c ==>
     width c = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bmajority3_width THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm badder3_width2;;

let badder3_bwire = prove
 (`!x y z s c.
     badder3 (bwire x) (bwire y) (bwire z) (bwire s) (bwire c) <=>
     adder3 x y z s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def; adder3_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [bwire_width; bxor3_bwire; bmajority3_bwire];
   ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [GSYM bxor3_bwire; GSYM bmajority3_bwire]);;

export_thm badder3_bwire;;

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
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC) THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `s : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `c : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
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

let badder3_right_bground = prove
 (`!x y n s c.
     width x = n /\ badder2 x y s c ==>
     badder3 x y (bground n) s c`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder2_def; badder3_def] THEN
  CONV_TAC (REWR_CONV (GSYM IMP_IMP)) THEN
  DISCH_THEN SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [bground_width] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor3_right_bground THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bmajority3_right_bground THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_right_bground;;

(***
let badder3_bits_to_num = prove
 (`!x y z s c t.
     badder3 x y z s c ==>
     bits_to_num (bsignal x t) + bits_to_num (bsignal y t) +
     bits_to_num (bsignal z t) =
     bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [badder3_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
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
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zh : wire`
      (X_CHOOSE_THEN `zt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `sh : wire`
      (X_CHOOSE_THEN `st : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch : wire`
      (X_CHOOSE_THEN `ct : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
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
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [wire_suc];
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [wire_zero] THEN
   DISCH_THEN
     (ASSUME_TAC o
      REWRITE_RULE [] o
      SPECL
        [`xh : wire`; `yh : wire`; `zh : wire`;
         `sh : wire`; `ch : wire`]) THEN
   MATCH_MP_TAC adder3 THEN
   ASM_REWRITE_TAC []]);;

export_thm badder3_bits_to_num;;
***)

logfile_end ();;

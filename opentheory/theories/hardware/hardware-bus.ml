(* ========================================================================= *)
(* BASIC BUS DEVICES                                                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-bus-def";;

(* ------------------------------------------------------------------------- *)
(* Primitive bus devices.                                                    *)
(* ------------------------------------------------------------------------- *)

let bdelay_def = new_definition
  `!x y.
     bdelay x y <=>
     ?n.
       width x = n /\
       width y = n /\
       !i xi yi.
         wire x i xi /\
         wire y i yi ==>
         delay xi yi`;;

export_thm bdelay_def;;

let bnot_def = new_definition
  `!x y.
     bnot x y <=>
     ?n.
       width x = n /\
       width y = n /\
       !i xi yi.
         wire x i xi /\
         wire y i yi ==>
         not xi yi`;;

export_thm bnot_def;;

let band2_def = new_definition
  `!x y z.
     band2 x y z <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       !i xi yi zi.
         wire x i xi /\
         wire y i yi /\
         wire z i zi ==>
         and2 xi yi zi`;;

export_thm band2_def;;

let bor2_def = new_definition
  `!x y z.
     bor2 x y z <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       !i xi yi zi.
         wire x i xi /\
         wire y i yi /\
         wire z i zi ==>
         or2 xi yi zi`;;

export_thm bor2_def;;

let bxor2_def = new_definition
  `!x y z.
     bxor2 x y z <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       !i xi yi zi.
         wire x i xi /\
         wire y i yi /\
         wire z i zi ==>
         xor2 xi yi zi`;;

export_thm bxor2_def;;

let bcase1_def = new_definition
  `!s x y z.
     bcase1 s x y z <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       !i xi yi zi.
         wire x i xi /\
         wire y i yi /\
         wire z i zi ==>
         case1 s xi yi zi`;;

export_thm bcase1_def;;

(* ------------------------------------------------------------------------- *)
(* Simple bus devices.                                                       *)
(* ------------------------------------------------------------------------- *)

let band3_def = new_definition
  `!w x y z.
     band3 w x y z <=>
     ?wx. band2 w x wx /\ band2 wx y z`;;

export_thm band3_def;;

let bor3_def = new_definition
  `!w x y z.
     bor3 w x y z <=>
     ?wx. bor2 w x wx /\ bor2 wx y z`;;

export_thm bor3_def;;

let bxor3_def = new_definition
  `!w x y z.
     bxor3 w x y z <=>
     ?wx. bxor2 w x wx /\ bxor2 wx y z`;;

export_thm bxor3_def;;

let bmajority3_def = new_definition
  `!w x y z.
     bmajority3 w x y z <=>
     ?wx wy xy.
       band2 w x wx /\ band2 w y wy /\ band2 x y xy /\
       bor3 wx wy xy z`;;

export_thm bmajority3_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-bus-thm";;

(* ------------------------------------------------------------------------- *)
(* Primitive bus devices.                                                    *)
(* ------------------------------------------------------------------------- *)

let bdelay_width = prove
 (`!x y.
     bdelay x y ==>
     width y = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bdelay_width;;

let bdelay_bsignal = prove
 (`!x y t. bdelay x y ==> bsignal y (t + 1) = bsignal x t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [bnil_bsignal];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [bappend_bwire_bsignal; CONS_11] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC delay_signal THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [wire_zero];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [wire_suc]]);;

export_thm bdelay_bsignal;;

let bdelay_wire = prove
 (`!x y i xi yi. bdelay x y /\ wire x i xi /\ wire y i yi ==> delay xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bdelay_wire;;

let bdelay_bwire = prove
 (`!x y. bdelay (bwire x) (bwire y) <=> delay x y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC bdelay_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [bdelay_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bdelay_bwire;;

let bdelay_bsub = prove
 (`!x y k n xs ys.
     bdelay x y /\
     bsub x k n xs /\
     bsub y k n ys ==>
     bdelay xs ys`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bdelay_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bdelay_bsub;;

let bnot_width = prove
 (`!x y.
     bnot x y ==>
     width y = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bnot_width;;

let bnot_wire = prove
 (`!x y i xi yi. bnot x y /\ wire x i xi /\ wire y i yi ==> not xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bnot_wire;;

let bnot_bwire = prove
 (`!x y. bnot (bwire x) (bwire y) <=> not x y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC bnot_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [bnot_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bnot_bwire;;

let bnot_bsub = prove
 (`!x y k n xs ys.
     bnot x y /\
     bsub x k n xs /\
     bsub y k n ys ==>
     bnot xs ys`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bnot_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bnot_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bnot_bsub;;

let band2_width = prove
 (`!x y z.
     band2 x y z ==>
     width z = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm band2_width;;

let band2_wire = prove
 (`!x y z i xi yi zi.
     band2 x y z /\
     wire x i xi /\ wire y i yi /\ wire z i zi ==>
     and2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm band2_wire;;

let band2_bwire = prove
 (`!x y z. band2 (bwire x) (bwire y) (bwire z) <=> and2 x y z`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC band2_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `bwire z` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [band2_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm band2_bwire;;

let band2_bsub = prove
 (`!x y z k n xs ys zs.
     band2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     band2 xs ys zs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [band2_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC band2_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `zs : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm band2_bsub;;

let bor2_width = prove
 (`!x y z.
     bor2 x y z ==>
     width z = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bor2_width;;

let bor2_wire = prove
 (`!x y z i xi yi zi.
     bor2 x y z /\
     wire x i xi /\ wire y i yi /\ wire z i zi ==>
     or2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bor2_wire;;

let bor2_bwire = prove
 (`!x y z. bor2 (bwire x) (bwire y) (bwire z) <=> or2 x y z`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC bor2_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `bwire z` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [bor2_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bor2_bwire;;

let bor2_bsub = prove
 (`!x y z k n xs ys zs.
     bor2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bor2 xs ys zs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bor2_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bor2_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `zs : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bor2_bsub;;

let bxor2_width = prove
 (`!x y z.
     bxor2 x y z ==>
     width z = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bxor2_width;;

let bxor2_wire = prove
 (`!x y z i xi yi zi.
     bxor2 x y z /\
     wire x i xi /\ wire y i yi /\ wire z i zi ==>
     xor2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bxor2_wire;;

let bxor2_bwire = prove
 (`!x y z. bxor2 (bwire x) (bwire y) (bwire z) <=> xor2 x y z`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC bxor2_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `bwire z` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [bxor2_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bxor2_bwire;;

let bxor2_bsub = prove
 (`!x y z k n xs ys zs.
     bxor2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bxor2 xs ys zs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bxor2_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `zs : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bxor2_bsub;;

let bcase1_width = prove
 (`!s x y z.
     bcase1 s x y z ==>
     width z = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bcase1_width;;

let bcase1_bsignal = prove
 (`!s x y z t.
      bcase1 s x y z ==>
      bsignal z t = (if signal s t then bsignal x t else bsignal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`z : bus`, `z : bus`) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [bnil_bsignal; COND_ID];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zh : wire`
      (X_CHOOSE_THEN `zt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [bappend_bwire_bsignal] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `CONS
      (if signal s t then signal xh t else signal yh t)
      (if signal s t then bsignal xt t else bsignal yt t)` THEN
  REVERSE_TAC CONJ_TAC THENL
  [COND_CASES_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [CONS_11] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC case1_signal THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [wire_zero];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [wire_suc]]);;

export_thm bcase1_bsignal;;

let bcase1_wire = prove
 (`!s x y z i xi yi zi.
     bcase1 s x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     case1 s xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bcase1_wire;;

let bcase1_bwire = prove
 (`!s x y z. bcase1 s (bwire x) (bwire y) (bwire z) <=> case1 s x y z`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC bcase1_wire THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   EXISTS_TAC `bwire z` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [bwire_wire];
   STRIP_TAC THEN
   REWRITE_TAC [bcase1_def; bwire_wire] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [bwire_width] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bcase1_bwire;;

let bcase1_bsub = prove
 (`!s x y z k n xs ys zs.
     bcase1 s x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bcase1 s xs ys zs`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
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
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC bcase1_wire THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `k + i : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `zs : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bcase1_bsub;;

(* ------------------------------------------------------------------------- *)
(* Simple bus devices.                                                       *)
(* ------------------------------------------------------------------------- *)

let band3_width = prove
 (`!w x y z.
     band3 w x y z ==>
     width z = width w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `width wx` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_width THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_width THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm band3_width;;

let band3_bwire = prove
 (`!w x y z.
     band3 (bwire w) (bwire x) (bwire y) (bwire z) <=>
     and3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band3_def; and3_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `bwire wx` THEN
   ASM_REWRITE_TAC [band2_bwire];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bwx : bus` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `width bwx = 1`
    (X_CHOOSE_THEN `wx : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire w)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC band2_width THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM band2_bwire]);;

export_thm band3_bwire;;

let band3_bsub = prove
 (`!w x y z k n ws xs ys zs.
     band3 w x y z /\
     bsub w k n ws /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     band3 ws xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wxs : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `wxs : bus` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm band3_bsub;;

let band3_wire = prove
 (`!w x y z i wi xi yi zi.
     band3 w x y z /\
     wire w i wi /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     and3 wi xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM band3_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC band3_bsub THEN
  EXISTS_TAC `w : bus` THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm band3_wire;;

let bor3_width = prove
 (`!w x y z.
     bor3 w x y z ==>
     width z = width w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `width wx` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor2_width THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bor2_width THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bor3_width;;

let bor3_bwire = prove
 (`!w x y z.
     bor3 (bwire w) (bwire x) (bwire y) (bwire z) <=>
     or3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def; or3_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `bwire wx` THEN
   ASM_REWRITE_TAC [bor2_bwire];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bwx : bus` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `width bwx = 1`
    (X_CHOOSE_THEN `wx : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire w)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC bor2_width THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM bor2_bwire]);;

export_thm bor3_bwire;;

let bor3_bsub = prove
 (`!w x y z k n ws xs ys zs.
     bor3 w x y z /\
     bsub w k n ws /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bor3 ws xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] bor2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wxs : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `wxs : bus` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor2_bsub THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bor2_bsub THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm bor3_bsub;;

let bor3_wire = prove
 (`!w x y z i wi xi yi zi.
     bor3 w x y z /\
     wire w i wi /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     or3 wi xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM bor3_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bor3_bsub THEN
  EXISTS_TAC `w : bus` THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm bor3_wire;;

let bxor3_width = prove
 (`!w x y z.
     bxor3 w x y z ==>
     width z = width w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `width wx` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_width THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bxor2_width THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bxor3_width;;

let bxor3_bwire = prove
 (`!w x y z.
     bxor3 (bwire w) (bwire x) (bwire y) (bwire z) <=>
     xor3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def; xor3_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `bwire wx` THEN
   ASM_REWRITE_TAC [bxor2_bwire];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bwx : bus` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `width bwx = 1`
    (X_CHOOSE_THEN `wx : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire w)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC bxor2_width THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM bxor2_bwire]);;

export_thm bxor3_bwire;;

let bxor3_bsub = prove
 (`!w x y z k n ws xs ys zs.
     bxor3 w x y z /\
     bsub w k n ws /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bxor3 ws xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] bxor2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wxs : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `wxs : bus` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_bsub THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bxor2_bsub THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm bxor3_bsub;;

let bxor3_wire = prove
 (`!w x y z i wi xi yi zi.
     bxor3 w x y z /\
     wire w i wi /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     xor3 wi xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM bxor3_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bxor3_bsub THEN
  EXISTS_TAC `w : bus` THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm bxor3_wire;;

let bmajority3_width = prove
 (`!w x y z.
     bmajority3 w x y z ==>
     width z = width w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `width wx` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor3_width THEN
   EXISTS_TAC `wy : bus` THEN
   EXISTS_TAC `xy : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_width THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm bmajority3_width;;

let bmajority3_bwire = prove
 (`!w x y z.
     bmajority3 (bwire w) (bwire x) (bwire y) (bwire z) <=>
     majority3 w x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def; majority3_def] THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `bwire wx` THEN
   EXISTS_TAC `bwire wy` THEN
   EXISTS_TAC `bwire xy` THEN
   ASM_REWRITE_TAC [band2_bwire; bor3_bwire];
   ALL_TAC] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `bwx : bus`
      (X_CHOOSE_THEN `bwy : bus`
        (X_CHOOSE_THEN `bxy : bus`
          STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `width bwx = 1`
    (X_CHOOSE_THEN `wx : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire w)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC band2_width THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  SUBGOAL_THEN `width bwy = 1`
    (X_CHOOSE_THEN `wy : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire w)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC band2_width THEN
    EXISTS_TAC `bwire y` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  SUBGOAL_THEN `width bxy = 1`
    (X_CHOOSE_THEN `xy : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `width (bwire x)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC band2_width THEN
    EXISTS_TAC `bwire y` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  EXISTS_TAC `wy : wire` THEN
  EXISTS_TAC `xy : wire` THEN
  ASM_REWRITE_TAC [GSYM band2_bwire; GSYM bor3_bwire]);;

export_thm bmajority3_bwire;;

let bmajority3_bsub = prove
 (`!w x y z k n ws xs ys zs.
     bmajority3 w x y z /\
     bsub w k n ws /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bmajority3 ws xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wxs : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`wy : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`w : bus`; `y : bus`; `wy : bus`] band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wys : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`xy : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC (SPECL [`x : bus`; `y : bus`; `xy : bus`] band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `xys : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `wxs : bus` THEN
  EXISTS_TAC `wys : bus` THEN
  EXISTS_TAC `xys : bus` THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `wy : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC band2_bsub THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `xy : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bor3_bsub THEN
   EXISTS_TAC `wx : bus` THEN
   EXISTS_TAC `wy : bus` THEN
   EXISTS_TAC `xy : bus` THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `k : num` THEN
   EXISTS_TAC `n : num` THEN
   ASM_REWRITE_TAC []]);;

export_thm bmajority3_bsub;;

let bmajority3_wire = prove
 (`!w x y z i wi xi yi zi.
     bmajority3 w x y z /\
     wire w i wi /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     majority3 wi xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM bmajority3_bwire] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bmajority3_bsub THEN
  EXISTS_TAC `w : bus` THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `y : bus` THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm bmajority3_wire;;

logfile_end ();;

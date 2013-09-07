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

(* ------------------------------------------------------------------------- *)
(* Simple bus devices.                                                       *)
(* ------------------------------------------------------------------------- *)

logfile_end ();;

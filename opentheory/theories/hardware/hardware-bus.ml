(* ========================================================================= *)
(* HARDWARE BUS DEVICES                                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware bus devices.                                       *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-bus-def";;

(* ~~~~~~~~~ *)
(* Bus wires *)
(* ~~~~~~~~~ *)

let wire_def = new_definition
  `!x i w. wire x i w <=> bsub x i 1 (bwire w)`;;

export_thm wire_def;;

(* ~~~~~~~~~~~~~~~ *)
(* Reversing a bus *)
(* ~~~~~~~~~~~~~~~ *)

let brev_def = new_definition
  `!x y.
     brev x y <=>
     width x = width y /\
     !i j xi yj. i + j + 1 = width x /\ wire x i xi /\ wire y j yj ==> xi = yj`;;

export_thm brev_def;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Lifting relations between wires *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let blift2_def = new_definition
  `!r x y.
     blift2 r x y <=>
     ?n.
       width x = n /\
       width y = n /\
       !i xi yi.
         wire x i xi /\
         wire y i yi ==>
         r xi yi`;;

export_thm blift2_def;;

let blift3_def = new_definition
  `!r x y z.
     blift3 r x y z <=>
     ?n.
       width x = n /\
       width y = n /\
       width z = n /\
       !i xi yi zi.
         wire x i xi /\
         wire y i yi /\
         wire z i zi ==>
         r xi yi zi`;;

export_thm blift3_def;;

(* ~~~~~~~~~~~~~~~~~~ *)
(* Lifted bus devices *)
(* ~~~~~~~~~~~~~~~~~~ *)

let bconnect_def = new_definition
  `bconnect = blift2 connect`;;

export_thm bconnect_def;;

let bdelay_def = new_definition
  `bdelay = blift2 delay`;;

export_thm bdelay_def;;

let bnot_def = new_definition
  `bnot = blift2 not`;;

export_thm bnot_def;;

let band2_def = new_definition
  `band2 = blift3 and2`;;

export_thm band2_def;;

let bor2_def = new_definition
  `bor2 = blift3 or2`;;

export_thm bor2_def;;

let bxor2_def = new_definition
  `bxor2 = blift3 xor2`;;

export_thm bxor2_def;;

let bcase1_def = new_definition
  `!s. bcase1 s = blift3 (case1 s)`;;

export_thm bcase1_def;;

(* ~~~~~~~~~~~~~~~~~~~ *)
(* Derived bus devices *)
(* ~~~~~~~~~~~~~~~~~~~ *)

let band3_def = new_definition
  `!w x y z.
     band3 w x y z <=>
     ?wx.
       band2 w x wx /\
       band2 wx y z`;;

export_thm band3_def;;

let bor3_def = new_definition
  `!w x y z.
     bor3 w x y z <=>
     ?wx.
       bor2 w x wx /\
       bor2 wx y z`;;

export_thm bor3_def;;

let bxor3_def = new_definition
  `!w x y z.
     bxor3 w x y z <=>
     ?wx.
       bxor2 w x wx /\
       bxor2 wx y z`;;

export_thm bxor3_def;;

let bmajority3_def = new_definition
  `!w x y z.
     bmajority3 w x y z <=>
     ?wx wy xy.
       band2 w x wx /\
       band2 w y wy /\
       band2 x y xy /\
       bor3 wx wy xy z`;;

export_thm bmajority3_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-bus-thm";;

(* ~~~~~~~~~ *)
(* Bus wires *)
(* ~~~~~~~~~ *)

let wire_inj = prove
 (`!x i w1 w2.
     wire x i w1 /\ wire x i w2 ==>
     w1 = w2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bwire_inj_imp THEN
  MATCH_MP_TAC bsub_inj THEN
  EXISTS_TAC `x : bus` THEN
  EXISTS_TAC `i : num` THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC []);;

export_thm wire_inj;;

let wire_exists = prove
 (`!x i. i < width x ==> ?w. wire x i w`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `i : num`; `1`] bsub_exists) THEN
  ASM_REWRITE_TAC [GSYM ADD1; LE_SUC_LT] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `i : num`; `1`; `y : bus`] bsub_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`y : bus`] width_one) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  EXISTS_TAC `w : wire` THEN
  ASM_REWRITE_TAC [wire_def]);;

export_thm wire_exists;;

let wire_in_prefix = prove
 (`!x y i w. i < width x ==> (wire (bappend x y) i w <=> wire x i w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; GSYM LE_SUC_LT; ADD1] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bsub_in_prefix THEN
  ASM_REWRITE_TAC []);;

export_thm wire_in_prefix;;

let wire_in_suffix = prove
 (`!x y i w. wire (bappend x y) (width x + i) w <=> wire y i w`,
  REWRITE_TAC [wire_def; bsub_in_suffix]);;

export_thm wire_in_suffix;;

let bsub_suc = prove
  (`!x w y k n.
      wire x k w /\ bsub x (SUC k) n y ==>
      bsub x k (SUC n) (bappend (bwire w) y)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD1] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD1; GSYM wire_def]);;

export_thm bsub_suc;;

let bsub_wire = prove
 (`!x k n y i w.
     bsub x k n y ==>
     (wire y i w <=> i < n /\ wire x (k + i) w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [wire_def; ADD1; GSYM LE_SUC_LT] THEN
  MATCH_MP_TAC bsub_bsub THEN
  ASM_REWRITE_TAC []);;

export_thm bsub_wire;;

let bsub_wire_imp = prove
 (`!x k n y i w.
     bsub x k n y /\
     wire y i w ==>
     wire x (k + i) w`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `k : num`; `n : num`; `y : bus`;
        `i : num`; `w : wire`]
       bsub_wire) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC);;

export_thm bsub_wire_imp;;

let wire_bound = prove
  (`!x i w. wire x i w ==> i < width x`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD1; GSYM LE_SUC_LT] THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `bwire w` THEN
   ASM_REWRITE_TAC [GSYM wire_def]);;

export_thm wire_bound;;

let wire_zero = prove
 (`!w x v. wire (bappend (bwire w) x) 0 v <=> v = w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def] THEN
  MP_TAC (SPECL [`bwire w`; `x : bus`; `bwire v`] bsub_prefix) THEN
  REWRITE_TAC [bwire_width; bwire_inj]);;

export_thm wire_zero;;

let wire_suc = prove
 (`!w x i v. wire (bappend (bwire w) x) (SUC i) v <=> wire x i v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; ADD1] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  MP_TAC
    (SPECL [`bwire w`; `x : bus`; `i : num`; `1`; `bwire v`]
     bsub_in_suffix) THEN
  REWRITE_TAC [bwire_width]);;

export_thm wire_suc;;

let bnil_wire = prove
 (`!i w. ~wire bnil i w`,
  REWRITE_TAC [wire_def; bnil_bsub; ONE; NOT_SUC]);;

export_thm bnil_wire;;

let bwire_wire = prove
 (`!w i v. wire (bwire w) i v <=> i = 0 /\ v = w`,
  REPEAT GEN_TAC THEN
  CONV_TAC
    (LAND_CONV (RATOR_CONV (LAND_CONV (REWR_CONV (GSYM bappend_bnil))))) THEN
  MP_TAC (SPEC `i : num` num_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [wire_zero];
   ASM_REWRITE_TAC [wire_suc; NOT_SUC; bnil_wire]]);;

export_thm bwire_wire;;

let wire_bits_to_num = prove
 (`!x i w t.
     wire x i w /\ signal w t ==>
     2 EXP i <= bits_to_num (bsignal x t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def] THEN
  STRIP_TAC THEN
  STP_TAC `bit_shl (bits_to_num (bsignal (bwire w) t)) i = 2 EXP i` THENL
  [DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC bsub_bits_to_num_le THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [bwire_bsignal; bits_to_num_sing; bit_to_num_true; one_bit_shl]);;

export_thm wire_bits_to_num;;

let bit_nth_wire_bits_to_num = prove
 (`!n x t.
     (!i xi. wire x i xi ==> signal xi t = bit_nth n i) ==>
     bits_to_num (bsignal x t) = bit_bound n (width x)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?m. width x = m` MP_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  REWRITE_TAC [LEFT_IMP_EXISTS_THM; IMP_IMP] THEN
  GEN_TAC THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`m : num`, `m : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [bnil_width; bit_bound_zero; bnil_bsignal; bits_to_num_nil];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [bit_bound_suc] THEN
  UNDISCH_THEN
    `width x = SUC m`
    (STRIP_ASSUME_TAC o REWRITE_RULE [width_suc]) THEN
  UNDISCH_THEN `x = bappend (bwire w) y` SUBST_VAR_TAC THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; bwire_bits_to_num; bappend_width; bwire_width] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`y : bus`; `bit_tl n`]) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [GSYM bit_nth_suc] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [wire_suc];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [bit_shl_one; GSYM bit_cons_def; GSYM bit_nth_zero] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  REWRITE_TAC [wire_zero]);;

export_thm bit_nth_wire_bits_to_num;;

let wire_signal = prove
 (`!x y i xi yi xt yt.
     wire x i xi /\ wire y i yi /\ bsignal x xt = bsignal y yt ==>
     signal xi xt = signal yi yt`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`;
        `y : bus`;
        `i : num`;
        `1`;
        `bwire xi`;
        `bwire yi`;
        `xt : cycle`;
        `yt : cycle`]
       bsub_bsignal) THEN
  ASM_REWRITE_TAC [GSYM wire_def; bwire_bsignal; CONS_11]);;

export_thm wire_signal;;

let bground_wire = prove
 (`!n k w. wire (bground n) k w <=> k < n /\ w = ground`,
  REWRITE_TAC
    [wire_def; bground_bsub; GSYM ADD1; LE_SUC_LT; bground_one; bwire_inj]);;

export_thm bground_wire;;

(* ~~~~~~~~~~~~~~~ *)
(* Reversing a bus *)
(* ~~~~~~~~~~~~~~~ *)

let brev_width = prove
 (`!x y.
     brev x y ==>
     ?n.
       width x = n /\
       width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [brev_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `width y` THEN
  ASM_REWRITE_TAC []);;

export_thm brev_width;;

let brev_width_out = prove
 (`!x y n.
     brev x y /\ width x = n ==>
     width y = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`] brev_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm brev_width_out;;

let brev_wire_out = prove
 (`!x y j yj.
     brev x y /\ wire y j yj ==>
     ?i. i + j + 1 = width x /\ wire x i yj`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [brev_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`y : bus`; `j : num`; `yj : wire`] wire_bound) THEN
  ASM_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] LT_EXISTS; SUC_ADD] THEN
  DISCH_THEN (X_CHOOSE_THEN `i : num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC [ADD1; ADD_ASSOC] THEN
  MP_TAC (SPECL [`x : bus`; `i : num`] wire_exists) THEN
  ANTS_TAC THENL
  [REWRITE_TAC [LT_EXISTS] THEN
   EXISTS_TAC `j : num` THEN
   ASM_REWRITE_TAC [ADD_SUC];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `xi : wire` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM
    (MP_TAC o SPECL [`i : num`; `j : num`; `xi : wire`; `yj : wire`]) THEN
  ASM_REWRITE_TAC [ADD1; ADD_ASSOC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC []);;

export_thm brev_wire_out;;

let brev_bnil = prove
 (`brev bnil bnil`,
  REWRITE_TAC [brev_def; bnil_width; ADD_EQ_0; ONE; NOT_SUC]);;

export_thm brev_bnil;;

let brev_bwire = prove
 (`!w. brev (bwire w) (bwire w)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [brev_def; bwire_wire] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm brev_bwire;;

let brev_bappend = prove
 (`!x1 x2 y1 y2.
     brev x1 y2 /\ brev x2 y1 ==> brev (bappend x1 x2) (bappend y1 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [brev_def; bappend_width] THEN
  REPEAT STRIP_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  ASM_CASES_TAC `i < width x1` THENL
  [MP_TAC
     (SPECL
        [`x1 : bus`; `x2 : bus`; `i : num`; `xi : wire`]
        wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `i + j + 1 = width x1 + width x2` THEN
   POP_ASSUM
     (X_CHOOSE_THEN `d : num` (fun th -> SUBST1_TAC th THEN ASSUME_TAC th) o
      REWRITE_RULE [LT_EXISTS]) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [GSYM ADD1; SUC_ADD; SUC_INJ] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   UNDISCH_TAC `wire (bappend y1 y2) (d + width x2) yj` THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [wire_in_suffix] THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   UNDISCH_THEN
     `!i j xi yj.
        i + j + 1 = width x1 /\ wire x1 i xi /\ wire y2 j yj ==> xi = yj`
     (MATCH_MP_TAC o SPECL [`i : num`; `d : num`]) THEN
   UNDISCH_THEN `width x1 = i + SUC d` SUBST1_TAC THEN
   ASM_REWRITE_TAC [ADD1];
   ALL_TAC] THEN
  UNDISCH_TAC `i + j + 1 = width x1 + width x2` THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     REWRITE_RULE [LE_EXISTS; NOT_LT]) THEN
  REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `wire (bappend x1 x2) (width x1 + d) xi` THEN
  ASM_REWRITE_TAC [wire_in_suffix] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`y1 : bus`; `y2 : bus`; `j : num`; `yj : wire`]
       wire_in_prefix) THEN
  ANTS_TAC THENL
  [REWRITE_TAC [LT_EXISTS] THEN
   EXISTS_TAC `d : num` THEN
   UNDISCH_THEN `width x2 = width y1` (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN `d + j + 1 = width x2` (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [ADD_ASSOC; ADD1; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  UNDISCH_THEN
    `!i j xi yj.
       i + j + 1 = width x2 /\ wire x2 i xi /\ wire y1 j yj ==> xi = yj`
    (MATCH_MP_TAC o SPECL [`d : num`; `j : num`]) THEN
  ASM_REWRITE_TAC []);;

export_thm brev_bappend;;

let brev_bappend_bwire = prove
 (`!w x y. brev (bappend (bwire w) x) (bappend y (bwire w)) <=> brev x y`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC brev_bappend THEN
   ASM_REWRITE_TAC [brev_bwire];
   ALL_TAC] THEN
  REWRITE_TAC [brev_def; bappend_width; bwire_width] THEN
  REWRITE_TAC [SPECL [`1`; `width x`] ADD_SYM] THEN
  REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [ADD_ASSOC] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `1 + i` THEN
  EXISTS_TAC `j : num` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_REWRITE_TAC [wire_suc; GSYM (ONCE_REWRITE_RULE [ADD_SYM] ADD1)] THEN
  MP_TAC
    (SPECL [`y : bus`; `bwire w`; `j : num`; `yj : wire`] wire_in_prefix) THEN
  REVERSE_TAC ANTS_TAC THENL
  [DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
  REWRITE_TAC [ONE; SUC_ADD; LT_SUC_LE; ZERO_ADD; LE_ADDR]);;

export_thm brev_bappend_bwire;;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* Lifting relations between wires *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let blift2_mono = prove
 (`!r s x y. (!xi yi. r xi yi ==> s xi yi) /\ blift2 r x y ==> blift2 s x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_mono;;

let blift2_width = prove
 (`!r x y.
     blift2 r x y ==>
     ?n.
       width x = n /\
       width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_width;;

let blift2_width_out = prove
 (`!r x y n.
     blift2 r x y /\ width x = n ==>
     width y = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`r : wire -> wire -> bool`;
                 `x : bus`;
                 `y : bus`] blift2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_width_out;;

let blift2_bnil = prove
 (`!r. blift2 r bnil bnil`,
  REWRITE_TAC [blift2_def; bnil_width; bnil_wire; EXISTS_REFL']);;

export_thm blift2_bnil;;

let blift2_bwire = prove
 (`!r w x. blift2 r (bwire w) (bwire x) <=> r w x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def; bwire_width; bwire_wire] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [];
   STRIP_TAC THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm blift2_bwire;;

let blift2_bappend = prove
 (`!r x1 x2 y1 y2.
     blift2 r x1 y1 /\ blift2 r x2 y2 ==>
     blift2 r (bappend x1 x2) (bappend y1 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `n1 : num` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `n2 : num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n1 + n2 : num` THEN
  ASM_REWRITE_TAC [bappend_width] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < (n1 : num)` THENL
  [MP_TAC (SPECL [`x1 : bus`;
                  `x2 : bus`;
                  `i : num`;
                  `xi : wire`] wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`y1 : bus`;
                  `y2 : bus`;
                  `i : num`;
                  `yi : wire`] wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC;
   POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   MP_TAC (SPECL [`x1 : bus`;
                  `x2 : bus`;
                  `d : num`;
                  `xi : wire`] wire_in_suffix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`y1 : bus`;
                  `y2 : bus`;
                  `d : num`;
                  `yi : wire`] wire_in_suffix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC]);;

export_thm blift2_bappend;;

let blift2_bsub = prove
 (`!r x y k n xs ys.
     blift2 r x y /\ bsub x k n xs /\ bsub y k n ys ==>
     blift2 r xs ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC)
       STRIP_ASSUME_TAC) THEN
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
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `k + i : num` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `xs : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC bsub_wire_imp THEN
   EXISTS_TAC `n : num` THEN
   EXISTS_TAC `ys : bus` THEN
   ASM_REWRITE_TAC []]);;

export_thm blift2_bsub;;

let blift2_wire = prove
 (`!r x y i xi yi. blift2 r x y /\ wire x i xi /\ wire y i yi ==> r xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_wire;;

let blift2_bappend_bwire = prove
 (`!r xh xt yh yt.
     blift2 r (bappend (bwire xh) xt) (bappend (bwire yh) yt) <=>
     r xh yh /\ blift2 r xt yt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM blift2_bwire] THEN
   MATCH_ACCEPT_TAC blift2_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC blift2_wire THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`r : wire -> wire -> bool`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`]
       blift2_width) THEN
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
  MATCH_MP_TAC blift2_bsub THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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

export_thm blift2_bappend_bwire;;

let blift2_induct = prove
 (`!r p.
     p bnil bnil /\
     (!xh xt yh yt.
        r xh yh /\ blift2 r xt yt /\ p xt yt ==>
        p (bappend (bwire xh) xt) (bappend (bwire yh) yt)) ==>
     !x y. blift2 r x y ==> p x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`r : wire -> wire -> bool`;
                 `x : bus`; `y : bus`] blift2_width) THEN
  ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN
  DISCH_THEN (fun th -> POP_ASSUM MP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC [IMP_IMP; GSYM CONJ_ASSOC] THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; IMP_CONJ] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
         (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
         (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
  REWRITE_TAC [blift2_bappend_bwire] THEN
  STRIP_TAC THEN
  UNDISCH_THEN
    `!xh xt yh yt.
       r xh yh /\ blift2 r xt yt /\ p xt yt ==>
       p (bappend (bwire xh) xt) (bappend (bwire yh) yt)`
    MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_induct;;

let blift2_exists = prove
 (`!r. (!xi. ?yi. r xi yi) ==> !x. ?y. blift2 r x y`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPEC `width x` EXISTS_REFL') THEN
  REWRITE_TAC [GSYM LEFT_FORALL_IMP_THM] THEN
  X_GEN_TAC `n : num` THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `bnil` THEN
   REWRITE_TAC [blift2_bnil];
   GEN_TAC THEN
   REWRITE_TAC [width_suc] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `y : bus`) THEN
   REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `z : bus` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `w : wire`) THEN
   DISCH_THEN (X_CHOOSE_THEN `x : wire` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `bappend (bwire x) z` THEN
   MATCH_MP_TAC blift2_bappend THEN
   ASM_REWRITE_TAC [blift2_bwire]]);;

export_thm blift2_exists;;

let blift2_refl = prove
 (`!r. (!w. r w w) ==> (!x. blift2 r x x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [blift2_def] THEN
  EXISTS_TAC `width x` THEN
  REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`x : bus`; `i : num`; `xi : wire`; `yi : wire`] wire_inj) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_refl;;

let blift2_bground = prove
 (`!r x y.
     blift2 r (bground (width x)) y <=>
     blift2 (\x y. r ground y) x y`,
  REPEAT GEN_TAC THEN
  (REVERSE_TAC o ASM_CASES_TAC) `?n. width x = n /\ width y = n` THENL
  [EQ_TAC THENL
   [DISCH_THEN (X_CHOOSE_THEN `m : num` MP_TAC o MATCH_MP blift2_width) THEN
    ASM_REWRITE_TAC [bground_width] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `~(?n. width x = n /\ width y = n)` THEN
    ASM_REWRITE_TAC [EXISTS_REFL'];
    DISCH_THEN (X_CHOOSE_THEN `m : num` MP_TAC o MATCH_MP blift2_width) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `~(?n. width x = n /\ width y = n)` THEN
    ASM_REWRITE_TAC [EXISTS_REFL']];
   ALL_TAC] THEN
  POP_ASSUM (X_CHOOSE_THEN `n : num` MP_TAC) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [blift2_bnil; bnil_width; bground_zero];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; IMP_CONJ] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC
    [bappend_width; bwire_width; bground_add; bground_one;
     blift2_bappend_bwire; bappend_bwire_inj] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift2_bground;;

let blift3_mono = prove
 (`!r s x y z.
     (!xi yi zi. r xi yi zi ==> s xi yi zi) /\
     blift3 r x y z ==>
     blift3 s x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_mono;;

let blift3_width = prove
 (`!r x y z.
     blift3 r x y z ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_width;;

let blift3_width_out = prove
 (`!r x y z n.
     blift3 r x y z /\ width x = n ==>
     width z = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`r : wire -> wire -> wire -> bool`;
                 `x : bus`;
                 `y : bus`;
                 `z : bus`] blift3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_width_out;;

let blift3_bnil = prove
 (`!r. blift3 r bnil bnil bnil`,
  REWRITE_TAC [blift3_def; bnil_width; bnil_wire; EXISTS_REFL']);;

export_thm blift3_bnil;;

let blift3_bwire = prove
 (`!r w x y. blift3 r (bwire w) (bwire x) (bwire y) <=> r w x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def; bwire_width; bwire_wire] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [];
   STRIP_TAC THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm blift3_bwire;;

let blift3_bappend = prove
 (`!r x1 x2 y1 y2 z1 z2.
     blift3 r x1 y1 z1 /\ blift3 r x2 y2 z2 ==>
     blift3 r (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `n1 : num` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `n2 : num` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `n1 + n2 : num` THEN
  ASM_REWRITE_TAC [bappend_width] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `i < (n1 : num)` THENL
  [MP_TAC (SPECL [`x1 : bus`;
                  `x2 : bus`;
                  `i : num`;
                  `xi : wire`] wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`y1 : bus`;
                  `y2 : bus`;
                  `i : num`;
                  `yi : wire`] wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`z1 : bus`;
                  `z2 : bus`;
                  `i : num`;
                  `zi : wire`] wire_in_prefix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC;
   POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   MP_TAC (SPECL [`x1 : bus`;
                  `x2 : bus`;
                  `d : num`;
                  `xi : wire`] wire_in_suffix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`y1 : bus`;
                  `y2 : bus`;
                  `d : num`;
                  `yi : wire`] wire_in_suffix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`z1 : bus`;
                  `z2 : bus`;
                  `d : num`;
                  `zi : wire`] wire_in_suffix) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_ACCEPT_TAC]);;

export_thm blift3_bappend;;

let blift3_bsub = prove
 (`!r x y z k n xs ys zs.
     blift3 r x y z /\ bsub x k n xs /\ bsub y k n ys /\ bsub z k n zs ==>
     blift3 r xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `m : num` STRIP_ASSUME_TAC)
       STRIP_ASSUME_TAC) THEN
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
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `k + i : num` THEN
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

export_thm blift3_bsub;;

let blift3_wire = prove
 (`!r x y z i xi yi zi.
     blift3 r x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     r xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_wire;;

let blift3_bappend_bwire = prove
 (`!r xh xt yh yt zh zt.
     blift3 r (bappend (bwire xh) xt) (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     r xh yh zh /\ blift3 r xt yt zt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM blift3_bwire] THEN
   MATCH_ACCEPT_TAC blift3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC blift3_wire THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`r : wire -> wire -> wire -> bool`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`]
       blift3_width) THEN
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
  MATCH_MP_TAC blift3_bsub THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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

export_thm blift3_bappend_bwire;;

let blift3_induct = prove
 (`!r p.
     p bnil bnil bnil /\
     (!xh xt yh yt zh zt.
        r xh yh zh /\ blift3 r xt yt zt /\ p xt yt zt ==>
        p (bappend (bwire xh) xt) (bappend (bwire yh) yt)
          (bappend (bwire zh) zt)) ==>
     !x y z. blift3 r x y z ==> p x y z`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`r : wire -> wire -> wire -> bool`;
                 `x : bus`; `y : bus`; `z : bus`] blift3_width) THEN
  ASM_REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
  GEN_TAC THEN
  DISCH_THEN (fun th -> POP_ASSUM MP_TAC THEN MP_TAC th) THEN
  REWRITE_TAC [IMP_IMP; GSYM CONJ_ASSOC] THEN
  SPEC_TAC (`z : bus`, `z : bus`) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; IMP_CONJ] THEN
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
  REWRITE_TAC [blift3_bappend_bwire] THEN
  STRIP_TAC THEN
  UNDISCH_THEN
    `!xh xt yh yt zh zt.
       r xh yh zh /\ blift3 r xt yt zt /\ p xt yt zt ==>
       p (bappend (bwire xh) xt) (bappend (bwire yh) yt)
         (bappend (bwire zh) zt)`
    MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_induct;;

let blift3_exists = prove
 (`!r.
     (!xi yi. ?zi. r xi yi zi) ==>
     !x y. width x = width y ==> ?z. blift3 r x y z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. width x = n /\ width y = n` MP_TAC THENL
  [EXISTS_TAC `width y` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [GSYM LEFT_FORALL_IMP_THM] THEN
  X_GEN_TAC `n : num` THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero; IMP_CONJ] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `bnil` THEN
   REWRITE_TAC [blift3_bnil];
   REPEAT GEN_TAC THEN
   REWRITE_TAC [width_suc; IMP_CONJ] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `xh : wire`
       (X_CHOOSE_THEN `xt : bus`
         (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `yh : wire`
       (X_CHOOSE_THEN `yt : bus`
         (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC))) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`xt : bus`; `yt : bus`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `zt : bus` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`xh : wire`; `yh : wire`]) THEN
   DISCH_THEN (X_CHOOSE_THEN `zh : wire` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   MATCH_MP_TAC blift3_bappend THEN
   ASM_REWRITE_TAC [blift3_bwire]]);;

export_thm blift3_exists;;

let blift3_refl = prove
 (`!r. (!w. r w w w) ==> (!x. blift3 r x x x)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [blift3_def] THEN
  EXISTS_TAC `width x` THEN
  REWRITE_TAC [] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`x : bus`; `i : num`; `xi : wire`; `yi : wire`] wire_inj) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL [`x : bus`; `i : num`; `xi : wire`; `zi : wire`] wire_inj) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_refl;;

let blift3_right_simplify = prove
 (`!s r.
     (!x y z. s x z ==> r x y z) ==>
     !x y z.
       width x = width y /\ blift2 s x z ==>
       blift3 r x y z`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `width x = width y` THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  UNDISCH_TAC `blift2 s x z` THEN
  SPEC_TAC (`z : bus`, `z : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  MATCH_MP_TAC blift2_induct THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   REWRITE_TAC [bnil_width; width_zero] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [blift3_bnil];
   ALL_TAC] THEN
  X_GEN_TAC `xh : wire` THEN
  X_GEN_TAC `xt : bus` THEN
  X_GEN_TAC `zh : wire` THEN
  X_GEN_TAC `zt : bus` THEN
  REWRITE_TAC [bwire_width; bappend_width] THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [GSYM ADD1] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC STRIP_ASSUME_TAC)) o
     REWRITE_RULE [width_suc]) THEN
  REWRITE_TAC [blift3_bappend_bwire] THEN
  CONJ_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_right_simplify;;

let blift3_right_bground = prove
 (`!r x n y.
     blift3 r x (bground n) y <=>
     width x = n /\ blift2 (\x y. r x ground y) x y`,
  REPEAT GEN_TAC THEN
  (REVERSE_TAC o ASM_CASES_TAC) `width x = n /\ width y = n` THENL
  [EQ_TAC THENL
   [DISCH_THEN (X_CHOOSE_THEN `m : num` MP_TAC o MATCH_MP blift3_width) THEN
    ASM_REWRITE_TAC [bground_width] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `~(width x = n /\ width y = n)` THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN
      (CONJUNCTS_THEN2
        STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `m : num` MP_TAC o MATCH_MP blift2_width)) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `~(width x = n /\ width y = n)` THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [blift3_bnil; blift2_bnil; bnil_width; bground_zero];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; IMP_CONJ] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC STRIP_ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST_VAR_TAC STRIP_ASSUME_TAC))) THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] ADD1] THEN
  REWRITE_TAC
    [bappend_width; bwire_width; bground_add; bground_one;
     blift3_bappend_bwire; blift2_bappend_bwire; bappend_bwire_inj] THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`xt : bus`; `yt : bus`]) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC (TAUT `!x y. y ==> (x <=> y /\ x)`) THEN
  EXISTS_TAC `xh : wire` THEN
  EXISTS_TAC `xt : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm blift3_right_bground;;

(* ~~~~~~~~~~~~~~~~~~ *)
(* Lifted bus devices *)
(* ~~~~~~~~~~~~~~~~~~ *)

let bconnect_width = prove
 (`!x y.
     bconnect x y ==>
     ?n.
       width x = n /\
       width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_width);;

export_thm bconnect_width;;

let bconnect_width_out = prove
 (`!x y n.
     bconnect x y /\ width x = n ==>
     width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_width_out);;

export_thm bconnect_width_out;;

let bconnect_bnil = prove
 (`bconnect bnil bnil`,
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_bnil);;

export_thm bconnect_bnil;;

let bconnect_bwire = prove
 (`!x y. bconnect (bwire x) (bwire y) <=> connect x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_bwire);;

export_thm bconnect_bwire;;

let bconnect_bappend = prove
 (`!x1 x2 y1 y2.
     bconnect x1 y1 /\ bconnect x2 y2 ==>
     bconnect (bappend x1 x2) (bappend y1 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend);;

export_thm bconnect_bappend;;

let bconnect_bsub = prove
 (`!x y k n xs ys.
     bconnect x y /\
     bsub x k n xs /\
     bsub y k n ys ==>
     bconnect xs ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_bsub);;

export_thm bconnect_bsub;;

let bconnect_wire = prove
 (`!x y i xi yi. bconnect x y /\ wire x i xi /\ wire y i yi ==> connect xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_wire);;

export_thm bconnect_wire;;

let bconnect_bappend_bwire = prove
 (`!xh xt yh yt.
     bconnect (bappend (bwire xh) xt) (bappend (bwire yh) yt) <=>
     connect xh yh /\ bconnect xt yt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bconnect_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend_bwire);;

export_thm bconnect_bappend_bwire;;

let bconnect_refl = prove
 (`!x. bconnect x x`,
  REWRITE_TAC [bconnect_def] THEN
  MATCH_MP_TAC blift2_refl THEN
  ACCEPT_TAC connect_refl);;

export_thm bconnect_refl;;

let bconnect_exists = prove
 (`!x. ?y. bconnect x y`,
  REWRITE_TAC [bconnect_def] THEN
  MATCH_MP_TAC blift2_exists THEN
  ACCEPT_TAC connect_exists);;

export_thm bconnect_exists;;

let bconnect_bsignal = prove
 (`!x y t. bconnect x y ==> bsignal y t = bsignal x t`,
  REWRITE_TAC [bconnect_def; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC blift2_induct THEN
  REWRITE_TAC [bappend_bwire_bsignal; CONS_11] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC connect_signal THEN
  ASM_REWRITE_TAC []);;

export_thm bconnect_bsignal;;

let bdelay_width = prove
 (`!x y.
     bdelay x y ==>
     ?n.
       width x = n /\
       width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_width);;

export_thm bdelay_width;;

let bdelay_width_out = prove
 (`!x y n.
     bdelay x y /\ width x = n ==>
     width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_width_out);;

export_thm bdelay_width_out;;

let bdelay_bnil = prove
 (`bdelay bnil bnil`,
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_bnil);;

export_thm bdelay_bnil;;

let bdelay_bwire = prove
 (`!x y. bdelay (bwire x) (bwire y) <=> delay x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_bwire);;

export_thm bdelay_bwire;;

let bdelay_bappend = prove
 (`!x1 x2 y1 y2.
     bdelay x1 y1 /\ bdelay x2 y2 ==>
     bdelay (bappend x1 x2) (bappend y1 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend);;

export_thm bdelay_bappend;;

let bdelay_bsub = prove
 (`!x y k n xs ys.
     bdelay x y /\
     bsub x k n xs /\
     bsub y k n ys ==>
     bdelay xs ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_bsub);;

export_thm bdelay_bsub;;

let bdelay_wire = prove
 (`!x y i xi yi. bdelay x y /\ wire x i xi /\ wire y i yi ==> delay xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_wire);;

export_thm bdelay_wire;;

let bdelay_bappend_bwire = prove
 (`!xh xt yh yt.
     bdelay (bappend (bwire xh) xt) (bappend (bwire yh) yt) <=>
     delay xh yh /\ bdelay xt yt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend_bwire);;

export_thm bdelay_bappend_bwire;;

let bdelay_exists = prove
 (`!x. ?y. bdelay x y`,
  REWRITE_TAC [bdelay_def] THEN
  MATCH_MP_TAC blift2_exists THEN
  ACCEPT_TAC delay_exists);;

export_thm bdelay_exists;;

let bdelay_bsignal = prove
 (`!x y t. bdelay x y ==> bsignal y (t + 1) = bsignal x t`,
  REWRITE_TAC [bdelay_def; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC blift2_induct THEN
  REWRITE_TAC [bnil_bsignal; bappend_bwire_bsignal; CONS_11] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC delay_signal THEN
  ASM_REWRITE_TAC []);;

export_thm bdelay_bsignal;;

let bnot_width = prove
 (`!x y.
     bnot x y ==>
     ?n.
       width x = n /\
       width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_width);;

export_thm bnot_width;;

let bnot_width_out = prove
 (`!x y n.
     bnot x y /\ width x = n ==>
     width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_width_out);;

export_thm bnot_width_out;;

let bnot_bnil = prove
 (`bnot bnil bnil`,
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_bnil);;

export_thm bnot_bnil;;

let bnot_bwire = prove
 (`!x y. bnot (bwire x) (bwire y) <=> not x y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_bwire);;

export_thm bnot_bwire;;

let bnot_bappend = prove
 (`!x1 x2 y1 y2.
     bnot x1 y1 /\ bnot x2 y2 ==>
     bnot (bappend x1 x2) (bappend y1 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend);;

export_thm bnot_bappend;;

let bnot_bsub = prove
 (`!x y k n xs ys.
     bnot x y /\
     bsub x k n xs /\
     bsub y k n ys ==>
     bnot xs ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_bsub);;

export_thm bnot_bsub;;

let bnot_wire = prove
 (`!x y i xi yi. bnot x y /\ wire x i xi /\ wire y i yi ==> not xi yi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_wire);;

export_thm bnot_wire;;

let bnot_bappend_bwire = prove
 (`!xh xt yh yt.
     bnot (bappend (bwire xh) xt) (bappend (bwire yh) yt) <=>
     not xh yh /\ bnot xt yt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bnot_def] THEN
  MATCH_ACCEPT_TAC blift2_bappend_bwire);;

export_thm bnot_bappend_bwire;;

let bnot_exists = prove
 (`!x. ?y. bnot x y`,
  REWRITE_TAC [bnot_def] THEN
  MATCH_MP_TAC blift2_exists THEN
  ACCEPT_TAC not_exists);;

export_thm bnot_exists;;

let band2_width = prove
 (`!x y z.
     band2 x y z ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_width);;

export_thm band2_width;;

let band2_width_out = prove
 (`!x y z n.
     band2 x y z /\ width x = n ==>
     width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_width_out);;

export_thm band2_width_out;;

let band2_bnil = prove
 (`band2 bnil bnil bnil`,
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_bnil);;

export_thm band2_bnil;;

let band2_bwire = prove
 (`!x y z. band2 (bwire x) (bwire y) (bwire z) <=> and2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_bwire);;

export_thm band2_bwire;;

let band2_bappend = prove
 (`!x1 x2 y1 y2 z1 z2.
     band2 x1 y1 z1 /\ band2 x2 y2 z2 ==>
     band2 (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend);;

export_thm band2_bappend;;

let band2_bsub = prove
 (`!x y z k n xs ys zs.
     band2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     band2 xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_bsub);;

export_thm band2_bsub;;

let band2_wire = prove
 (`!x y z i xi yi zi.
     band2 x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     and2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_wire);;

export_thm band2_wire;;

let band2_bappend_bwire = prove
 (`!xh xt yh yt zh zt.
     band2 (bappend (bwire xh) xt) (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     and2 xh yh zh /\ band2 xt yt zt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend_bwire);;

export_thm band2_bappend_bwire;;

let band2_exists = prove
 (`!x y. width x = width y ==> ?z. band2 x y z`,
  REWRITE_TAC [band2_def] THEN
  MATCH_MP_TAC blift3_exists THEN
  ACCEPT_TAC and2_exists);;

export_thm band2_exists;;

let band2_right_bground = prove
 (`!x n y.
     width x = n /\ bconnect (bground n) y ==>
     band2 x (bground n) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band2_def; blift3_right_bground; bconnect_def] THEN
  REVERSE_TAC (ASM_CASES_TAC `width x = n`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [blift2_bground] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC blift2_mono THEN
  EXISTS_TAC `\ (x : wire) y. connect ground y` THEN
  ASM_REWRITE_TAC [and2_right_ground]);;

export_thm band2_right_bground;;

let bor2_width = prove
 (`!x y z.
     bor2 x y z ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_width);;

export_thm bor2_width;;

let bor2_width_out = prove
 (`!x y z n.
     bor2 x y z /\ width x = n ==>
     width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_width_out);;

export_thm bor2_width_out;;

let bor2_bnil = prove
 (`bor2 bnil bnil bnil`,
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bnil);;

export_thm bor2_bnil;;

let bor2_bwire = prove
 (`!x y z. bor2 (bwire x) (bwire y) (bwire z) <=> or2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bwire);;

export_thm bor2_bwire;;

let bor2_bappend = prove
 (`!x1 x2 y1 y2 z1 z2.
     bor2 x1 y1 z1 /\ bor2 x2 y2 z2 ==>
     bor2 (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend);;

export_thm bor2_bappend;;

let bor2_bsub = prove
 (`!x y z k n xs ys zs.
     bor2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bor2 xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bsub);;

export_thm bor2_bsub;;

let bor2_wire = prove
 (`!x y z i xi yi zi.
     bor2 x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     or2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_wire);;

export_thm bor2_wire;;

let bor2_bappend_bwire = prove
 (`!xh xt yh yt zh zt.
     bor2 (bappend (bwire xh) xt) (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     or2 xh yh zh /\ bor2 xt yt zt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend_bwire);;

export_thm bor2_bappend_bwire;;

let bor2_exists = prove
 (`!x y. width x = width y ==> ?z. bor2 x y z`,
  REWRITE_TAC [bor2_def] THEN
  MATCH_MP_TAC blift3_exists THEN
  ACCEPT_TAC or2_exists);;

export_thm bor2_exists;;

let bor2_right_bground = prove
 (`!x n y.
     width x = n /\ bconnect x y ==>
     bor2 x (bground n) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor2_def; blift3_right_bground; bconnect_def] THEN
  REVERSE_TAC (ASM_CASES_TAC `width x = n`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC blift2_mono THEN
  EXISTS_TAC `connect` THEN
  ASM_REWRITE_TAC [or2_right_ground]);;

export_thm bor2_right_bground;;

let bxor2_width = prove
 (`!x y z.
     bxor2 x y z ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_width);;

export_thm bxor2_width;;

let bxor2_width_out = prove
 (`!x y z n.
     bxor2 x y z /\ width x = n ==>
     width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_width_out);;

export_thm bxor2_width_out;;

let bxor2_bnil = prove
 (`bxor2 bnil bnil bnil`,
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bnil);;

export_thm bxor2_bnil;;

let bxor2_bwire = prove
 (`!x y z. bxor2 (bwire x) (bwire y) (bwire z) <=> xor2 x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bwire);;

export_thm bxor2_bwire;;

let bxor2_bappend = prove
 (`!x1 x2 y1 y2 z1 z2.
     bxor2 x1 y1 z1 /\ bxor2 x2 y2 z2 ==>
     bxor2 (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend);;

export_thm bxor2_bappend;;

let bxor2_bsub = prove
 (`!x y z k n xs ys zs.
     bxor2 x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bxor2 xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bsub);;

export_thm bxor2_bsub;;

let bxor2_wire = prove
 (`!x y z i xi yi zi.
     bxor2 x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     xor2 xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_wire);;

export_thm bxor2_wire;;

let bxor2_bappend_bwire = prove
 (`!xh xt yh yt zh zt.
     bxor2 (bappend (bwire xh) xt) (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     xor2 xh yh zh /\ bxor2 xt yt zt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend_bwire);;

export_thm bxor2_bappend_bwire;;

let bxor2_exists = prove
 (`!x y. width x = width y ==> ?z. bxor2 x y z`,
  REWRITE_TAC [bxor2_def] THEN
  MATCH_MP_TAC blift3_exists THEN
  ACCEPT_TAC xor2_exists);;

export_thm bxor2_exists;;

let bxor2_right_bground = prove
 (`!x n y.
     width x = n /\ bconnect x y ==>
     bxor2 x (bground n) y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor2_def; blift3_right_bground; bconnect_def] THEN
  REVERSE_TAC (ASM_CASES_TAC `width x = n`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC blift2_mono THEN
  EXISTS_TAC `connect` THEN
  ASM_REWRITE_TAC [xor2_right_ground]);;

export_thm bxor2_right_bground;;

let bcase1_width = prove
 (`!s x y z.
     bcase1 s x y z ==>
     ?n.
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_width);;

export_thm bcase1_width;;

let bcase1_width_out = prove
 (`!s x y z n.
     bcase1 s x y z /\ width x = n ==>
     width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_width_out);;

export_thm bcase1_width_out;;

let bcase1_bnil = prove
 (`!s. bcase1 s bnil bnil bnil`,
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_bnil);;

export_thm bcase1_bnil;;

let bcase1_bwire = prove
 (`!s x y z. bcase1 s (bwire x) (bwire y) (bwire z) <=> case1 s x y z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_bwire);;

export_thm bcase1_bwire;;

let bcase1_bappend = prove
 (`!s x1 x2 y1 y2 z1 z2.
     bcase1 s x1 y1 z1 /\ bcase1 s x2 y2 z2 ==>
     bcase1 s (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend);;

export_thm bcase1_bappend;;

let bcase1_bsub = prove
 (`!s x y z k n xs ys zs.
     bcase1 s x y z /\
     bsub x k n xs /\
     bsub y k n ys /\
     bsub z k n zs ==>
     bcase1 s xs ys zs`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_bsub);;

export_thm bcase1_bsub;;

let bcase1_wire = prove
 (`!s x y z i xi yi zi.
     bcase1 s x y z /\ wire x i xi /\ wire y i yi /\ wire z i zi ==>
     case1 s xi yi zi`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_wire);;

export_thm bcase1_wire;;

let bcase1_bappend_bwire = prove
 (`!s xh xt yh yt zh zt.
     bcase1
       s
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     case1 s xh yh zh /\ bcase1 s xt yt zt`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_ACCEPT_TAC blift3_bappend_bwire);;

export_thm bcase1_bappend_bwire;;

let bcase1_exists = prove
 (`!s x y. width x = width y ==> ?z. bcase1 s x y z`,
  GEN_TAC THEN
  REWRITE_TAC [bcase1_def] THEN
  MATCH_MP_TAC blift3_exists THEN
  MATCH_ACCEPT_TAC case1_exists);;

export_thm bcase1_exists;;

let bcase1_bsignal = prove
 (`!s x y z t.
      bcase1 s x y z ==>
      bsignal z t = (if signal s t then bsignal x t else bsignal y t)`,
  GEN_TAC THEN
  REWRITE_TAC [bcase1_def; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC blift3_induct THEN
  CONJ_TAC THENL
  [GEN_TAC THEN
   COND_CASES_TAC THEN
   REFL_TAC;
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bappend_bwire_bsignal] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `CONS
       (if signal s t then signal xh t else signal yh t)
       (if signal s t then bsignal xt t else bsignal yt t)` THEN
  ASM_REWRITE_TAC [CONS_11] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC case1_signal THEN
   ASM_REWRITE_TAC [];
   COND_CASES_TAC THEN
   REWRITE_TAC []]);;

export_thm bcase1_bsignal;;

(* ~~~~~~~~~~~~~~~~~~~ *)
(* Derived bus devices *)
(* ~~~~~~~~~~~~~~~~~~~ *)

let band3_width = prove
 (`!w x y z.
     band3 w x y z ==>
     ?n.
       width w = n /\
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] band2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`; `z : bus`] band2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm band3_width;;

let band3_width_out = prove
 (`!w x y z n.
     band3 w x y z /\ width w = n ==>
     width z = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `y : bus`; `z : bus`] band3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm band3_width_out;;

let band3_bnil = prove
 (`band3 bnil bnil bnil bnil`,
  REWRITE_TAC [band3_def] THEN
  EXISTS_TAC `bnil` THEN
  REWRITE_TAC [band2_bnil]);;

export_thm band3_bnil;;

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
   [MATCH_MP_TAC band2_width_out THEN
    EXISTS_TAC `bwire w` THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM band2_bwire]);;

export_thm band3_bwire;;

let band3_bappend = prove
 (`!w1 w2 x1 x2 y1 y2 z1 z2.
     band3 w1 x1 y1 z1 /\ band3 w2 x2 y2 z2 ==>
     band3 (bappend w1 w2) (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [band3_def] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx1 : bus` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `wx2 : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `bappend wx1 wx2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC band2_bappend THEN
  ASM_REWRITE_TAC []);;

export_thm band3_bappend;;

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
  [MP_TAC
     (SPECL
        [`w : bus`; `x : bus`; `wx : bus`; `width w`]
        band2_width_out) THEN
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

let band3_bappend_bwire = prove
 (`!wh wt xh xt yh yt zh zt.
     band3
       (bappend (bwire wh) wt)
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     and3 wh xh yh zh /\ band3 wt xt yt zt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM band3_bwire] THEN
   MATCH_ACCEPT_TAC band3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band3_wire THEN
   EXISTS_TAC `bappend (bwire wh) wt` THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire wh) wt`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`]
       band3_width) THEN
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
  MATCH_MP_TAC band3_bsub THEN
  EXISTS_TAC `bappend (bwire wh) wt` THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire wh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm band3_bappend_bwire;;

let band3_exists = prove
 (`!w x y. width w = width x /\ width w = width y ==> ?z. band3 w x y z`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [band3_def] THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`] band2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`] band2_exists) THEN
  SUBGOAL_THEN `width wx = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `z : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `wx : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm band3_exists;;

let bor3_width = prove
 (`!w x y z.
     bor3 w x y z ==>
     ?n.
       width w = n /\
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] bor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`; `z : bus`] bor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bor3_width;;

let bor3_width_out = prove
 (`!w x y z n.
     bor3 w x y z /\ width w = n ==>
     width z = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `y : bus`; `z : bus`] bor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bor3_width_out;;

let bor3_bnil = prove
 (`bor3 bnil bnil bnil bnil`,
  REWRITE_TAC [bor3_def] THEN
  EXISTS_TAC `bnil` THEN
  REWRITE_TAC [bor2_bnil]);;

export_thm bor3_bnil;;

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
   [MATCH_MP_TAC bor2_width_out THEN
    EXISTS_TAC `bwire w` THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM bor2_bwire]);;

export_thm bor3_bwire;;

let bor3_bappend = prove
 (`!w1 w2 x1 x2 y1 y2 z1 z2.
     bor3 w1 x1 y1 z1 /\ bor3 w2 x2 y2 z2 ==>
     bor3 (bappend w1 w2) (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx1 : bus` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `wx2 : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `bappend wx1 wx2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC bor2_bappend THEN
  ASM_REWRITE_TAC []);;

export_thm bor3_bappend;;

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
  [MP_TAC
     (SPECL
        [`w : bus`; `x : bus`; `wx : bus`; `width w`]
        bor2_width_out) THEN
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

let bor3_bappend_bwire = prove
 (`!wh wt xh xt yh yt zh zt.
     bor3
       (bappend (bwire wh) wt)
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     or3 wh xh yh zh /\ bor3 wt xt yt zt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM bor3_bwire] THEN
   MATCH_ACCEPT_TAC bor3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor3_wire THEN
   EXISTS_TAC `bappend (bwire wh) wt` THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire wh) wt`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`]
       bor3_width) THEN
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
  MATCH_MP_TAC bor3_bsub THEN
  EXISTS_TAC `bappend (bwire wh) wt` THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire wh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm bor3_bappend_bwire;;

let bor3_exists = prove
 (`!w x y. width w = width x /\ width w = width y ==> ?z. bor3 w x y z`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`] bor2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`] bor2_exists) THEN
  SUBGOAL_THEN `width wx = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bor2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `z : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `wx : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm bor3_exists;;

let bor3_right_bground = prove
 (`!x y n z.
     width x = n /\ bor2 x y z ==>
     bor3 x y (bground n) z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bor3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : bus` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC bor2_right_bground THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bor2_width_out THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_ACCEPT_TAC bconnect_refl]);;

export_thm bor3_right_bground;;

let bxor3_width = prove
 (`!w x y z.
     bxor3 w x y z ==>
     ?n.
       width w = n /\
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `wx : bus`] bxor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`; `z : bus`] bxor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bxor3_width;;

let bxor3_width_out = prove
 (`!w x y z n.
     bxor3 w x y z /\ width w = n ==>
     width z = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`; `y : bus`; `z : bus`] bxor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bxor3_width_out;;

let bxor3_bnil = prove
 (`bxor3 bnil bnil bnil bnil`,
  REWRITE_TAC [bxor3_def] THEN
  EXISTS_TAC `bnil` THEN
  REWRITE_TAC [bxor2_bnil]);;

export_thm bxor3_bnil;;

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
   [MATCH_MP_TAC bxor2_width_out THEN
    EXISTS_TAC `bwire w` THEN
    EXISTS_TAC `bwire x` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [bwire_width]];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  ASM_REWRITE_TAC [GSYM bxor2_bwire]);;

export_thm bxor3_bwire;;

let bxor3_bappend = prove
 (`!w1 w2 x1 x2 y1 y2 z1 z2.
     bxor3 w1 x1 y1 z1 /\ bxor3 w2 x2 y2 z2 ==>
     bxor3 (bappend w1 w2) (bappend x1 x2) (bappend y1 y2) (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx1 : bus` STRIP_ASSUME_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `wx2 : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `bappend wx1 wx2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC bxor2_bappend THEN
  ASM_REWRITE_TAC []);;

export_thm bxor3_bappend;;

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
  [MP_TAC
     (SPECL
        [`w : bus`; `x : bus`; `wx : bus`; `width w`]
        bxor2_width_out) THEN
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

let bxor3_bappend_bwire = prove
 (`!wh wt xh xt yh yt zh zt.
     bxor3
       (bappend (bwire wh) wt)
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     xor3 wh xh yh zh /\ bxor3 wt xt yt zt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM bxor3_bwire] THEN
   MATCH_ACCEPT_TAC bxor3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor3_wire THEN
   EXISTS_TAC `bappend (bwire wh) wt` THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire wh) wt`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`]
       bxor3_width) THEN
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
  MATCH_MP_TAC bxor3_bsub THEN
  EXISTS_TAC `bappend (bwire wh) wt` THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire wh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm bxor3_bappend_bwire;;

let bxor3_exists = prove
 (`!w x y. width w = width x /\ width w = width y ==> ?z. bxor3 w x y z`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`] bxor2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`wx : bus`; `y : bus`] bxor2_exists) THEN
  SUBGOAL_THEN `width wx = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bxor2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `z : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `wx : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm bxor3_exists;;

let bxor3_right_bground = prove
 (`!x y n z.
     width x = n /\ bxor2 x y z ==>
     bxor3 x y (bground n) z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bxor3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z : bus` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC bxor2_right_bground THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bxor2_width_out THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   MATCH_ACCEPT_TAC bconnect_refl]);;

export_thm bxor3_right_bground;;

let bmajority3_width = prove
 (`!w x y z.
     bmajority3 w x y z ==>
     ?n.
       width w = n /\
       width x = n /\
       width y = n /\
       width z = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`wx : bus`; `wy : bus`; `xy : bus`; `z : bus`] bor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  CONJ_TAC THENL
  [POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `w : bus`;
   POP_ASSUM SUBST_VAR_TAC THEN
   MP_TAC (SPECL [`x : bus`; `y : bus`; `xy : bus`] band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bmajority3_width;;

let bmajority3_width_out = prove
 (`!w x y z n.
     bmajority3 w x y z /\ width w = n ==>
     width z = n`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC
    (SPECL
       [`w : bus`; `x : bus`; `y : bus`; `z : bus`]
       bmajority3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bmajority3_width_out;;

let bmajority3_bnil = prove
 (`bmajority3 bnil bnil bnil bnil`,
  REWRITE_TAC [bmajority3_def] THEN
  EXISTS_TAC `bnil` THEN
  EXISTS_TAC `bnil` THEN
  EXISTS_TAC `bnil` THEN
  REWRITE_TAC [band2_bnil; bor3_bnil]);;

export_thm bmajority3_bnil;;

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
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `bwire w` THEN
   EXISTS_TAC `bwire x` THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN `width bwy = 1`
    (X_CHOOSE_THEN `wy : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `bwire w` THEN
   EXISTS_TAC `bwire y` THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN `width bxy = 1`
    (X_CHOOSE_THEN `xy : wire` SUBST_VAR_TAC o
     REWRITE_RULE [width_one]) THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `bwire x` THEN
   EXISTS_TAC `bwire y` THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  EXISTS_TAC `wx : wire` THEN
  EXISTS_TAC `wy : wire` THEN
  EXISTS_TAC `xy : wire` THEN
  ASM_REWRITE_TAC [GSYM band2_bwire; GSYM bor3_bwire]);;

export_thm bmajority3_bwire;;

let bmajority3_bappend = prove
 (`!w1 w2 x1 x2 y1 y2 z1 z2.
     bmajority3 w1 x1 y1 z1 /\ bmajority3 w2 x2 y2 z2 ==>
     bmajority3
       (bappend w1 w2)
       (bappend x1 x2)
       (bappend y1 y2)
       (bappend z1 z2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  ONCE_REWRITE_TAC [GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `wx1 : bus`
      (X_CHOOSE_THEN `wy1 : bus`
        (X_CHOOSE_THEN `xy1 : bus`
          STRIP_ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `wx2 : bus`
      (X_CHOOSE_THEN `wy2 : bus`
        (X_CHOOSE_THEN `xy2 : bus`
          STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `bappend wx1 wx2` THEN
  EXISTS_TAC `bappend wy1 wy2` THEN
  EXISTS_TAC `bappend xy1 xy2` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_bappend THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC bor3_bappend THEN
  ASM_REWRITE_TAC []);;

export_thm bmajority3_bappend;;

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
  [MP_TAC
     (SPECL
        [`w : bus`; `x : bus`; `wx : bus`; `width w`]
        band2_width_out) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wxs : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`wy : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC
     (SPECL
        [`w : bus`; `y : bus`; `wy : bus`; `width w`]
        band2_width_out) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC bsub_bound THEN
   EXISTS_TAC `ws : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `wys : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`xy : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ANTS_TAC THENL
  [MP_TAC
     (SPECL
        [`x : bus`; `y : bus`; `xy : bus`; `width x`]
        band2_width_out) THEN
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

let bmajority3_bappend_bwire = prove
 (`!wh wt xh xt yh yt zh zt.
     bmajority3
       (bappend (bwire wh) wt)
       (bappend (bwire xh) xt)
       (bappend (bwire yh) yt)
       (bappend (bwire zh) zt) <=>
     majority3 wh xh yh zh /\ bmajority3 wt xt yt zt`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [REWRITE_TAC [GSYM bmajority3_bwire] THEN
   MATCH_ACCEPT_TAC bmajority3_bappend;
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bmajority3_wire THEN
   EXISTS_TAC `bappend (bwire wh) wt` THEN
   EXISTS_TAC `bappend (bwire xh) xt` THEN
   EXISTS_TAC `bappend (bwire yh) yt` THEN
   EXISTS_TAC `bappend (bwire zh) zt` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`bappend (bwire wh) wt`;
        `bappend (bwire xh) xt`;
        `bappend (bwire yh) yt`;
        `bappend (bwire zh) zt`]
       bmajority3_width) THEN
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
  MATCH_MP_TAC bmajority3_bsub THEN
  EXISTS_TAC `bappend (bwire wh) wt` THEN
  EXISTS_TAC `bappend (bwire xh) xt` THEN
  EXISTS_TAC `bappend (bwire yh) yt` THEN
  EXISTS_TAC `bappend (bwire zh) zt` THEN
  EXISTS_TAC `1` THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [CONJ_ASSOC] THEN
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
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width (bwire xh) = 1` (SUBST1_TAC o SYM) THENL
   [REWRITE_TAC [bwire_width];
    REWRITE_TAC [bsub_suffix]];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `width (bwire wh) = 1` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [bwire_width];
   REWRITE_TAC [bsub_suffix]]);;

export_thm bmajority3_bappend_bwire;;

let bmajority3_exists = prove
 (`!w x y. width w = width x /\ width w = width y ==> ?z. bmajority3 w x y z`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  MP_TAC (SPECL [`w : bus`; `x : bus`] band2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `wx : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`w : bus`; `y : bus`] band2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `wy : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`] band2_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `xy : bus` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `width wx = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `x : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width wy = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `w : bus` THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width xy = width w` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC band2_width_out THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `y : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPECL [`wx : bus`; `wy : bus`; `xy : bus`] bor3_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `z : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `wx : bus` THEN
  EXISTS_TAC `wy : bus` THEN
  EXISTS_TAC `xy : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm bmajority3_exists;;

let bmajority3_right_bground = prove
 (`!x y n z.
     width x = n /\ band2 x y z ==>
     bmajority3 x y (bground n) z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmajority3_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `width y = n /\ width z = n` STRIP_ASSUME_TAC THENL
  [MP_TAC
     (SPECL
        [`x : bus`; `y : bus`; `z : bus`]
        band2_width) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  EXISTS_TAC `z : bus` THEN
  EXISTS_TAC `bground n` THEN
  EXISTS_TAC `bground n` THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_right_bground THEN
   ASM_REWRITE_TAC [bconnect_refl];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC band2_right_bground THEN
   ASM_REWRITE_TAC [bconnect_refl];
   ALL_TAC] THEN
  MATCH_MP_TAC bor3_right_bground THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC bor2_right_bground THEN
  ASM_REWRITE_TAC [bconnect_refl]);;

export_thm bmajority3_right_bground;;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-bus-tools.ml";;

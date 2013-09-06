(* ========================================================================= *)
(* PROPERTIES OF THE HARDWARE MODEL                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

logfile "hardware-thm";;

(* ------------------------------------------------------------------------- *)
(* Cycles are the primitive time steps.                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Wires are streams of signals.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Wires generate signals at each cycle.                                     *)
(* ------------------------------------------------------------------------- *)

let mk_wire_signal = prove
 (`!s t. signal (mk_wire s) t = snth s t`,
  REWRITE_TAC [signal_def; wire_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Power and ground wires.                                                   *)
(* ------------------------------------------------------------------------- *)

let ground_signal = prove
 (`!t. ~signal ground t`,
  REWRITE_TAC [ground_def; mk_wire_signal; snth_sreplicate]);;

export_thm ground_signal;;

let power_signal = prove
 (`!t. signal power t`,
  REWRITE_TAC [power_def; mk_wire_signal; snth_sreplicate]);;

export_thm power_signal;;

let bit_to_num_ground = prove
  (`!t. bit_to_num (signal ground t) = 0`,
   REWRITE_TAC [ground_signal; bit_to_num_false]);;

export_thm bit_to_num_ground;;

let bit_to_num_power = prove
  (`!t. bit_to_num (signal power t) = 1`,
   REWRITE_TAC [power_signal; bit_to_num_true]);;

export_thm bit_to_num_power;;

(* ------------------------------------------------------------------------- *)
(* Buses are lists of wires.                                                 *)
(* ------------------------------------------------------------------------- *)

let dest_bus_inj_imp = prove
 (`!x y. dest_bus x = dest_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

let dest_bus_inj = prove
 (`!x y. dest_bus x = dest_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC dest_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

let mk_bus_inj_imp = prove
 (`!x y. mk_bus x = mk_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

let mk_bus_inj = prove
 (`!x y. mk_bus x = mk_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC mk_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bus constructors.                                                         *)
(* ------------------------------------------------------------------------- *)

let bwire_inj_imp = prove
 (`!w1 w2. bwire w1 = bwire w2 ==> w1 = w2`,
  REWRITE_TAC [bwire_def; mk_bus_inj; CONS_11]);;

export_thm bwire_inj_imp;;

let bwire_inj = prove
 (`!w1 w2. bwire w1 = bwire w2 <=> w1 = w2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC bwire_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

export_thm bwire_inj;;

let bappend_bnil = prove
 (`!x. bappend x bnil = x`,
  REWRITE_TAC [bappend_def; bnil_def; bus_tybij; APPEND_NIL]);;

export_thm bappend_bnil;;

let bnil_bappend = prove
 (`!x. bappend bnil x = x`,
  REWRITE_TAC [bappend_def; bnil_def; bus_tybij; NIL_APPEND]);;

export_thm bnil_bappend;;

let bappend_assoc = prove
 (`!x y z. bappend (bappend x y) z = bappend x (bappend y z)`,
  REWRITE_TAC [bappend_def; bus_tybij; APPEND_ASSOC]);;

export_thm bappend_assoc;;

(* ------------------------------------------------------------------------- *)
(* Bus widths.                                                               *)
(* ------------------------------------------------------------------------- *)

let bnil_width = prove
 (`width bnil = 0`,
  REWRITE_TAC [width_def; bnil_def; bus_tybij; LENGTH_NIL]);;

export_thm bnil_width;;

let bwire_width = prove
 (`!w. width (bwire w) = 1`,
  REWRITE_TAC [width_def; bwire_def; bus_tybij; LENGTH_CONS; LENGTH_NIL; ONE]);;

export_thm bwire_width;;

let bappend_width = prove
 (`!x y. width (bappend x y) = width x + width y`,
  REWRITE_TAC [width_def; bappend_def; bus_tybij; LENGTH_APPEND]);;

export_thm bappend_width;;

let width_zero = prove
 (`!x. width x = 0 <=> x = bnil`,
  GEN_TAC THEN
  REWRITE_TAC [width_def; LENGTH_EQ_NIL] THEN
  ONCE_REWRITE_TAC [GSYM dest_bus_inj] THEN
  REWRITE_TAC [bnil_def; bus_tybij]);;

export_thm width_zero;;

let width_suc = prove
 (`!n x.
     width x = SUC n <=>
     ?w y. x = bappend (bwire w) y /\ width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [width_def; LENGTH_EQ_CONS; bappend_def; bwire_def; APPEND_SING;
     bus_tybij] THEN
  MATCH_MP_TAC EQ_SYM THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `dest_bus y` THEN
   ASM_REWRITE_TAC [bus_tybij];
   STRIP_TAC THEN
   EXISTS_TAC `mk_bus t` THEN
   ASM_REWRITE_TAC [bus_tybij] THEN
   MATCH_MP_TAC dest_bus_inj_imp THEN
   ASM_REWRITE_TAC [bus_tybij]]);;

export_thm width_suc;;

let width_one = prove
 (`!x. width x = 1 <=> ?w. x = bwire w`,
  GEN_TAC THEN
  REWRITE_TAC [ONE; width_suc; width_zero] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [bappend_bnil];
   STRIP_TAC THEN
   EXISTS_TAC `bnil` THEN
   ASM_REWRITE_TAC [bappend_bnil]]);;

export_thm width_one;;

(* ------------------------------------------------------------------------- *)
(* Buses generate signal lists at each cycle.                                *)
(* ------------------------------------------------------------------------- *)

let length_bsignal = prove
 (`!x t. LENGTH (bsignal x t) = width x`,
  REWRITE_TAC [bsignal_def; bus_tybij; width_def; LENGTH_MAP]);;

export_thm length_bsignal;;

let bsignal_bnil = prove
 (`!t. bsignal bnil t = []`,
  REWRITE_TAC [bsignal_def; bnil_def; bus_tybij; MAP]);;

export_thm bsignal_bnil;;

let bsignal_bwire = prove
 (`!w t. bsignal (bwire w) t = [signal w t]`,
  REWRITE_TAC [bsignal_def; bwire_def; bus_tybij; MAP]);;

export_thm bsignal_bwire;;

let bsignal_bappend = prove
 (`!x y t.
     bsignal (bappend x y) t =
     APPEND (bsignal x t) (bsignal y t)`,
  REWRITE_TAC [bsignal_def; bus_tybij; bappend_def; APPEND; MAP_APPEND]);;

export_thm bsignal_bappend;;

let bsignal_bappend_bwire = prove
 (`!w x t. bsignal (bappend (bwire w) x) t = CONS (signal w t) (bsignal x t)`,
  REWRITE_TAC [bsignal_bappend; bsignal_bwire; APPEND_SING]);;

export_thm bsignal_bappend_bwire;;

let bits_to_num_bsignal_append = prove
 (`!x y t.
     bits_to_num (bsignal (bappend x y) t) =
     bits_to_num (bsignal x t) +
     bit_shl (bits_to_num (bsignal y t)) (width x)`,
  REWRITE_TAC [bsignal_bappend; bits_to_num_append; length_bsignal]);;

export_thm bits_to_num_bsignal_append;;

(* ------------------------------------------------------------------------- *)
(* Sub-buses.                                                                *)
(* ------------------------------------------------------------------------- *)

let bsub_inj = prove
  (`!x k n y z.
      bsub x k n y /\ bsub x k n z ==>
      y = z`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bsub_def] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm bsub_inj;;

let bsub_exists = prove
  (`!x k n. k + n <= width x ==> ?y. bsub x k n y`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [bsub_def] THEN
   EXISTS_TAC `mk_bus (take n (drop k (dest_bus x)))` THEN
   REFL_TAC);;

export_thm bsub_exists;;

let bsub_bound = prove
  (`!x k n y. bsub x k n y ==> k + n <= width x`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bsub_def] THEN
   STRIP_TAC);;

export_thm bsub_bound;;

let bsub_width = prove
  (`!x k n y. bsub x k n y ==> width y = n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bsub_def; width_def] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [bus_tybij] THEN
   MATCH_MP_TAC length_take THEN
   SUBGOAL_THEN `k + n <= k + LENGTH (drop k (dest_bus x))`
     (fun th -> MP_TAC th THEN REWRITE_TAC [LE_ADD_LCANCEL]) THEN
   MP_TAC (ISPECL [`k : num`; `dest_bus x`] length_drop_add) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `k + n : num` THEN
    ASM_REWRITE_TAC [LE_ADD];
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm bsub_width;;

let bsub_all = prove
  (`!x y. bsub x 0 (width x) y <=> y = x`,
   REWRITE_TAC
     [bsub_def; width_def; ZERO_ADD; LE_REFL; drop_zero; take_length;
      bus_tybij]);;

export_thm bsub_all;;

let bsub_zero = prove
  (`!x y k. bsub x k 0 y <=> k <= width x /\ y = bnil`,
   REWRITE_TAC [bsub_def; ADD_0; take_zero; bnil_def]);;

export_thm bsub_zero;;

let bsub_add = prove
  (`!x y z k m n.
      bsub x k m y /\ bsub x (k + m) n z ==>
      bsub x k (m + n) (bappend y z)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bsub_def; GSYM ADD_ASSOC; width_def] THEN
   SPEC_TAC (`dest_bus x`, `l : wire list`) THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   ASM_REWRITE_TAC [bappend_def; bus_tybij; mk_bus_inj] THEN
   MP_TAC
     (ISPECL [`m : num`; `n : num`; `drop k l : wire list`] take_add) THEN
   ANTS_TAC THENL
   [SUBGOAL_THEN `k + m + n <= k + LENGTH (drop k l : wire list)`
      (fun th ->
        MP_TAC th THEN
        REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL]) THEN
    MP_TAC (ISPECL [`k : num`; `l : wire list`] length_drop_add) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `k + m : num` THEN
     ASM_REWRITE_TAC [LE_ADD];
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC []];
    DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC drop_add THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    ASM_REWRITE_TAC []]);;

export_thm bsub_add;;

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

let bsub_prefix = prove
 (`!x y z. bsub (bappend x y) 0 (width x) z <=> z = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bsub_def; bappend_width; ZERO_ADD; LE_ADD; drop_zero] THEN
  REWRITE_TAC [bappend_def; width_def; bus_tybij; take_append]);;

export_thm bsub_prefix;;

let bsub_skip_prefix = prove
 (`!x y k n z. bsub (bappend x y) (width x + k) n z <=> bsub y k n z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bsub_def; bappend_width; LE_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  REWRITE_TAC [bappend_def; width_def; bus_tybij] THEN
  REVERSE_TAC (ASM_CASES_TAC `k + n <= LENGTH (dest_bus y)`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  MP_TAC (ISPECL [`k : num`;
                  `LENGTH (dest_bus x)`;
                  `APPEND (dest_bus x) (dest_bus y)`] drop_add) THEN
  ANTS_TAC THENL
  [ONCE_REWRITE_TAC [ADD_SYM] THEN
   REWRITE_TAC [LENGTH_APPEND; LE_ADD_LCANCEL] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k + n : num` THEN
   ASM_REWRITE_TAC [LE_ADD];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [drop_append]);;

export_thm bsub_skip_prefix;;

let bsub_suffix = prove
 (`!x y z. bsub (bappend x y) (width x) (width y) z <=> z = y`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `0`; `width y`; `z : bus`]
                bsub_skip_prefix) THEN
  REWRITE_TAC [ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bsub_all]);;

export_thm bsub_suffix;;

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
+  REWRITE_TAC [bwire_width; bwire_inj]);;

export_thm wire_zero;;

(***
let wire_suc = prove
 (`!w x i v. wire (bappend (bwire w) x) (SUC i) v <=> wire x i v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def]
; bsub_def; bus_tybij; width_def] THEN
  REWRITE_TAC [SUC_ADD; LENGTH_CONS; LE_SUC] THEN
  REWRITE_TAC [GSYM ADD1; LE_SUC_LT] THEN
  SPEC_TAC (`dest_bus b`, `l : wire list`) THEN
  GEN_TAC THEN
  ASM_CASES_TAC `i < LENGTH (l : wire list)` THENL
  [AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC drop_suc THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   FIRST_X_ASSUM ACCEPT_TAC;
   ASM_REWRITE_TAC []]);;

export_thm wire_suc;;
***)

(***
let bits_to_num_bsignal_wire = prove
 (`!x i w t.
     wire b i w /\ signal w t ==>
     2 EXP i <= bits_to_num (bsignal b t)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`i : num`, `i : num`) THEN
  INDUCT_TAC THENL
  [GEN_TAC THEN
   MP_TAC (SPEC `width x` num_CASES) THEN
   STRIP_TAC THENL
   [STRIP_TAC THEN
    MP_TAC (SPECL [`x : bus`; `0`; `w : wire`] wire_width) THEN
    ASM_REWRITE_TAC [LT_REFL];
    POP_ASSUM (MP_TAC o REWRITE_RULE [width_suc]) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `h : wire`
        (X_CHOOSE_THEN `c : bus`
          (SUBST_VAR_TAC o CONJUNCT1))) THEN
    REWRITE_TAC [wire_zero] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
    ASM_REWRITE_TAC
      [EXP_0; bsignal_cons; bits_to_num_cons; bit_cons_def;
       bit_to_num_true; LE_ADD]];
   ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC (SPEC `width x` num_CASES) THEN
  STRIP_TAC THENL
  [STRIP_TAC THEN
   MP_TAC (SPECL [`x : bus`; `SUC i`; `w : wire`] wire_width) THEN
   ASM_REWRITE_TAC [LT_ZERO];
   POP_ASSUM (MP_TAC o REWRITE_RULE [width_suc]) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `h : wire`
       (X_CHOOSE_THEN `c : bus`
         (SUBST_VAR_TAC o CONJUNCT1))) THEN
   REWRITE_TAC [wire_suc] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [EXP_SUC; bsignal_cons; bits_to_num_cons; bus_tybij] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `bit_cons (signal h t) (2 EXP i)` THEN
   STRIP_TAC THENL
   [REWRITE_TAC [bit_cons_def; LE_ADDR];
    REWRITE_TAC [bit_cons_def; bit_cons_le_lcancel] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]]);;

export_thm bits_to_num_bsignal_wire;;

(* ------------------------------------------------------------------------- *)
(* Power and ground buses.                                                   *)
(* ------------------------------------------------------------------------- *)

***)

logfile_end ();;

(* ========================================================================= *)
(* PROPERTIES OF THE HARDWARE MODEL                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "hardware-thm";;

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

export_thm mk_wire_signal;;

let signal_eq_imp = prove
 (`!w1 w2. (!t. signal w1 t = signal w2 t) ==> w1 = w2`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM wire_tybij] THEN
  REWRITE_TAC [mk_wire_signal; snth_eq] THEN
  DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

export_thm signal_eq_imp;;

let signal_eq = prove
 (`!w1 w2. (!t. signal w1 t = signal w2 t) <=> w1 = w2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC signal_eq_imp;
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC []]);;

export_thm signal_eq;;

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

let bappend_bwire_inj = prove
 (`!w1 w2 x1 x2.
     bappend (bwire w1) x1 = bappend (bwire w2) x2 <=>
     w1 = w2 /\ x1 = x2`,
  REWRITE_TAC
    [bappend_def; bwire_def; bus_tybij; APPEND_SING; mk_bus_inj;
     CONS_11; dest_bus_inj]);;

export_thm bappend_bwire_inj;;

(* ------------------------------------------------------------------------- *)
(* Bus widths.                                                               *)
(* ------------------------------------------------------------------------- *)

let bnil_width = prove
 (`width bnil = 0`,
  REWRITE_TAC [width_def; bnil_def; bus_tybij; LENGTH_NIL]);;

export_thm bnil_width;;

let bwire_width = prove
 (`!w. width (bwire w) = 1`,
  REWRITE_TAC
    [width_def; bwire_def; bus_tybij; LENGTH_CONS; LENGTH_NIL; ONE]);;

export_thm bwire_width;;

let bappend_width = prove
 (`!x y. width (bappend x y) = width x + width y`,
  REWRITE_TAC [width_def; bappend_def; bus_tybij; LENGTH_APPEND]);;

export_thm bappend_width;;

let bappend_bwire_width = prove
 (`!w x. width (bappend (bwire w) x) = SUC (width x)`,
  REWRITE_TAC [bappend_width; bwire_width; ONCE_REWRITE_RULE [ADD_SYM] ADD1]);;

export_thm bappend_bwire_width;;

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

let bnil_bsignal = prove
 (`!t. bsignal bnil t = []`,
  REWRITE_TAC [bsignal_def; bnil_def; bus_tybij; MAP]);;

export_thm bnil_bsignal;;

let bnil_bits_to_num = prove
 (`!t. bits_to_num (bsignal bnil t) = 0`,
  REWRITE_TAC [bnil_bsignal; bits_to_num_nil]);;

export_thm bnil_bits_to_num;;

let bwire_bsignal = prove
 (`!w t. bsignal (bwire w) t = [signal w t]`,
  REWRITE_TAC [bsignal_def; bwire_def; bus_tybij; MAP]);;

export_thm bwire_bsignal;;

let bwire_bits_to_num = prove
 (`!w t. bits_to_num (bsignal (bwire w) t) = bit_to_num (signal w t)`,
  REWRITE_TAC [bwire_bsignal; bits_to_num_sing]);;

export_thm bwire_bits_to_num;;

let bappend_bsignal = prove
 (`!x y t.
     bsignal (bappend x y) t =
     APPEND (bsignal x t) (bsignal y t)`,
  REWRITE_TAC [bsignal_def; bus_tybij; bappend_def; APPEND; MAP_APPEND]);;

export_thm bappend_bsignal;;

let bappend_bwire_bsignal = prove
 (`!w x t. bsignal (bappend (bwire w) x) t = CONS (signal w t) (bsignal x t)`,
  REWRITE_TAC [bappend_bsignal; bwire_bsignal; APPEND_SING]);;

export_thm bappend_bwire_bsignal;;

let bappend_bits_to_num = prove
 (`!x y t.
     bits_to_num (bsignal (bappend x y) t) =
     bits_to_num (bsignal x t) +
     bit_shl (bits_to_num (bsignal y t)) (width x)`,
  REWRITE_TAC [bappend_bsignal; bits_to_num_append; length_bsignal]);;

export_thm bappend_bits_to_num;;

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

let bnil_bsub = prove
 (`!k n x. bsub bnil k n x <=> k = 0 /\ n = 0 /\ x = bnil`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bsub_def; bnil_width; LE_ZERO; ADD_EQ_0] THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC [take_zero; bnil_def];
   ASM_REWRITE_TAC []]);;

export_thm bnil_bsub;;

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

let bsub_bappend_cancel = prove
 (`!x y n z.
     bsub (bappend x y) 0 (width x + n) (bappend x z) <=>
     bsub y 0 n z`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [bsub_def; drop_zero; ZERO_ADD; bappend_def; bus_tybij; width_def;
     LENGTH_APPEND; LE_ADD_LCANCEL; mk_bus_inj] THEN
  REVERSE_TAC (ASM_CASES_TAC `n <= LENGTH (dest_bus y)`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
    (ISPECL
       [`LENGTH (dest_bus x)`;
        `n : num`;
        `APPEND (dest_bus x) (dest_bus y)`]
     take_add) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [LENGTH_APPEND; LE_ADD_LCANCEL];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [take_append; APPEND_LCANCEL; drop_append] THEN
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (GSYM mk_dest_bus)))) THEN
  REWRITE_TAC [mk_bus_inj]);;

export_thm bsub_bappend_cancel;;

let bsub_bappend_bwire_cancel = prove
 (`!w x n y.
     bsub (bappend (bwire w) x) 0 (SUC n) (bappend (bwire w) y) <=>
     bsub x 0 n y`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL
       [`bwire w`; `x : bus`; `n : num`; `y : bus`]
       bsub_bappend_cancel) THEN
  REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] ADD1; bwire_width]);;

export_thm bsub_bappend_bwire_cancel;;

let bsub_bappend_exists = prove
 (`!x k n y.
     bsub x k n y ==>
     ?d p q.
       width x = k + n + d /\
       bsub x 0 k p /\
       bsub x (k + n) d q /\
       x = bappend p (bappend y q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `k : num`; `n : num`; `y : bus`] bsub_bound) THEN
  ASM_REWRITE_TAC [LE_EXISTS; GSYM ADD_ASSOC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `d : num` THEN
  MP_TAC (SPECL [`x : bus`; `0`; `k : num`] bsub_exists) THEN
  ASM_REWRITE_TAC [ZERO_ADD; LE_ADD] THEN
  DISCH_THEN (X_CHOOSE_THEN `p : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p : bus` THEN
  MP_TAC (SPECL [`x : bus`; `k + n : num`; `d : num`] bsub_exists) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; LE_REFL] THEN
  DISCH_THEN (X_CHOOSE_THEN `q : bus` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q : bus` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC EQ_SYM THEN
  ASM_REWRITE_TAC [GSYM bsub_all] THEN
  MATCH_MP_TAC bsub_add THEN
  ASM_REWRITE_TAC [ZERO_ADD] THEN
  MATCH_MP_TAC bsub_add THEN
  ASM_REWRITE_TAC []);;

export_thm bsub_bappend_exists;;

let bsub_prefix = prove
 (`!x y z. bsub (bappend x y) 0 (width x) z <=> z = x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bsub_def; bappend_width; ZERO_ADD; LE_ADD; drop_zero] THEN
  REWRITE_TAC [bappend_def; width_def; bus_tybij; take_append]);;

export_thm bsub_prefix;;

let bsub_in_suffix = prove
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

export_thm bsub_in_suffix;;

let bsub_in_prefix = prove
 (`!x y k n z.
     k + n <= width x ==>
     (bsub (bappend x y) k n z <=> bsub x k n z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `k : num`; `n : num`] bsub_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `b : bus` STRIP_ASSUME_TAC) THEN
  MP_TAC
    (SPECL
       [`x : bus`; `k : num`; `n : num`; `b : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [bappend_assoc] THEN
  SUBGOAL_THEN `width p + 0 = k` (SUBST1_TAC o SYM) THENL
  [REWRITE_TAC [ADD_0] THEN
   MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [bsub_in_suffix] THEN
  SUBGOAL_THEN `width b = n` (SUBST1_TAC o SYM) THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [bsub_prefix]);;

export_thm bsub_in_prefix;;

let bsub_suffix = prove
 (`!x y z. bsub (bappend x y) (width x) (width y) z <=> z = y`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `0`; `width y`; `z : bus`]
                bsub_in_suffix) THEN
  REWRITE_TAC [ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bsub_all]);;

export_thm bsub_suffix;;

let bsub_bsub = prove
 (`!x j m y k n z.
     bsub x j m y ==>
     (bsub y k n z <=> k + n <= m /\ bsub x (j + k) n z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `j : num`; `m : num`; `y : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `0`; `j : num`; `p : bus`] bsub_width) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [bsub_in_suffix] THEN
  SUBGOAL_THEN `width y = m` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `j : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_CASES_TAC `k + n <= (m : num)` THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC bsub_in_prefix THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [bsub_def]]);;

export_thm bsub_bsub;;

let bsub_bsub_imp = prove
 (`!x j m y k n z.
     bsub x j m y /\
     bsub y k n z ==>
     bsub x (j + k) n z`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `j : num`; `m : num`; `y : bus`;
        `k : num`; `n : num`; `z : bus`]
       bsub_bsub) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC);;

export_thm bsub_bsub_imp;;

let bsub_bits_to_num = prove
 (`!x k n y t.
     bsub x k n y ==>
     bits_to_num (bsignal y t) =
     bit_bound (bit_shr (bits_to_num (bsignal x t)) k) n`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
      [`x : bus`; `k : num`; `n : num`; `y : bus`]
      bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [bappend_bits_to_num] THEN
  SUBGOAL_THEN `width p = k` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [add_bit_shr] THEN
  SUBGOAL_THEN
    `bit_shr (bits_to_num (bsignal p t)) k = 0`
    SUBST1_TAC THENL
  [REWRITE_TAC [bit_shr_eq_zero] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (bsignal p t)` THEN
   REWRITE_TAC [bit_width_bits_to_num] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL];
   ALL_TAC] THEN
  REWRITE_TAC [ZERO_ADD] THEN
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM bit_bound_add))) THEN
  SUBGOAL_THEN `width y = n` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [bit_bound_shl; ADD_0; bit_bound_bound] THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC [bit_bound_id] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH (bsignal y t)` THEN
  REWRITE_TAC [bit_width_bits_to_num] THEN
  ASM_REWRITE_TAC [length_bsignal; LE_REFL]);;

export_thm bsub_bits_to_num;;

let bsub_bits_to_num_le = prove
 (`!x k n y t.
     bsub x k n y ==>
     bit_shl (bits_to_num (bsignal y t)) k <= bits_to_num (bsignal x t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
   (SPECL
      [`x : bus`; `k : num`; `n : num`; `y : bus`; `t : cycle`]
      bsub_bits_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [GSYM bit_bound_shl_add] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `bit_shl (bit_shr (bits_to_num (bsignal x t)) k) k` THEN
  REWRITE_TAC [bit_bound_le] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `bit_bound (bits_to_num (bsignal x t)) k +
     bit_shl (bit_shr (bits_to_num (bsignal x t)) k) k` THEN
  REWRITE_TAC [LE_ADDR] THEN
  REWRITE_TAC [bit_bound; LE_REFL]);;

export_thm bsub_bits_to_num_le;;

let bsub_bsignal = prove
 (`!x y k n xs ys xt yt.
     bsub x k n xs /\ bsub y k n ys /\ bsignal x xt = bsignal y yt ==>
     bsignal xs xt = bsignal ys yt`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`;
        `k : num`;
        `n : num`;
        `xs : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d : num`
       (X_CHOOSE_THEN `xp : bus`
          (X_CHOOSE_THEN `xq : bus`
             STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `width xp = k` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width xs = n` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k : num` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width xq = d` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `x : bus` THEN
   EXISTS_TAC `k + n : num` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`y : bus`;
        `k : num`;
        `n : num`;
        `ys : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d' : num`
       (X_CHOOSE_THEN `yp : bus`
          (X_CHOOSE_THEN `yq : bus`
             STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `width yp = k` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width ys = n` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `k : num` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width yq = d'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `y : bus` THEN
   EXISTS_TAC `k + n : num` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `LENGTH (bsignal x xt) = LENGTH (bsignal y yt)` MP_TAC THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [length_bsignal; bappend_width; EQ_ADD_LCANCEL] THEN
  DISCH_THEN (SUBST_VAR_TAC o SYM) THEN
  MATCH_MP_TAC APPEND_LINJ THEN
  EXISTS_TAC `bsignal xq xt` THEN
  EXISTS_TAC `bsignal yq yt` THEN
  ASM_REWRITE_TAC [length_bsignal] THEN
  MATCH_MP_TAC APPEND_RINJ THEN
  EXISTS_TAC `bsignal xp xt` THEN
  EXISTS_TAC `bsignal yp yt` THEN
  ASM_REWRITE_TAC [LENGTH_APPEND; length_bsignal] THEN
  ASM_REWRITE_TAC [GSYM bappend_bsignal]);;

export_thm bsub_bsignal;;

(* ------------------------------------------------------------------------- *)
(* Power and ground buses.                                                   *)
(* ------------------------------------------------------------------------- *)

let bground_width = prove
 (`!n. width (bground n) = n`,
  REWRITE_TAC [bground_def; width_def; bus_tybij; LENGTH_REPLICATE]);;

export_thm bground_width;;

let bground_zero = prove
 (`bground 0 = bnil`,
  REWRITE_TAC [bground_def; REPLICATE_0; bnil_def]);;

export_thm bground_zero;;

let bground_suc = prove
 (`!n. bground (SUC n) = bappend (bwire ground) (bground n)`,
  REWRITE_TAC
    [bground_def; REPLICATE_SUC; bwire_def; bappend_def; bus_tybij;
     APPEND_SING]);;

export_thm bground_suc;;

let bground_one = prove
 (`bground 1 = bwire ground`,
  REWRITE_TAC [ONE; bground_suc; bground_zero; bappend_bnil]);;

export_thm bground_one;;

let bground_add = prove
 (`!m n. bground (m + n) = bappend (bground m) (bground n)`,
  REWRITE_TAC [bground_def; REPLICATE_ADD; bappend_def; bus_tybij]);;

export_thm bground_add;;

let bground_bsub = prove
 (`!n i k x. bsub (bground n) i k x <=> i + k <= n /\ x = bground k`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC (ASM_CASES_TAC `(i : num) + k <= n`) THENL
  [ASM_REWRITE_TAC [bsub_def; bground_width];
   ALL_TAC] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     REWRITE_RULE [LE_EXISTS]) THEN
  REWRITE_TAC [LE_ADD] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC [bground_add] THEN
  MP_TAC
    (SPECL [`bground i`; `bground (k + d)`; `0`; `k : num`; `x : bus`]
       bsub_in_suffix) THEN
  REWRITE_TAC [bground_width; ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bground_add] THEN
  MP_TAC (SPECL [`bground k`; `bground d`; `x : bus`] bsub_prefix) THEN
  REWRITE_TAC [bground_width]);;

export_thm bground_bsub;;

let bground_bsignal = prove
 (`!n t. bsignal (bground n) t = REPLICATE F n`,
  REWRITE_TAC
    [bsignal_def; bground_def; MAP_REPLICATE; bus_tybij; ground_signal]);;

export_thm bground_bsignal;;

let bground_bits_to_num = prove
 (`!n t. bits_to_num (bsignal (bground n) t) = 0`,
  REWRITE_TAC [bground_bsignal; bits_to_num_replicate_false]);;

export_thm bground_bits_to_num;;

let bpower_width = prove
 (`!n. width (bpower n) = n`,
  REWRITE_TAC [bpower_def; width_def; bus_tybij; LENGTH_REPLICATE]);;

export_thm bpower_width;;

let bpower_zero = prove
 (`bpower 0 = bnil`,
  REWRITE_TAC [bpower_def; REPLICATE_0; bnil_def]);;

export_thm bpower_zero;;

let bpower_suc = prove
 (`!n. bpower (SUC n) = bappend (bwire power) (bpower n)`,
  REWRITE_TAC
    [bpower_def; REPLICATE_SUC; bwire_def; bappend_def; bus_tybij;
     APPEND_SING]);;

export_thm bpower_suc;;

let bpower_one = prove
 (`bpower 1 = bwire power`,
  REWRITE_TAC [ONE; bpower_suc; bpower_zero; bappend_bnil]);;

export_thm bpower_one;;

let bpower_add = prove
 (`!m n. bpower (m + n) = bappend (bpower m) (bpower n)`,
  REWRITE_TAC [bpower_def; REPLICATE_ADD; bappend_def; bus_tybij]);;

export_thm bpower_add;;

let bpower_bsub = prove
 (`!n i k x. bsub (bpower n) i k x <=> i + k <= n /\ x = bpower k`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC (ASM_CASES_TAC `(i : num) + k <= n`) THENL
  [ASM_REWRITE_TAC [bsub_def; bpower_width];
   ALL_TAC] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     REWRITE_RULE [LE_EXISTS]) THEN
  REWRITE_TAC [LE_ADD] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  ONCE_REWRITE_TAC [bpower_add] THEN
  MP_TAC
    (SPECL [`bpower i`; `bpower (k + d)`; `0`; `k : num`; `x : bus`]
       bsub_in_suffix) THEN
  REWRITE_TAC [bpower_width; ADD_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bpower_add] THEN
  MP_TAC (SPECL [`bpower k`; `bpower d`; `x : bus`] bsub_prefix) THEN
  REWRITE_TAC [bpower_width]);;

export_thm bpower_bsub;;

let bpower_bsignal = prove
 (`!n t. bsignal (bpower n) t = REPLICATE T n`,
  REWRITE_TAC
    [bsignal_def; bpower_def; MAP_REPLICATE; bus_tybij; power_signal]);;

export_thm bpower_bsignal;;

let bpower_bits_to_num = prove
 (`!n t. bits_to_num (bsignal (bpower n) t) = 2 EXP n - 1`,
  REWRITE_TAC [bpower_bsignal; bits_to_num_replicate_true]);;

export_thm bpower_bits_to_num;;

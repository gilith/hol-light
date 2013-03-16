(* ========================================================================= *)
(* HARDWARE VERIFICATION                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for hardware verification.                                *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/hardware/hardware.int";;

(* ------------------------------------------------------------------------- *)
(* Modelling hardware in higher order logic in the Gordon style [1].         *)
(*                                                                           *)
(* 1. "Why higher order logic is a good formalism for specifying and         *)
(*    verifying hardware", http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf          *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Definition of wire devices.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-def";;

(* ------------------------------------------------------------------------- *)
(* Wires.                                                                    *)
(* ------------------------------------------------------------------------- *)

let mk_wire_signal =
  let tybij = define_newtype ("w","wire") ("s",`:bool stream`) in
  let def = new_definition `!w. signal w = snth (dest_wire w)` in
  prove
  (`!s t. signal (mk_wire s) t = snth s t`,
   REWRITE_TAC [def; tybij]);;

export_thm mk_wire_signal;;

let power_signal =
  let def = new_definition `power = mk_wire (sreplicate T)` in
  prove
    (`!t. signal power t = T`,
     REWRITE_TAC [mk_wire_signal; def; snth_sreplicate]);;

export_thm power_signal;;

let ground_signal =
  let def = new_definition `ground = mk_wire (sreplicate F)` in
  prove
    (`!t. signal ground t = F`,
     REWRITE_TAC [mk_wire_signal; def; snth_sreplicate]);;

export_thm ground_signal;;

(* ------------------------------------------------------------------------- *)
(* Primitive wire devices.                                                   *)
(* ------------------------------------------------------------------------- *)

let delay_signal =
  let def = new_definition
    `!x y.
       delay x y <=>
       !t. signal y (t + 1) = signal x t` in
  prove
  (`!x y.
      delay x y ==>
      !t. signal y (t + 1) = signal x t`,
   REWRITE_TAC [def]);;

export_thm delay_signal;;

let not_signal =
  let def = new_definition
    `!x y.
       not x y <=>
       !t. signal y t = ~signal x t` in
  prove
  (`!x y.
      not x y ==>
      !t. signal y t = ~signal x t`,
   REWRITE_TAC [def]);;

export_thm not_signal;;

let and2_signal =
  let def = new_definition
    `!x1 x2 y.
       and2 x1 x2 y <=>
       !t. signal y t = (signal x1 t /\ signal x2 t)` in
  prove
  (`!x1 x2 y.
      and2 x1 x2 y ==>
      !t. signal y t = (signal x1 t /\ signal x2 t)`,
   REWRITE_TAC [def]);;

export_thm and2_signal;;

let or2_signal =
  let def = new_definition
    `!x1 x2 y.
       or2 x1 x2 y <=>
       !t. signal y t = (signal x1 t \/ signal x2 t)` in
  prove
  (`!x1 x2 y.
      or2 x1 x2 y ==>
      !t. signal y t = (signal x1 t \/ signal x2 t)`,
   REWRITE_TAC [def]);;

export_thm or2_signal;;

let xor2_signal =
  let def = new_definition
    `!x1 x2 y.
       xor2 x1 x2 y <=>
       !t. signal y t = ~(signal x1 t = signal x2 t)` in
  prove
  (`!x1 x2 y.
      xor2 x1 x2 y ==>
      !t. signal y t = ~(signal x1 t = signal x2 t)`,
   REWRITE_TAC [def]);;

export_thm xor2_signal;;

(* ------------------------------------------------------------------------- *)
(* Wire devices.                                                             *)
(* ------------------------------------------------------------------------- *)

let or3_def = new_definition
  `!x1 x2 x3 y.
     or3 x1 x2 x3 y <=>
     ?w. or2 x1 x2 w /\ or2 w x3 y`;;

export_thm or3_def;;

let xor3_def = new_definition
  `!x1 x2 x3 y.
     xor3 x1 x2 x3 y <=>
     ?w. xor2 x1 x2 w /\ xor2 w x3 y`;;

export_thm xor3_def;;

let majority3_def = new_definition
  `!x1 x2 x3 y.
     majority3 x1 x2 x3 y <=>
     ?w12 w13 w23.
       and2 x1 x2 w12 /\ and2 x1 x3 w13 /\ and2 x2 x3 w23 /\
       or3 w12 w13 w23 y`;;

export_thm majority3_def;;

let adder2_def = new_definition
  `!x y s c.
     adder2 x y s c <=>
     xor2 x y s /\ and2 x y c`;;

export_thm adder2_def;;

let adder3_def = new_definition
  `!x y z s c.
     adder3 x y z s c <=>
     xor3 x y z s /\ majority3 x y z c`;;

export_thm adder3_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of wire devices.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-thm";;

let or3_signal = prove
 (`!x1 x2 x3 y.
     or3 x1 x2 x3 y ==>
     !t. signal y t = (signal x1 t \/ signal x2 t \/ signal x3 t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`w : wire`; `x3 : wire`; `y : wire`] or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC (SPECL [`x1 : wire`; `x2 : wire`; `w : wire`] or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [DISJ_ASSOC]);;

export_thm or3_signal;;

let xor3_signal = prove
 (`!x1 x2 x3 y.
     xor3 x1 x2 x3 y ==>
     !t. signal y t = (signal x1 t = (signal x2 t = signal x3 t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`w : wire`; `x3 : wire`; `y : wire`] xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC (SPECL [`x1 : wire`; `x2 : wire`; `w : wire`] xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x1 t` THEN
  BOOL_CASES_TAC `signal x2 t` THEN
  REWRITE_TAC []);;

export_thm xor3_signal;;

let majority3_signal = prove
 (`!x1 x2 x3 y.
     majority3 x1 x2 x3 y ==>
     !t.
       signal y t =
       ((signal x1 t /\ signal x2 t) \/
        (signal x1 t /\ signal x3 t) \/
        (signal x2 t /\ signal x3 t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC (SPECL [`x1 : wire`; `x2 : wire`; `w12 : wire`] and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC (SPECL [`x1 : wire`; `x3 : wire`; `w13 : wire`] and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC (SPECL [`x2 : wire`; `x3 : wire`; `w23 : wire`] and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w12 : wire`; `w13 : wire`; `w23 : wire`; `y : wire`]
       or3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC []);;

export_thm majority3_signal;;

let adder2 = prove
 (`!x y s c.
     adder2 x y s c ==>
     !t.
       bits_to_num [signal x t] + bits_to_num [signal y t] =
       bits_to_num [signal s t] + 2 * bits_to_num [signal c t]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def; bits_to_num_def; MULT_0; ZERO_ADD] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `s : wire`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `c : wire`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x t` THEN
  BOOL_CASES_TAC `signal y t` THEN
  NUM_REDUCE_TAC);;

export_thm adder2;;

let adder3 = prove
 (`!x y z s c.
     adder3 x y z s c ==>
     !t.
       bits_to_num [signal x t] + bits_to_num [signal y t] +
       bits_to_num [signal z t] =
       bits_to_num [signal s t] + 2 * bits_to_num [signal c t]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def; bits_to_num_def; MULT_0; ZERO_ADD] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `s : wire`]
       xor3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `c : wire`]
       majority3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x t` THEN
  BOOL_CASES_TAC `signal y t` THEN
  BOOL_CASES_TAC `signal z t` THEN
  NUM_REDUCE_TAC);;

export_thm adder3;;

(* ------------------------------------------------------------------------- *)
(* Definition of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-bus-def";;

(* ------------------------------------------------------------------------- *)
(* Buses.                                                                    *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_bus,dest_mk_bus) =
  CONJ_PAIR (define_newtype ("b","bus") ("l",`:wire list`));;

export_thm mk_dest_bus;;
export_thm dest_mk_bus;;

let bus_tybij = CONJ mk_dest_bus dest_mk_bus;;

let width_def = new_definition
  `!b. width b = LENGTH (dest_bus b)`;;

export_thm width_def;;

let bappend_def = new_definition
  `!x y. bappend x y = mk_bus (APPEND (dest_bus x) (dest_bus y))`;;

export_thm bappend_def;;

let bsub_def = new_definition
  `!k n x y.
     bsub k n x y <=>
     k + n <= width x /\
     y = mk_bus (take n (drop k (dest_bus x)))`;;

export_thm bsub_def;;

let wire_def = new_definition
  `!i b w. wire i b w <=> bsub i 1 b (mk_bus [w])`;;

export_thm wire_def;;

let bsignal_def = new_definition
  `!b t. bsignal b t = MAP (\w. signal w t) (dest_bus b)`;;

export_thm bsignal_def;;

(* ------------------------------------------------------------------------- *)
(* Bus devices.                                                              *)
(* ------------------------------------------------------------------------- *)

let compressor2_def = new_definition
  `!x y s c.
     compressor2 x y s c <=>
     ?n.
       width x = n /\ width y = n /\
       width s = n /\ width c = n /\
       !i xi yi si ci.
         wire i x xi /\ wire i y yi /\
         wire i s si /\ wire i c ci ==>
         adder2 xi yi si ci`;;

export_thm compressor2_def;;

(***
let compressor3_def = new_definition
  `!x y z s c.
     compressor3 x y z s c <=>
     ?n.
       width x = n /\ width y = n /\ width z = n /\
       width s = n /\ width c = n /\
       !i.
         i < n ==>
         adder3 (wire x i) (wire y i) (wire z i) (wire s i) (wire c i)`;;

export_thm compressor3_def;;

let compressor4_def = new_definition
  `!w x y z s c.
     compressor4 w x y z s c <=>
     ?n p q p0 p1 q1 z0 z1 s0 s1 s2 c0 c1.
       width w = n + 1 /\ width x = n + 1 /\ width y = n + 1 /\
       width z = n + 1 /\ width s = n + 2 /\ width c = n + 1 /\
       compressor3 w x y p q /\
       wire 0 p p0 /\
       wire 0 z z0 /\
       compressor2 p0 z0 s0 c0 /\
       bsub 1 n p p1 /\
       bsub 0 n q q1 /\
       bsub 1 n z z1 /\
       compressor3 p1 q1 z1 s1 c1 /\
       bsub n 1 q s2 /\
       s = bappend s0 (bappend s1 s2) /\
       c = bappend c0 c1`;;

export_thm compressor4_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-bus-thm";;

let dest_bus_inj_imp = prove
 (`!x y. dest_bus x = dest_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

export_thm dest_bus_inj_imp;;

let dest_bus_inj = prove
 (`!x y. dest_bus x = dest_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC dest_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

export_thm dest_bus_inj;;

let mk_bus_inj_imp = prove
 (`!x y. mk_bus x = mk_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

export_thm mk_bus_inj_imp;;

let mk_bus_inj = prove
 (`!x y. mk_bus x = mk_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC mk_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

export_thm mk_bus_inj;;

let width_zero = prove
 (`!x. width x = 0 <=> x = mk_bus []`,
  GEN_TAC THEN
  REWRITE_TAC [width_def; LENGTH_EQ_NIL] THEN
  ONCE_REWRITE_TAC [GSYM dest_bus_inj] THEN
  REWRITE_TAC [bus_tybij]);;

export_thm width_zero;;

let width_suc = prove
 (`!n x.
     width x = SUC n <=>
     ?w y. x = mk_bus (CONS w (dest_bus y)) /\ width y = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_def; LENGTH_EQ_CONS] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `mk_bus t` THEN
   ASM_REWRITE_TAC [bus_tybij] THEN
   MATCH_MP_TAC dest_bus_inj_imp THEN
   ASM_REWRITE_TAC [bus_tybij];
   STRIP_TAC THEN
   EXISTS_TAC `dest_bus y` THEN
   ASM_REWRITE_TAC [bus_tybij]]);;

export_thm width_suc;;

let width_bsub = prove
  (`!x y k n. bsub k n x y ==> width y = n`,
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

export_thm width_bsub;;
    
let bsub_width = prove
  (`!x y. bsub 0 (width x) x y <=> y = x`,
   REWRITE_TAC
     [bsub_def; width_def; ZERO_ADD; LE_REFL; drop_zero; take_length;
      bus_tybij]);;
   
export_thm bsub_width;;

(***
let bsub_adjacent = prove
  (`!x y z k m n.
      bsub k m x y /\ bsub (k + m) n x z ==>
      bsub k (m + n) x (bappend y z)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bsub_def; GSYM ADD_ASSOC] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [bappend_def; bus_tybij; mk_bus_inj] THEN
   
   

***)

(***
let wire_zero = prove
 (`!x xs y. wire 0 (mk_bus (CONS x xs)) y <=> y = x`,
  REWRITE_TAC [wire_def; bsub_def]
; bus_tybij; nth_zero]);;

export_thm wire_zero;;

let wire_suc = prove
 (`!w x i.
     i < width x ==>
     wire (mk_bus (CONS w (dest_bus x))) (SUC i) = wire x i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; bus_tybij; width_def] THEN
  MATCH_ACCEPT_TAC nth_suc);;

export_thm wire_suc;;
***)

let bsignal_nil = prove
 (`!t. bsignal (mk_bus []) t = []`,
  REWRITE_TAC [bsignal_def; bus_tybij; MAP]);;

export_thm bsignal_nil;;

let bsignal_cons = prove
 (`!w ws t.
     bsignal (mk_bus (CONS w ws)) t =
     CONS (signal w t) (bsignal (mk_bus ws) t)`,
  REWRITE_TAC [bsignal_def; bus_tybij; MAP]);;

export_thm bsignal_cons;;

(***
let compressor2 = prove
 (`!x y s c.
     compressor2 x y s c ==>
     !t.
       bits_to_num (bsignal x t) + bits_to_num (bsignal y t) =
       bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`c : bus`, `c : bus`) THEN
  SPEC_TAC (`s : bus`, `s : bus`) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [bsignal_nil; bits_to_num_nil] THEN
   NUM_REDUCE_TAC;
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
    (X_CHOOSE_THEN `sh : wire`
      (X_CHOOSE_THEN `st : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch : wire`
      (X_CHOOSE_THEN `ct : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((2 * bits_to_num (bsignal xt t)) +
      (2 * bits_to_num (bsignal yt t))) +
     ((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t)))) +
     ((if signal sh t then 1 else 0) +
      2 * (if signal ch t then 1 else 0))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t)))) +
     ((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL; GSYM LEFT_ADD_DISTRIB] THEN
   AP_TERM_TAC THEN
   SPEC_TAC (`t : num`, `t : num`) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   ASM_REWRITE_TAC [LT_SUC] THEN
   MP_TAC (SPECL [`xh : wire`; `xt : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`yh : wire`; `yt : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`sh : wire`; `st : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`ch : wire`; `ct : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   DISCH_THEN ACCEPT_TAC;
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [LT_0; wire_zero] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`xh : wire`; `yh : wire`;
         `sh : wire`; `ch : wire`] adder2) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPEC `t : num`) THEN
   REWRITE_TAC [bits_to_num_def; MULT_0; ZERO_ADD]]);;

export_thm compressor2;;

let compressor3 = prove
 (`!x y z s c.
     compressor3 x y z s c ==>
     !t.
       bits_to_num (bsignal x t) + bits_to_num (bsignal y t) +
       bits_to_num (bsignal z t) =
       bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor3_def; GSYM LEFT_FORALL_IMP_THM] THEN
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
   ASM_REWRITE_TAC [bsignal_nil; bits_to_num_nil] THEN
   NUM_REDUCE_TAC;
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
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((2 * bits_to_num (bsignal xt t)) +
      (2 * bits_to_num (bsignal yt t)) +
      (2 * bits_to_num (bsignal zt t))) +
     ((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0) +
      (if signal zh t then 1 else 0))` THEN
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
    `((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t)))) +
     ((if signal sh t then 1 else 0) +
      2 * (if signal ch t then 1 else 0))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t)))) +
     ((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0) +
      (if signal zh t then 1 else 0))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL; GSYM LEFT_ADD_DISTRIB] THEN
   AP_TERM_TAC THEN
   SPEC_TAC (`t : num`, `t : num`) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   ASM_REWRITE_TAC [LT_SUC] THEN
   MP_TAC (SPECL [`xh : wire`; `xt : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`yh : wire`; `yt : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`zh : wire`; `zt : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`sh : wire`; `st : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   MP_TAC (SPECL [`ch : wire`; `ct : bus`; `i : num`] wire_suc) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC []; DISCH_THEN SUBST1_TAC] THEN
   DISCH_THEN ACCEPT_TAC;
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [LT_0; wire_zero] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`xh : wire`; `yh : wire`; `zh : wire`;
         `sh : wire`; `ch : wire`] adder3) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPEC `t : num`) THEN
   REWRITE_TAC [bits_to_num_def; MULT_0; ZERO_ADD]]);;

export_thm compressor3;;
***)

(***
let compressor4 = prove
 (`!w x y z s c.
     compressor4 w x y z s c ==>
     !t.
       bits_to_num (bsignal w t) + bits_to_num (bsignal x t) +
       bits_to_num (bsignal y t) + bits_to_num (bsignal z t) =
       bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor4_def] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  MP_TAC
    (SPECL
       [`w : bus`; `x : bus`; `y : bus`;
        `p : bus`; `q : bus`] compressor3) THEN
  ASM_REWRITE_TAC [ADD_ASSOC] THEN
  DISCH_THEN (SUBST1_TAC o SPEC `t : num`) THEN

export_thm compressor4;;
***)

logfile_end ();;

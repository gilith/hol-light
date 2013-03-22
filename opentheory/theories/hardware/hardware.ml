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
    `!x y'.
       delay x y' <=>
       !t. signal y' (t + 1) = signal x t` in
  prove
  (`!x y' t.
      delay x y' ==>
      signal y' (t + 1) = signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [def]));;

export_thm delay_signal;;

let not_signal =
  let def = new_definition
    `!x y'.
       not x y' <=>
       !t. signal y' t = ~signal x t` in
  prove
  (`!x y' t.
      not x y' ==>
      signal y' t = ~signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [def]));;

export_thm not_signal;;

let and2_signal =
  let def = new_definition
    `!x1 x2 y'.
       and2 x1 x2 y' <=>
       !t. signal y' t = (signal x1 t /\ signal x2 t)` in
  prove
  (`!x1 x2 y' t.
      and2 x1 x2 y' ==>
      signal y' t = (signal x1 t /\ signal x2 t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [def]));;

export_thm and2_signal;;

let or2_signal =
  let def = new_definition
    `!x1 x2 y'.
       or2 x1 x2 y' <=>
       !t. signal y' t = (signal x1 t \/ signal x2 t)` in
  prove
  (`!x1 x2 y' t.
      or2 x1 x2 y' ==>
      signal y' t = (signal x1 t \/ signal x2 t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [def]));;

export_thm or2_signal;;

let xor2_signal =
  let def = new_definition
    `!x1 x2 y'.
       xor2 x1 x2 y' <=>
       !t. signal y' t = ~(signal x1 t = signal x2 t)` in
  prove
  (`!x1 x2 y' t.
      xor2 x1 x2 y' ==>
      signal y' t = ~(signal x1 t = signal x2 t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [def]));;

export_thm xor2_signal;;

(* ------------------------------------------------------------------------- *)
(* Wire devices.                                                             *)
(* ------------------------------------------------------------------------- *)

let or3_def = new_definition
  `!x1 x2 x3 y'.
     or3 x1 x2 x3 y' <=>
     ?w. or2 x1 x2 w /\ or2 w x3 y'`;;

export_thm or3_def;;

let xor3_def = new_definition
  `!x1 x2 x3 y'.
     xor3 x1 x2 x3 y' <=>
     ?w. xor2 x1 x2 w /\ xor2 w x3 y'`;;

export_thm xor3_def;;

let majority3_def = new_definition
  `!x1 x2 x3 y'.
     majority3 x1 x2 x3 y' <=>
     ?w12 w13 w23.
       and2 x1 x2 w12 /\ and2 x1 x3 w13 /\ and2 x2 x3 w23 /\
       or3 w12 w13 w23 y'`;;

export_thm majority3_def;;

let adder2_def = new_definition
  `!x y s' c'.
     adder2 x y s' c' <=>
     xor2 x y s' /\ and2 x y c'`;;

export_thm adder2_def;;

let adder3_def = new_definition
  `!x y z s' c'.
     adder3 x y z s' c' <=>
     xor3 x y z s' /\ majority3 x y z c'`;;

export_thm adder3_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of wire devices.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-thm";;

let or3_signal = prove
 (`!x1 x2 x3 y' t.
     or3 x1 x2 x3 y' ==>
     signal y' t = (signal x1 t \/ signal x2 t \/ signal x3 t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x3 : wire`; `y' : wire`; `t : num`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x1 : wire`; `x2 : wire`; `w : wire`; `t : num`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [DISJ_ASSOC]);;

export_thm or3_signal;;

let xor3_signal = prove
 (`!x1 x2 x3 y' t.
     xor3 x1 x2 x3 y' ==>
     signal y' t = (signal x1 t = (signal x2 t = signal x3 t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x3 : wire`; `y' : wire`; `t : num`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x1 : wire`; `x2 : wire`; `w : wire`; `t : num`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x1 t` THEN
  BOOL_CASES_TAC `signal x2 t` THEN
  REWRITE_TAC []);;

export_thm xor3_signal;;

let majority3_signal = prove
 (`!x1 x2 x3 y' t.
     majority3 x1 x2 x3 y' ==>
     signal y' t =
     ((signal x1 t /\ signal x2 t) \/
      (signal x1 t /\ signal x3 t) \/
      (signal x2 t /\ signal x3 t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x1 : wire`; `x2 : wire`; `w12 : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x1 : wire`; `x3 : wire`; `w13 : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x2 : wire`; `x3 : wire`; `w23 : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w12 : wire`; `w13 : wire`; `w23 : wire`; `y' : wire`; `t : num`]
       or3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC []);;

export_thm majority3_signal;;

let adder2 = prove
 (`!x y s' c' t.
     adder2 x y s' c' ==>
     bits_to_num [signal x t] + bits_to_num [signal y t] =
     bits_to_num [signal s' t] + 2 * bits_to_num [signal c' t]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def; bits_to_num_def; MULT_0; ZERO_ADD] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `s' : wire`; `t : num`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `c' : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal x t` THEN
  BOOL_CASES_TAC `signal y t` THEN
  NUM_REDUCE_TAC);;

export_thm adder2;;

let adder3 = prove
 (`!x y z s' c' t.
     adder3 x y z s' c' ==>
     bits_to_num [signal x t] + bits_to_num [signal y t] +
     bits_to_num [signal z t] =
     bits_to_num [signal s' t] + 2 * bits_to_num [signal c' t]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def; bits_to_num_def; MULT_0; ZERO_ADD] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `s' : wire`; `t : num`]
       xor3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `z : wire`; `c' : wire`; `t : num`]
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
  `!x k n y.
     bsub x k n y <=>
     k + n <= width x /\
     y = mk_bus (take n (drop k (dest_bus x)))`;;

export_thm bsub_def;;

let wire_def = new_definition
  `!b i w. wire b i w <=> bsub b i 1 (mk_bus [w])`;;

export_thm wire_def;;

let bsignal_def = new_definition
  `!b t. bsignal b t = MAP (\w. signal w t) (dest_bus b)`;;

export_thm bsignal_def;;

let bground_def = new_definition
  `!n. bground n = mk_bus (REPLICATE ground n)`;;

export_thm bground_def;;

let bpower_def = new_definition
  `!n. bpower n = mk_bus (REPLICATE power n)`;;

export_thm bpower_def;;

(* ------------------------------------------------------------------------- *)
(* Bus devices.                                                              *)
(* ------------------------------------------------------------------------- *)

let compressor2_def = new_definition
  `!x y s' c'.
     compressor2 x y s' c' <=>
     ?n.
       width x = n /\ width y = n /\
       width s' = n /\ width c' = n /\
       !i xi yi si' ci'.
         wire x i xi /\ wire y i yi /\
         wire s' i si' /\ wire c' i ci' ==>
         adder2 xi yi si' ci'`;;

export_thm compressor2_def;;

let compressor3_def = new_definition
  `!x y z s' c'.
     compressor3 x y z s' c' <=>
     ?n.
       width x = n /\ width y = n /\ width z = n /\
       width s' = n /\ width c' = n /\
       !i xi yi zi si' ci'.
         wire x i xi /\ wire y i yi /\ wire z i zi /\
         wire s' i si' /\ wire c' i ci' ==>
         adder3 xi yi zi si' ci'`;;

export_thm compressor3_def;;

let compressor4_def = new_definition
  `!w x y z s' c'.
     compressor4 w x y z s' c' <=>
     ?n p q p0 p1 q1 z0 z1 s0' s1' s2' c0' c1'.
       width w = n + 1 /\
       width x = n + 1 /\
       width y = n + 1 /\
       width z = n + 1 /\
       width s' = n + 2 /\
       width c' = n + 1 /\
       compressor3 w x y p q /\
       bsub p 0 1 p0 /\
       bsub z 0 1 z0 /\
       compressor2 p0 z0 s0' c0' /\
       bsub p 1 n p1 /\
       bsub q 0 n q1 /\
       bsub z 1 n z1 /\
       compressor3 p1 q1 z1 s1' c1' /\
       bsub q n 1 s2' /\
       s' = bappend s0' (bappend s1' s2') /\
       c' = bappend c0' c1'`;;

export_thm compressor4_def;;

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

export_thm width_bsub;;

let bsub_width = prove
  (`!x y. bsub x 0 (width x) y <=> y = x`,
   REWRITE_TAC
     [bsub_def; width_def; ZERO_ADD; LE_REFL; drop_zero; take_length;
      bus_tybij]);;

export_thm bsub_width;;

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

let wire_zero = prove
 (`!v b w. wire (mk_bus (CONS v (dest_bus b))) 0 w <=> w = v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; bsub_def; bus_tybij; width_def] THEN
  REWRITE_TAC [ONE; ADD; LENGTH_CONS; LE_SUC; mk_bus_inj; drop_zero] THEN
  MP_TAC (ISPECL [`0`; `v : wire`; `dest_bus b`] take_suc) THEN
  ASM_REWRITE_TAC [LE_0] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [take_zero; CONS_11]);;

export_thm wire_zero;;

let wire_suc = prove
 (`!v b i w. wire (mk_bus (CONS v (dest_bus b))) (SUC i) w <=> wire b i w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; bsub_def; bus_tybij; width_def] THEN
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

let bsignal_append = prove
 (`!b1 b2 t.
     bsignal (bappend b1 b2) t =
     APPEND (bsignal b1 t) (bsignal b2 t)`,
  REWRITE_TAC [bsignal_def; bus_tybij; bappend_def; APPEND; MAP_APPEND]);;

export_thm bsignal_append;;

let bits_to_num_bsignal_append = prove
 (`!b1 b2 t.
     bits_to_num (bsignal (bappend b1 b2) t) =
     bits_to_num (bsignal b1 t) + 2 EXP width b1 * bits_to_num (bsignal b2 t)`,
  REWRITE_TAC
    [bsignal_append; bits_to_num_append; width_def; bsignal_def; LENGTH_MAP]);;

export_thm bits_to_num_bsignal_append;;

let compressor2 = prove
 (`!x y s' c' t.
     compressor2 x y s' c' ==>
     bits_to_num (bsignal x t) + bits_to_num (bsignal y t) =
     bits_to_num (bsignal s' t) + 2 * bits_to_num (bsignal c' t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`c' : bus`, `c' : bus`) THEN
  SPEC_TAC (`s' : bus`, `s' : bus`) THEN
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
    (X_CHOOSE_THEN `sh' : wire`
      (X_CHOOSE_THEN `st' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch' : wire`
      (X_CHOOSE_THEN `ct' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0)) +
     ((2 * bits_to_num (bsignal xt t)) +
      (2 * bits_to_num (bsignal yt t)))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((if signal sh' t then 1 else 0) +
      2 * (if signal ch' t then 1 else 0)) +
     ((2 * bits_to_num (bsignal st' t)) +
      (2 * (2 * bits_to_num (bsignal ct' t))))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0)) +
     ((2 * bits_to_num (bsignal st' t)) +
      (2 * (2 * bits_to_num (bsignal ct' t))))` THEN
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
        [`xh : wire`; `yh : wire`;
         `sh' : wire`; `ch' : wire`]) THEN
   MP_TAC
     (SPECL
        [`xh : wire`; `yh : wire`;
         `sh' : wire`; `ch' : wire`; `t : num`] adder2) THEN
   ASM_REWRITE_TAC [bits_to_num_def; MULT_0; ADD_0]]);;

export_thm compressor2;;

let compressor2_width = prove
 (`!x y s' c'.
     compressor2 x y s' c' ==>
     width s' = width x /\
     width c' = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor2_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm compressor2_width;;

let compressor3 = prove
 (`!x y z s' c' t.
     compressor3 x y z s' c' ==>
     bits_to_num (bsignal x t) + bits_to_num (bsignal y t) +
     bits_to_num (bsignal z t) =
     bits_to_num (bsignal s' t) + 2 * bits_to_num (bsignal c' t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor3_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`c' : bus`, `c' : bus`) THEN
  SPEC_TAC (`s' : bus`, `s' : bus`) THEN
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
    (X_CHOOSE_THEN `sh' : wire`
      (X_CHOOSE_THEN `st' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch' : wire`
      (X_CHOOSE_THEN `ct' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0) +
      (if signal zh t then 1 else 0)) +
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
    `((if signal sh' t then 1 else 0) +
      2 * (if signal ch' t then 1 else 0)) +
     ((2 * bits_to_num (bsignal st' t)) +
      (2 * (2 * bits_to_num (bsignal ct' t))))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((if signal xh t then 1 else 0) +
      (if signal yh t then 1 else 0) +
      (if signal zh t then 1 else 0)) +
     ((2 * bits_to_num (bsignal st' t)) +
      (2 * (2 * bits_to_num (bsignal ct' t))))` THEN
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
         `sh' : wire`; `ch' : wire`]) THEN
   MP_TAC
     (SPECL
        [`xh : wire`; `yh : wire`; `zh : wire`;
         `sh' : wire`; `ch' : wire`; `t : num`] adder3) THEN
   ASM_REWRITE_TAC [bits_to_num_def; MULT_0; ADD_0]]);;

export_thm compressor3;;

let compressor3_width = prove
 (`!x y z s' c'.
     compressor3 x y z s' c' ==>
     width s' = width x /\
     width c' = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor3_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm compressor3_width;;

let compressor4 = prove
 (`!w x y z s' c' t.
     compressor4 w x y z s' c' ==>
     bits_to_num (bsignal w t) + bits_to_num (bsignal x t) +
     bits_to_num (bsignal y t) + bits_to_num (bsignal z t) =
     bits_to_num (bsignal s' t) + 2 * bits_to_num (bsignal c' t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor4_def] THEN
  STRIP_TAC THEN
  REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
  MP_TAC
    (SPECL
       [`w : bus`; `x : bus`; `y : bus`;
        `p : bus`; `q : bus`; `t : num`] compressor3) THEN
  ASM_REWRITE_TAC [ADD_ASSOC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`w : bus`; `x : bus`; `y : bus`;
        `p : bus`; `q : bus`] compressor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `bappend p0 p1 = p` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_width] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend z0 z1 = z` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_width] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [bits_to_num_bsignal_append] THEN
  SUBGOAL_THEN `width p0 = 1` ASSUME_TAC THENL
  [MATCH_MP_TAC width_bsub THEN
   EXISTS_TAC `p : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width z0 = 1` ASSUME_TAC THENL
  [MATCH_MP_TAC width_bsub THEN
   EXISTS_TAC `z : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`p0 : bus`; `z0 : bus`; `s0' : bus`; `c0' : bus`]
       compressor2_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [EXP_1] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal p0 t) +
      bits_to_num (bsignal z0 t)) +
     (2 * bits_to_num (bsignal p1 t) +
      2 * bits_to_num (bsignal q t) +
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
    `(bits_to_num (bsignal s0' t) +
      2 * bits_to_num (bsignal c0' t)) +
     (2 * bits_to_num (bsignal (bappend s1' s2') t) +
      2 * (2 * bits_to_num (bsignal c1' t)))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL; LEFT_ADD_DISTRIB] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal s0' t) +
      2 * bits_to_num (bsignal c0' t)) +
     (2 * bits_to_num (bsignal p1 t) +
      2 * bits_to_num (bsignal q t) +
      2 * bits_to_num (bsignal z1 t))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   MATCH_MP_TAC compressor2 THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  REWRITE_TAC [GSYM LEFT_ADD_DISTRIB] THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN `bappend q1 s2' = q` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_width] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [bits_to_num_bsignal_append] THEN
  SUBGOAL_THEN `width q1 = n` ASSUME_TAC THENL
  [MATCH_MP_TAC width_bsub THEN
   EXISTS_TAC `q : bus` THEN
   EXISTS_TAC `0` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN `width p1 = n` ASSUME_TAC THENL
  [MATCH_MP_TAC width_bsub THEN
   EXISTS_TAC `p : bus` THEN
   EXISTS_TAC `1` THEN
   FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`p1 : bus`; `q1 : bus`; `z1 : bus`; `s1' : bus`; `c1' : bus`]
       compressor3_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal p1 t) +
      bits_to_num (bsignal q1 t) +
      bits_to_num (bsignal z1 t)) +
     2 EXP n * bits_to_num (bsignal s2' t)` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal s1' t) + 2 * bits_to_num (bsignal c1' t)) +
     2 EXP n * bits_to_num (bsignal s2' t)` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC compressor3 THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm compressor4;;

let compressor4_width = prove
 (`!w x y z s' c'.
     compressor4 w x y z s' c' ==>
     width s' = width w + 1 /\
     width c' = width w`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor4_def; GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [TWO; ONE; ADD_SUC; ADD_0]);;

export_thm compressor4_width;;

logfile_end ();;

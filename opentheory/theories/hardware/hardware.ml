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

let delay_def = new_definition
  `!x y'.
     delay x y' <=>
     !t. signal y' (t + 1) = signal x t`;;

export_thm delay_def;;

let not_def = new_definition
  `!x y'.
     not x y' <=>
     !t. signal y' t = ~signal x t`;;

export_thm not_def;;

let and2_def = new_definition
  `!x y z'.
     and2 x y z' <=>
     !t. signal z' t = (signal x t /\ signal y t)`;;

export_thm and2_def;;

let or2_def = new_definition
  `!x y z'.
     or2 x y z' <=>
     !t. signal z' t = (signal x t \/ signal y t)`;;

export_thm or2_def;;

let xor2_def = new_definition
  `!x y z'.
     xor2 x y z' <=>
     !t. signal z' t = ~(signal x t = signal y t)`;;

export_thm xor2_def;;

let case1_def = new_definition
  `!s x y z'.
     case1 s x y z' <=>
     !t. signal z' t = (if signal s t then signal x t else signal y t)`;;

export_thm case1_def;;

(* ------------------------------------------------------------------------- *)
(* Wire devices.                                                             *)
(* ------------------------------------------------------------------------- *)

let or3_def = new_definition
  `!w x y z'.
     or3 w x y z' <=>
     ?wx. or2 w x wx /\ or2 wx y z'`;;

export_thm or3_def;;

let xor3_def = new_definition
  `!w x y z'.
     xor3 w x y z' <=>
     ?wx. xor2 w x wx /\ xor2 wx y z'`;;

export_thm xor3_def;;

let majority3_def = new_definition
  `!w x y z'.
     majority3 w x y z' <=>
     ?wx wy xy.
       and2 w x wx /\ and2 w y wy /\ and2 x y xy /\
       or3 wx wy xy z'`;;

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

let bit_to_num_power = prove
  (`!t. bit_to_num (signal power t) = 1`,
   REWRITE_TAC [power_signal; bit_to_num_true]);;

export_thm bit_to_num_power;;

let bit_to_num_ground = prove
  (`!t. bit_to_num (signal ground t) = 0`,
   REWRITE_TAC [ground_signal; bit_to_num_false]);;

export_thm bit_to_num_ground;;

let delay_signal = prove
  (`!x y' t.
      delay x y' ==>
      signal y' (t + 1) = signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [delay_def]));;

export_thm delay_signal;;

let not_signal = prove
  (`!x y' t.
      not x y' ==>
      signal y' t = ~signal x t`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [not_def]));;

export_thm not_signal;;

let and2_signal = prove
  (`!x y z' t.
      and2 x y z' ==>
      signal z' t = (signal x t /\ signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [and2_def]));;

export_thm and2_signal;;

let and2_right_ground = prove
 (`!x y'. y' = ground ==> and2 x ground y'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [and2_def; ground_signal]);;

export_thm and2_right_ground;;

let or2_signal = prove
  (`!x y z' t.
      or2 x y z' ==>
      signal z' t = (signal x t \/ signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [or2_def]));;

export_thm or2_signal;;

let or2_right_ground = prove
 (`!x y'. y' = x ==> or2 x ground y'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [or2_def; ground_signal]);;

export_thm or2_right_ground;;

let xor2_signal = prove
  (`!x y z' t.
      xor2 x y z' ==>
      signal z' t = ~(signal x t = signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [xor2_def]));;

export_thm xor2_signal;;

let xor2_right_ground = prove
 (`!x y'. y' = x ==> xor2 x ground y'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [xor2_def; ground_signal]);;

export_thm xor2_right_ground;;

let case1_signal = prove
  (`!s x y z' t.
      case1 s x y z' ==>
      signal z' t = (if signal s t then signal x t else signal y t)`,
   REPEAT GEN_TAC THEN
   DISCH_THEN (MATCH_ACCEPT_TAC o REWRITE_RULE [case1_def]));;

export_thm case1_signal;;

let or3_signal = prove
 (`!w x y z' t.
     or3 w x y z' ==>
     signal z' t = (signal w t \/ signal x t \/ signal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `y : wire`; `z' : wire`; `t : num`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : num`]
       or2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [DISJ_ASSOC]);;

export_thm or3_signal;;

let or3_right_ground = prove
 (`!x y z'. or2 x y z' ==> or3 x y ground z'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [or3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z' : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC or2_right_ground THEN
  REFL_TAC);;

export_thm or3_right_ground;;

let xor3_signal = prove
 (`!w x y z' t.
     xor3 w x y z' ==>
     signal z' t = (signal w t = (signal x t = signal y t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `y : wire`; `z' : wire`; `t : num`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : num`]
       xor2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `signal w t` THEN
  BOOL_CASES_TAC `signal x t` THEN
  REWRITE_TAC []);;

export_thm xor3_signal;;

let xor3_right_ground = prove
 (`!x y z'. xor2 x y z' ==> xor3 x y ground z'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z' : wire` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC xor2_right_ground THEN
  REFL_TAC);;

export_thm xor3_right_ground;;

let majority3_signal = prove
 (`!w x y z' t.
     majority3 w x y z' ==>
     signal z' t =
     ((signal w t /\ signal x t) \/
      (signal w t /\ signal y t) \/
      (signal x t /\ signal y t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`; `x : wire`; `wx : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`w : wire`; `y : wire`; `wy : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`x : wire`; `y : wire`; `xy : wire`; `t : num`]
       and2_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  MP_TAC
    (SPECL
       [`wx : wire`; `wy : wire`; `xy : wire`; `z' : wire`; `t : num`]
       or3_signal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; STRIP_TAC]) THEN
  ASM_REWRITE_TAC []);;

export_thm majority3_signal;;

let majority3_right_ground = prove
 (`!x y z'. and2 x y z' ==> majority3 x y ground z'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [majority3_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `z' : wire` THEN
  EXISTS_TAC `ground` THEN
  EXISTS_TAC `ground` THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC and2_right_ground THEN
   REFL_TAC;
   MATCH_MP_TAC and2_right_ground THEN
   REFL_TAC;
   MATCH_MP_TAC or3_right_ground THEN
   MATCH_MP_TAC or2_right_ground THEN
   REFL_TAC]);;

export_thm majority3_right_ground;;

let adder3_right_ground = prove
 (`!x y s' c'. adder2 x y s' c' ==> adder3 x y ground s' c'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder2_def; adder3_def] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC xor3_right_ground THEN
   ASM_REWRITE_TAC [];
   MATCH_MP_TAC majority3_right_ground THEN
   ASM_REWRITE_TAC []]);;

export_thm adder3_right_ground;;

let adder3 = prove
 (`!x y z s' c' t.
     adder3 x y z s' c' ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) +
     bit_to_num (signal z t) =
     bit_to_num (signal s' t) + 2 * bit_to_num (signal c' t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def] THEN
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
  REWRITE_TAC [bit_to_num_def] THEN
  NUM_REDUCE_TAC);;

export_thm adder3;;

let adder2 = prove
 (`!x y s' c' t.
     adder2 x y s' c' ==>
     bit_to_num (signal x t) + bit_to_num (signal y t) =
     bit_to_num (signal s' t) + 2 * bit_to_num (signal c' t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : wire`; `y : wire`; `s' : wire`; `c' : wire`]
            adder3_right_ground) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`x : wire`; `y : wire`; `ground`;
            `s' : wire`; `c' : wire`; `t : num`]
       adder3) THEN
  ASM_REWRITE_TAC [bit_to_num_ground; ADD_0]);;

export_thm adder2;;

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

let bdelay_def = new_definition
  `!x y'.
     bdelay x y' <=>
     ?n.
       width x = n /\
       width y' = n /\
       !i xi yi'.
         wire x i xi /\
         wire y' i yi' ==>
         delay xi yi'`;;

export_thm bdelay_def;;

let bcase1_def = new_definition
  `!s x y z'.
     bcase1 s x y z' <=>
     ?n.
       width x = n /\
       width y = n /\
       width z' = n /\
       !i xi yi zi'.
         wire x i xi /\
         wire y i yi /\
         wire z' i zi' ==>
         case1 s xi yi zi'`;;

export_thm bcase1_def;;

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

let icounter_def = new_definition
  `!ld nb inc dn'.
      icounter ld nb inc dn' <=>
      ?r sp sp0 sp1 cp cp0 cp1 cp2 sq sq0 sq1 cq cq0 cq1 sr cr dp dq.
         width nb = r + 1 /\
         width sp = r + 1 /\
         width cp = r + 1 /\
         width sq = r + 1 /\
         width cq = r + 1 /\
         width sr = r + 1 /\
         width cr = r + 1
         /\
         wire sp 0 sp0 /\
         bsub sp 0 r sp1 /\
         wire sq 0 sq0 /\
         bsub sq 0 r sq1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1
         /\
         xor2 inc sp0 sq0 /\
         and2 inc sp0 cq0 /\
         compressor2 sp1 cp1 sq1 cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb sq sr /\
         bcase1 ld (bground (r + 1)) cq cr /\
         case1 ld ground dq dn'
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn' dp`;;

export_thm icounter_def;;

let counter_def = new_definition
  `!ld nb dn'.
      counter ld nb dn' <=>
      ?r nb0 nb1 sp cp cp0 cp1 cp2 sq cq cq0 cq1 sr cr cr0 cr1 dp dq.
         width nb = r + 1 /\
         width sp = r /\
         width cp = r + 1 /\
         width sq = r /\
         width cq = r + 1 /\
         width sr = r /\
         width cr = r + 1
         /\
         wire nb 0 nb0 /\
         bsub nb 1 r nb1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1 /\
         wire cr 0 cr0 /\
         bsub cr 1 r cr1
         /\
         not cp0 cq0 /\
         compressor2 sp cp1 sq cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb1 sq sr /\
         case1 ld nb0 cq0 cr0 /\
         bcase1 ld (bground r) cq1 cr1 /\
         case1 ld ground dq dn'
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn' dp`;;

export_thm counter_def;;

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

let width_nil = prove
 (`width (mk_bus []) = 0`,
  REWRITE_TAC [width_def; bus_tybij; LENGTH_NIL]);;

export_thm width_nil;;

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

let bsub_exists = prove
  (`!x k n. k + n <= width x ==> ?y. bsub x k n y`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [bsub_def] THEN
   EXISTS_TAC `mk_bus (take n (drop k (dest_bus x)))` THEN
   REFL_TAC);;

export_thm bsub_exists;;

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

let wire_exists = prove
  (`!b i. i < width b ==> ?w. wire b i w`,
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [wire_def; bsub_def; GSYM ADD1; LE_SUC_LT] THEN
   EXISTS_TAC `HD (drop i (dest_bus b))` THEN
   REWRITE_TAC [mk_bus_inj] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [width_def; LT_EXISTS] THEN
   STRIP_TAC THEN
   MP_TAC (ISPECL [`i : num`; `dest_bus b`] length_drop) THEN
   POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [LE_ADD; ADD_SUB2; LENGTH_EQ_CONS] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [take_one; HD]);;

export_thm wire_exists;;

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

let length_bsignal = prove
 (`!b t. LENGTH (bsignal b t) = width b`,
  REWRITE_TAC [bsignal_def; bus_tybij; width_def; LENGTH_MAP]);;

export_thm length_bsignal;;

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

let bsignal_wire = prove
 (`!w t. bsignal (mk_bus [w]) t = [signal w t]`,
  REWRITE_TAC [bsignal_cons; bsignal_nil; bus_tybij]);;

export_thm bsignal_wire;;

let bsignal_append = prove
 (`!b1 b2 t.
     bsignal (bappend b1 b2) t =
     APPEND (bsignal b1 t) (bsignal b2 t)`,
  REWRITE_TAC [bsignal_def; bus_tybij; bappend_def; APPEND; MAP_APPEND]);;

export_thm bsignal_append;;

let bits_to_num_bsignal_append = prove
 (`!b1 b2 t.
     bits_to_num (bsignal (bappend b1 b2) t) =
     bits_to_num (bsignal b1 t) +
     bit_shl (bits_to_num (bsignal b2 t)) (width b1)`,
  REWRITE_TAC
    [bsignal_append; bits_to_num_append; width_def; bsignal_def; LENGTH_MAP]);;

export_thm bits_to_num_bsignal_append;;

let width_bground = prove
 (`!n. width (bground n) = n`,
  REWRITE_TAC [bground_def; width_def; bus_tybij; LENGTH_REPLICATE]);;

export_thm width_bground;;

let bsub_bground = prove
 (`!n i k x. bsub (bground n) i k x <=> i + k <= n /\ x = bground k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bsub_def; width_bground; bground_def; bus_tybij] THEN
  ASM_CASES_TAC `i + k <= (n : num)` THENL
  [ASM_REWRITE_TAC [] THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   POP_ASSUM
     (CHOOSE_THEN SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS; GSYM ADD_ASSOC]) THEN
   MP_TAC
     (ISPECL [`i : num`; `i + k + d : num`; `ground`] drop_replicate) THEN
   REWRITE_TAC [LE_ADD] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUB2] THEN
   MATCH_MP_TAC take_replicate THEN
   MATCH_ACCEPT_TAC LE_ADD;
   ASM_REWRITE_TAC []]);;

export_thm bsub_bground;;

let wire_bground = prove
 (`!n k w. wire (bground n) k w <=> k < n /\ w = ground`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [wire_def; bsub_bground] THEN
  REWRITE_TAC [GSYM ADD1; LE_SUC_LT; bground_def; mk_bus_inj] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [ONE; REPLICATE; CONS_11]);;

export_thm wire_bground;;

let bsignal_bground = prove
 (`!n t. bsignal (bground n) t = REPLICATE F n`,
  REWRITE_TAC
    [bsignal_def; bground_def; MAP_REPLICATE; bus_tybij; ground_signal]);;

export_thm bsignal_bground;;

let bits_to_num_bsignal_bground = prove
 (`!n t. bits_to_num (bsignal (bground n) t) = 0`,
  REWRITE_TAC [bsignal_bground; bits_to_num_replicate_false]);;

export_thm bits_to_num_bsignal_bground;;

let bdelay_width = prove
 (`!x y'.
     bdelay x y' ==>
     width y' = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bdelay_width;;

let bdelay_bsignal = prove
 (`!x y' t. bdelay x y' ==> bsignal y' (t + 1) = bsignal x t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bdelay_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`y' : bus`, `y' : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [bsignal_def; MAP_NIL; bus_tybij];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh' : wire`
      (X_CHOOSE_THEN `yt' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [bsignal_cons; bus_tybij; CONS_11] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM
     (MP_TAC o SPECL [`0`; `xh : wire`; `yh' : wire`]) THEN
   REWRITE_TAC [wire_zero; delay_def] THEN
   DISCH_THEN MATCH_ACCEPT_TAC;
   FIRST_X_ASSUM
     (MP_TAC o SPECL [`xt : bus`; `yt' : bus`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [wire_suc]]);;

export_thm bdelay_bsignal;;

let bcase1_width = prove
 (`!s x y z'.
     bcase1 s x y z' ==>
     width z' = width x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm bcase1_width;;

let bcase1_bsignal = prove
 (`!s x y z' t.
      bcase1 s x y z' ==>
      bsignal z' t = (if signal s t then bsignal x t else bsignal y t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bcase1_def; GSYM LEFT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  SPEC_TAC (`z' : bus`, `z' : bus`) THEN
  SPEC_TAC (`y : bus`, `y : bus`) THEN
  SPEC_TAC (`x : bus`, `x : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [COND_ID];
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
    (X_CHOOSE_THEN `zh' : wire`
      (X_CHOOSE_THEN `zt' : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `signal s t` THEN
  (ASM_REWRITE_TAC [bsignal_cons; bus_tybij; CONS_11] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM
      (MP_TAC o SPECL [`0`; `xh : wire`; `yh : wire`; `zh' : wire`]) THEN
    REWRITE_TAC [wire_zero; case1_def] THEN
    DISCH_THEN (SUBST1_TAC o SPEC `t : num`) THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM
      (MP_TAC o SPECL [`xt : bus`; `yt : bus`; `zt' : bus`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
    EXISTS_TAC `SUC i` THEN
    ASM_REWRITE_TAC [wire_suc]]));;

export_thm bcase1_bsignal;;

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

let compressor3_right_bground = prove
 (`!x y n s' c'.
     n = width x /\ compressor2 x y s' c' ==>
     compressor3 x y (bground n) s' c'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor2_def; compressor3_def] THEN
  CONV_TAC (REWR_CONV (GSYM IMP_IMP)) THEN
  DISCH_THEN SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC [width_bground] THEN
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `wire (bground n) i zi` THEN
  REWRITE_TAC [wire_bground] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MATCH_MP_TAC adder3_right_ground THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC []);;

export_thm compressor3_right_bground;;

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
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij; bit_cons_def] THEN
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
    `(bit_to_num (signal sh' t) +
      2 * bit_to_num (signal ch' t)) +
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
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
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
   MATCH_MP_TAC adder3 THEN
   ASM_REWRITE_TAC []]);;

export_thm compressor3;;

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

let compressor2 = prove
 (`!x y s' c' t.
     compressor2 x y s' c' ==>
     bits_to_num (bsignal x t) + bits_to_num (bsignal y t) =
     bits_to_num (bsignal s' t) + 2 * bits_to_num (bsignal c' t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x : bus`; `y : bus`; `width x`; `s' : bus`; `c' : bus`]
                compressor3_right_bground) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`x : bus`; `y : bus`; `bground (width x)`; `s' : bus`; `c' : bus`]
       compressor3) THEN
  ASM_REWRITE_TAC [bits_to_num_bsignal_bground; ADD_0] THEN
  DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm compressor2;;

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
  ASM_REWRITE_TAC [bit_shl_one] THEN
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
     bit_shl (bits_to_num (bsignal s2' t)) n` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bits_to_num (bsignal s1' t) + 2 * bits_to_num (bsignal c1' t)) +
     bit_shl (bits_to_num (bsignal s2' t)) n` THEN
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

(***
let icounter = prove
 (`!n ld nb inc dn' t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n = 2 EXP (width nb) /\
     icounter ld nb inc dn' ==>
     (signal dn' (t + k) <=>
      n <= CARD { i | 0 < i /\ i + width nb <= k /\ signal inc (t + i) })`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [icounter_def; GSYM RIGHT_EXISTS_AND_THM;
     GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
  [UNDISCH_TAC `bits_to_num (bsignal nb t) + n = 2 EXP (width nb)` THEN
   ASM_REWRITE_TAC [ADD_0] THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `bsignal nb t` bits_to_num_bound) THEN
   ASM_REWRITE_TAC [length_bsignal; LT_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?f. (\j. CARD { i | 0 < i /\ i <= j /\ signal inc (t + i) }) = f`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!j1 j2. j1 <= j2 ==> (f : num -> num) j1 <= f j2`
    STRIP_ASSUME_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN   
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC CARD_SUBSET THEN
   CONJ_TAC THENL
   [REWRITE_TAC [SUBSET; IN_ELIM] THEN
    X_GEN_TAC `i : num` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `j1 : num` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{ i : num | i <= j2 }` THEN
    REWRITE_TAC [FINITE_NUMSEG_LE; SUBSET; IN_ELIM] THEN
    REPEAT STRIP_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `n <= CARD { i | 0 < i /\ i + width nb <= k /\ signal inc (t + i) } <=>
     width nb <= k /\ n <= f (k - width nb)`
    SUBST1_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   ASM_CASES_TAC `width nb <= k` THENL
   [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [LE_ADD; ADD_SUB2] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) THEN
    CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
    REWRITE_TAC [LE_ADD_LCANCEL];
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LE; LT_EXISTS]) THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL_0] THEN
    ASM_REWRITE_TAC [ADD_SUC; NOT_SUC; EMPTY_GSPEC; CARD_EMPTY; LE_ZERO]];
   ALL_TAC] THEN
  STP_TAC
    `if f k < n then
       (bits_to_num (bsignal sr (t + k)) +
        2 * bits_to_num (bsignal cr (t + k)) + n =
        2 EXP (r + 1) + f k /\
        ~signal dn' (t + k))
     else
       ?s.
         (k - minimal j. n <= f j) = s /\
         (if s <= r then
            (?srs crs crs0.
               bsub sr (s + 1) (r - s) srs /\
               bsub cr s ((r + 1) - s) crs /\
               wire cr s crs0 /\
               bits_to_num (bsignal srs (t + k)) +
               bits_to_num (bsignal crs (t + k)) =
               2 EXP (r - s) /\
               signal crs0 (t + k) /\
               ~signal dn' (t + k))
          else
            signal dn' (t + k))` THENL
  [COND_CASES_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (TAUT `!x y. (x ==> ~y) ==> ~(x /\ y)`) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
       REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD_SUB2; NOT_LE] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(f : num -> num) ((r + 1) + d)` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LE_ADDR];
    ALL_TAC] THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LT]) THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `\j. n <= (f : num -> num) j` MINIMAL) THEN
   REWRITE_TAC [] THEN
   SUBGOAL_THEN
     `(?j. n <= (f : num -> num) j) <=> T`
     SUBST1_TAC THENL
   [REWRITE_TAC [] THEN
    EXISTS_TAC `k : num` THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   SPEC_TAC (`minimal j. n <= (f : num -> num) j`, `j : num`) THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   POP_ASSUM
     (fun th ->
      MP_TAC (SPEC `k : num` th) THEN
      ASM_REWRITE_TAC [NOT_LT] THEN
      ASSUME_TAC th) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   REWRITE_TAC [ADD_SUB2] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   COND_CASES_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (TAUT `!x y. (x ==> ~y) ==> ~(x /\ y)`) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM (SPEC `s : num` LT_ADD_RCANCEL)] THEN
    POP_ASSUM
      (X_CHOOSE_THEN `m : num` SUBST1_TAC o
       REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD_SUB2] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [LT_ADD_RCANCEL] THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC_LE];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_THEN `~(s : num <= r)`
      (X_CHOOSE_THEN `m : num` SUBST_VAR_TAC o
       REWRITE_RULE [NOT_LE; LT_EXISTS]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `r + SUC m = m + (r + 1)` SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD1; ADD_SUC; SUC_INJ] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD1] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADDR; ADD_SUB] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(f : num -> num) j` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LE_ADD]];
   ALL_TAC] THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [DISCH_THEN
     (STRIP_ASSUME_TAC o
      REWRITE_RULE [LE_REFL; ADD_0] o
      SPEC `0`) THEN
   SUBGOAL_THEN `(f : num -> num) 0 = 0` ASSUME_TAC THENL
   [POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LE_ZERO; LT_NZ] THEN
    PURE_REWRITE_TAC [TAUT `!x y. ~x /\ x /\ y <=> F`; GSYM EMPTY] THEN
    REWRITE_TAC [CARD_EMPTY];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [LT_NZ; ADD_0] THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `nb : bus`; `sq : bus`;
         `sr : bus`; `t : num`] bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `bground (r + 1)`; `cq : bus`;
         `cr : bus`; `t : num`] bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `ground`; `dq : wire`;
         `dn' : wire`; `t : num`] case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC
     [ground_signal; bits_to_num_bsignal_bground; MULT_0; ZERO_ADD];
   ALL_TAC] THEN
  POP_ASSUM (fun th ->
    STRIP_TAC THEN
    MP_TAC th) THEN
  ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k : num` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  POP_ASSUM
    (STRIP_ASSUME_TAC o
     REWRITE_RULE [LE_REFL; NOT_SUC] o
     SPEC `SUC k`) THEN
  SUBGOAL_THEN
    `f (SUC k) = f k + if signal inc (t + SUC k) then 1 else 0`
    SUBST1_TAC THENL
  [POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD ({i | 0 < i /\ i <= k /\ signal inc (t + i)} UNION
            (if signal inc (t + SUC k) then {SUC k} else {}))` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION; IN_UNION; IN_ELIM] THEN
    X_GEN_TAC `i : num` THEN
    REWRITE_TAC [CONJUNCT2 LE; LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB] THEN
    CONV_TAC (LAND_CONV (REWR_CONV DISJ_SYM)) THEN
    AP_TERM_TAC THEN
    ASM_CASES_TAC `i = SUC k` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     REWRITE_TAC [LT_NZ; NOT_SUC] THEN
     COND_CASES_TAC THEN
     REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY];
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD {i | 0 < i /\ i <= k /\ signal inc (t + i)} +
      CARD (if signal inc (t + SUC k) then {SUC k} else {})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{ i : num | i <= k }` THEN
     REWRITE_TAC [FINITE_NUMSEG_LE; SUBSET; IN_ELIM] THEN
     REPEAT STRIP_TAC;
     COND_CASES_TAC THEN
     REWRITE_TAC [FINITE_INSERT; FINITE_EMPTY];
     REWRITE_TAC [DISJOINT; EXTENSION; IN_ELIM; NOT_IN_EMPTY; IN_INTER] THEN
     X_GEN_TAC `i : num` THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC [IN_SING] THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [NOT_LE; SUC_LT];
      REWRITE_TAC [NOT_IN_EMPTY]]];
    ALL_TAC] THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [CARD_SING; CARD_EMPTY];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ld : wire`; `nb : bus`; `sq : bus`;
        `sr : bus`; `t + SUC k`] bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`ld : wire`; `bground (r + 1)`; `cq : bus`;
        `cr : bus`; `t + SUC k`] bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`cr : bus`; `r : num`] wire_exists) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [LT_ADD; ONE; LT_0];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `cr2 : wire` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `signal dn' (t + SUC k) <=>
     signal dn' (t + k) \/ signal cr2 (t + k)`
    SUBST1_TAC THENL
  [MP_TAC
     (SPECL
        [`ld : wire`; `ground`; `dq : wire`;
         `dn' : wire`; `t + SUC k`] case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
    (SPECL [`dp : wire`; `cp2 : wire`; `dq : wire`; `t + SUC k`]
       or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUC] THEN
   REWRITE_TAC [ADD1] THEN
   MP_TAC
     (SPECL
        [`dn' : wire`; `dp : wire`; `t + k : num`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
bdelay_bsignal

  COND_CASES_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `signal dn' (t + SUC k) <=> F` SUBST1_TAC THENL
   [


   COND_CASES_TAC THENL
   [
    
NUMSEG_LE; SUBSET; IN_ELIM] THEN

P_TERM_TAC THEN
    REWRITE_TAC [EXTENSION; IN_UNION; IN_ELIM] THEN
    X_GEN_TAC `i : num` THEN
    REWRITE_TAC [CONJUNCT2 LE; LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB] THEN
    CONV_TAC (LAND_CONV (REWR_CONV DISJ_SYM)) THEN
    AP_TERM_TAC THEN
    ASM_CASES_TAC `i = SUC k` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     REWRITE_TAC [LT_NZ; NOT_SUC] THEN
     COND_CASES_TAC THEN
     REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY];
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
   
     

    [
DE_MORGAN_THM]
EXTENSION; IN_UNION; IN_ELIM] THEN

LE_SUC
LE_SIC


   CARD_UNION

  [
  
  COND_CASES_TAC THENL
  [
   
   
   

   SUBGOAL_THEN `(f : num -> num) 0 < n <=> T` SUBST1_TAC THENL
   [REWRITE_TAC [] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [LE_ZERO; LT_NZ] THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LE_ZERO; LT_NZ] THEN
    PURE_REWRITE_TAC [TAUT `!x y. ~x /\ x /\ y <=> F`; GSYM EMPTY] THEN
    REWRITE_TAC [CARD_EMPTY];
    ALL_TAC] THEN
   
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD (EMPTY : num set)` THEN
    REVERSE CONJ_TAC THENL
    [
    REWRITE_TAC [CARD_EMPTY] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) THEN
    
    

  STP_TAC
    `!k f s srs crs crs0.
       (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
       (\j. CARD { i | 0 < i /\ i <= j /\ signal inc (t + i) }) = f /\
       (k - minimal j. f j = n) = s /\
       bsub sr (s + 1) (r - s) srs /\
       bsub cr s ((r + 1) - s) crs /\
       wire cr s crs0 ==>
       if f k < n then
         (bits_to_num (bsignal sr (t + k)) +
          2 * bits_to_num (bsignal cr (t + k)) + n =
          2 EXP (r + 1) + f k /\
          ~signal dn' (t + k))
       else if s <= r then
         (bits_to_num (bsignal srs (t + k)) +
          bits_to_num (bsignal crs (t + k)) =
          2 EXP (r - s) /\
          signal crs0 (t + k) /\
          ~signal dn' (t + k))
       else
         signal dn' (t + k)` THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `?s. (k - minimal j. f j = n) = s /\
     STRIP_ASSUME_TAC THENL
   [MATCH_ACCEPT_TAC EXISTS_REFL';
    ALL_TAC] THEN
   

   FIRST_X_ASSUM (MP_TAC o SPEC_ALL o SPECL [`k : num`; `f : num -> num`]) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   

let counter = prove
 (`!n ld nb dn' t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n + 1 = 2 EXP (width nb) + width nb /\
     counter ld nb dn' ==>
     (signal dn' (t + k) <=> n <= k)`,
  REPEAT STRIP_TAC THEN


(***
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
  [STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [bits_to_num_bsignal_bound
length_bsignal
width_def
***)

  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [counter_def; GSYM RIGHT_EXISTS_AND_THM;
     GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`cr : bus`; `r : num`] wire_exists) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `cr2 : wire` ASSUME_TAC) THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  STP_TAC
    `(!i. i < n ==> ~signal cr2 i) /\ signal cr2 n`

  SUBGOAL_THEN
     `!i.
        i < n ==>
        (bit_cons (~signal cr0 (t + i))
           (bits_to_num (bsignal sr (t + i)) +
            bits_to_num (bsignal cr (t + i))) + n) =
        2 EXP (width nb) + width nb + i` ASSUME_TAC THENL
  [SUBGOAL_THEN `bappend (mk_bus [cr0]) cr1 = cr`
     (SUBST1_TAC o SYM) THENL
   [CONV_TAC (REWR_CONV (GSYM bsub_width)) THEN
    SUBGOAL_THEN `width cr = 1 + r` SUBST1_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT_NZ; ADD_0] THEN
    UNDISCH_THEN
      `bits_to_num (bsignal nb t) + n + 1 = 2 EXP width nb + width nb`
      (SUBST1_TAC o SYM) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [ADD_0; LE_0] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `bground r`; `cq1 : bus`;
          `cr1 : bus`; `t : num`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [bits_to_num_bsignal_bground; bit_cons_zero] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(bits_to_num (bsignal nb t) + 1) + n` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    SUBGOAL_THEN `bappend (mk_bus [nb0]) nb1 = nb`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_width)) THEN
     SUBGOAL_THEN `width nb = 1 + r` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_ACCEPT_TAC ADD_SYM;
      MATCH_MP_TAC bsub_add THEN
      REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb1 : bus`; `sq : bus`;
          `sr : bus`; `t : num`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb0 : wire`; `cq0 : wire`;
          `cr0 : wire`; `t : num`] case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    BOOL_CASES_TAC `signal nb0 t` THEN
    REWRITE_TAC
      [bit_cons_def; ADD_ASSOC; LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL;
       bit_to_num_def; ZERO_ADD; MULT_1; MULT_0; ADD_0] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC [ADD_SUC] THEN
   FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
   [REWRITE_TAC [GSYM LE_SUC_LT] THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM SUC_ADD))) THEN
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   REWRITE_TAC [NOT_SUC]
ADD_0; LE_0] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `bground r`; `cq1 : bus`;
          `cr1 : bus`; `t : num`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [bits_to_num_bsignal_bground; bit_cons_zero] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(bits_to_num (bsignal nb t) + 1) + n` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    SUBGOAL_THEN `bappend (mk_bus [nb0]) nb1 = nb`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_width)) THEN
     SUBGOAL_THEN `width nb = 1 + r` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_ACCEPT_TAC ADD_SYM;
      MATCH_MP_TAC bsub_add THEN
      REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb1 : bus`; `sq : bus`;
          `sr : bus`; `t : num`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb0 : wire`; `cq0 : wire`;
          `cr0 : wire`; `t : num`] case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    BOOL_CASES_TAC `signal nb0 t` THEN
    REWRITE_TAC
      [bit_cons_def; ADD_ASSOC; LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL;
       bit_to_num_def; ZERO_ADD; MULT_1; MULT_0; ADD_0] THEN
    NUM_REDUCE_TAC;

  GEN_TAC THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`nb : bus`, `nb : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`r : num`, `r : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [ZERO_ADD; bsignal_nil; bits_to_num_nil; width_nil; EXP_0; ADD_0]
   ASM_REWRITE_TAC []
bsignal_nil; bits_to_num_nil] THEN
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
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij; bit_cons_def] THEN
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
    `(bit_to_num (signal sh' t) +
      2 * bit_to_num (signal ch' t)) +
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
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
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
   MATCH_MP_TAC adder3 THEN
   ASM_REWRITE_TAC []]);;

export_thm counter;;
***)

logfile_end ();;

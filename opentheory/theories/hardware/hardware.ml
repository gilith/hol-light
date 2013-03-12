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
  let def = new_definition `power = mk_wire (sconstant T)` in
  prove
    (`!t. signal power t = T`,
     REWRITE_TAC [mk_wire_signal; def; snth_sconstant]);;

export_thm power_signal;;

let ground_signal =
  let def = new_definition `ground = mk_wire (sconstant F)` in
  prove
    (`!t. signal ground t = F`,
     REWRITE_TAC [mk_wire_signal; def; snth_sconstant]);;

export_thm ground_signal;;

(* ------------------------------------------------------------------------- *)
(* Primitive wire devices.                                                   *)
(* ------------------------------------------------------------------------- *)

let flipflop_signal =
  let def = new_definition
    `!x y.
       flipflop x y <=>
       !t. signal y (t + 1) = signal x t` in
  prove
  (`!x y.
      flipflop x y ==>
      !t. signal y (t + 1) = signal x t`,
   REWRITE_TAC [def]);;

export_thm flipflop_signal;;

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

let wire_def = new_definition
  `!b i. wire b i = nth (dest_bus b) i`;;

export_thm wire_def;;

let bsignal_def = new_definition
  `!b t. bsignal b t = MAP (\w. signal w t) (dest_bus b)`;;

export_thm bsignal_def;;

(* ------------------------------------------------------------------------- *)
(* Definition of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

let compressor32_def = new_definition
  `!x y z s c.
     compressor32 x y z s c <=>
     ?n.
       width x = n /\ width y = n /\ width z = n /\
       width s = n /\ width c = n /\
       !i.
         i < n ==>
         adder3 (wire x i) (wire y i) (wire z i) (wire s i) (wire c i)`;;

export_thm compressor32_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of bus devices.                                                *)
(* ------------------------------------------------------------------------- *)

(***
let compressor32 = prove
 (`!x y z s c.
     compressor32 x y z s c ==>
     !t.
       bits_to_num (bsignal x t) + bits_to_num (bsignal y t) +
       bits_to_num (bsignal z t) =
       bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor32_def] THEN
  STRIP_TAC THEN
***)

logfile_end ();;

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
(* Why higher order logic is a good formalism for specifying and verifying   *)
(* hardware [1].                                                             *)
(*                                                                           *)
(* 1. http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf                               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Definition of wire devices.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-def";;

(* ------------------------------------------------------------------------- *)
(* Wires.                                                                    *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_wire,dest_mk_wire) =
  CONJ_PAIR (define_newtype ("w","wire") ("s",`:bool stream`));;

export_thm mk_dest_wire;;
export_thm dest_mk_wire;;

let wire_tybij = CONJ mk_dest_wire dest_mk_wire;;

let signal_def = new_definition
  `!w. signal w = snth (dest_wire w)`;;

export_thm signal_def;;

let power_def =
  let def = new_definition `power = mk_wire (sconstant T)` in
  prove
    (`!t. signal power t = T`,
     REWRITE_TAC [signal_def; def; wire_tybij; snth_sconstant]);;

export_thm power_def;;

let ground_def =
  let def = new_definition `ground = mk_wire (sconstant F)` in
  prove
    (`!t. signal ground t = F`,
     REWRITE_TAC [signal_def; def; wire_tybij; snth_sconstant]);;

export_thm ground_def;;

(* ------------------------------------------------------------------------- *)
(* Primitive wire devices.                                                   *)
(* ------------------------------------------------------------------------- *)

let flipflop_def = new_definition
  `!x y.
     flipflop x y <=>
     !t. signal x t = signal y (t + 1)`;;

export_thm flipflop_def;;

let not_def = new_definition
  `!x y.
     not x y <=>
     !t. signal y t = ~signal x t`;;

export_thm not_def;;

let and2_def = new_definition
  `!x1 x2 y.
     and2 x1 x2 y <=>
     !t. signal y t = (signal x1 t /\ signal x2 t)`;;

export_thm and2_def;;

let or2_def = new_definition
  `!x1 x2 y.
     or2 x1 x2 y <=>
     !t. signal y t = (signal x1 t \/ signal x2 t)`;;

export_thm or2_def;;

let xor2_def = new_definition
  `!x1 x2 y.
     xor2 x1 x2 y <=>
     !t. signal y t = ~(signal x1 t = signal x2 t)`;;

export_thm xor2_def;;

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

(***
let xor3 = prove
 (`!x1 x2 x3 y.
     xor3 x1 x2 x3 y <=>
     !t. signal y t = (signal x1 t = (signal x2 t = signal x3 t))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [xor3_def; xor2_def] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   BOOL_CASES_TAC `signal x1 t` THEN
   BOOL_CASES_TAC `signal x2 t` THEN
   REWRITE_TAC [];
   STRIP_TAC THEN
   EXISTS_TAC

export_thm xor3;;
***)

(***
let adder3 = prove
 (`!x y z s c t.
     adder3 x y z s c ==>
     bits_to_num [signal x t] + bits_to_num [signal y t] +
     bits_to_num [signal z t] =
     bits_to_num [signal s t] + 2 * bits_to_num [signal c t]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [adder3_def; bits_to_num_def; MULT_0; ZERO_ADD] THEN
  STRIP_TAC THEN

export_thm adder3;;
***)

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
 (`!x y z s c t.
     compressor32 x y z s c ==>
     bits_to_num (bsignal x t) + bits_to_num (bsignal y t) +
     bits_to_num (bsignal z t) =
     bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [compressor32_def] THEN
  STRIP_TAC THEN
***)

logfile_end ();;

(* ========================================================================= *)
(* HARDWARE VERIFICATION                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for hardware verification.                                *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/montgomery/montgomery.int";;

(* ------------------------------------------------------------------------- *)
(* Why higher order logic is a good formalism for specifying and verifying   *)
(* hardware [1].                                                             *)
(*                                                                           *)
(* 1. http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf                               *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-def";;

let (mk_dest_wire,dest_mk_wire) =
  CONJ_PAIR (define_newtype ("w","wire") ("s",`:bool stream`));;

export_thm mk_dest_wire;;
export_thm dest_mk_wire;;

let wire_tybij = CONJ mk_dest_wire dest_mk_wire;;

let signal_def = new_definition
  `!w. signal w = snth (dest_wire w)`;;

export_thm signal_def;;

(***
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
***)

(* ------------------------------------------------------------------------- *)
(* Basic devices.                                                            *)
(* ------------------------------------------------------------------------- *)

let delay_def = new_definition
  `!x y.
     flipflop x y <=>
     !t. signal x t = signal y (t + 1)`;;

export_thm delay_def;;

let not_def = new_definition
  `!x y.
     not x y <=>
     !t. signal y t = ~signal x t`;;

export_thm notgate_def;;

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
(* Bus devices.                                                              *)
(* ------------------------------------------------------------------------- *)

let compressor32_def = new_definition
  `!x y z s c.
     compressor32 x y z s c <=>
     ?n.
       LENGTH x = n /\
       LENGTH y = n /\
       LENGTH z = n /\
       LENGTH s = n /\
       LENGTH c = n /\
       !i.
         i < n ==>
         adder3 (nth x i) (nth y i) (nth z i) (nth s i) (nth c i)`;;



logfile_end ();;

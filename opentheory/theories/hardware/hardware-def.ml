(* ========================================================================= *)
(* DEFINITION OF THE HARDWARE MODEL                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "hardware-def";;

(* ------------------------------------------------------------------------- *)
(* Wires are streams of signals.                                             *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_wire,dest_mk_wire) =
  CONJ_PAIR (define_newtype ("w","wire") ("s",`:bool stream`));;

export_thm mk_dest_wire;;
export_thm dest_mk_wire;;

let wire_tybij = CONJ mk_dest_wire dest_mk_wire;;

(* ------------------------------------------------------------------------- *)
(* Wires generate signals at each cycle.                                     *)
(* ------------------------------------------------------------------------- *)

let signal_def = new_definition `!w. signal w = snth (dest_wire w)`;;

export_thm signal_def;;

(* ------------------------------------------------------------------------- *)
(* Power and ground wires.                                                   *)
(* ------------------------------------------------------------------------- *)

let ground_def = new_definition `ground = mk_wire (sreplicate F)`;;

export_thm ground_def;;

let power_def = new_definition `power = mk_wire (sreplicate T)`;;

export_thm power_def;;

(* ------------------------------------------------------------------------- *)
(* Buses are lists of wires.                                                 *)
(* ------------------------------------------------------------------------- *)

let (mk_dest_bus,dest_mk_bus) =
  CONJ_PAIR (define_newtype ("x","bus") ("l",`:wire list`));;

export_thm mk_dest_bus;;
export_thm dest_mk_bus;;

let bus_tybij = CONJ mk_dest_bus dest_mk_bus;;

(* ------------------------------------------------------------------------- *)
(* Bus constructors.                                                         *)
(* ------------------------------------------------------------------------- *)

let bnil_def = new_definition
  `bnil = mk_bus []`;;

export_thm bnil_def;;

let bwire_def = new_definition
  `!w. bwire w = mk_bus [w]`;;

export_thm bwire_def;;

let bappend_def = new_definition
  `!x y. bappend x y = mk_bus (APPEND (dest_bus x) (dest_bus y))`;;

export_thm bappend_def;;

(* ------------------------------------------------------------------------- *)
(* Bus widths.                                                               *)
(* ------------------------------------------------------------------------- *)

let width_def = new_definition
  `!x. width x = LENGTH (dest_bus x)`;;

export_thm width_def;;

(* ------------------------------------------------------------------------- *)
(* Buses generate signal lists at each cycle.                                *)
(* ------------------------------------------------------------------------- *)

let bsignal_def = new_definition
  `!x t. bsignal x t = MAP (\w. signal w t) (dest_bus x)`;;

export_thm bsignal_def;;

(* ------------------------------------------------------------------------- *)
(* Sub-buses.                                                                *)
(* ------------------------------------------------------------------------- *)

let bsub_def = new_definition
  `!x k n y.
     bsub x k n y <=>
     k + n <= width x /\
     y = mk_bus (take n (drop k (dest_bus x)))`;;

export_thm bsub_def;;

(* ------------------------------------------------------------------------- *)
(* Power and ground buses.                                                   *)
(* ------------------------------------------------------------------------- *)

let bground_def = new_definition
  `!n. bground n = mk_bus (REPLICATE ground n)`;;

export_thm bground_def;;

let bpower_def = new_definition
  `!n. bpower n = mk_bus (REPLICATE power n)`;;

export_thm bpower_def;;

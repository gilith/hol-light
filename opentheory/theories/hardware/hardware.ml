(* ========================================================================= *)
(* HARDWARE DEVICES                                                          *)
(* Joe Leslie-Hurd                                                           *)
(*                                                                           *)
(* Modelling hardware in higher order logic in the Gordon style [1].         *)
(*                                                                           *)
(* 1. Why higher order logic is a good formalism for specifying and          *)
(*    verifying hardware, http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "stream";
   "natural-bits"];;

needs "opentheory/theories/tools.ml";;
needs "opentheory/theories/natural-bits/natural-bits-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/hardware/hardware.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of the hardware model.                                         *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-def.ml";;

(* ------------------------------------------------------------------------- *)
(* Syntax operations for the hardware model.                                 *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-syntax.ml";;

(* ------------------------------------------------------------------------- *)
(* Properties of the hardware model.                                         *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware wire devices.                                                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-wire.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware bus devices.                                                     *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-bus.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware synthesis.                                                       *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-synthesis.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware adder devices.                                                   *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-adder.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware counter devices.                                                 *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-counter.ml";;

(* ------------------------------------------------------------------------- *)
(* Hardware multiplier devices.                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-multiplier.ml";;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-hol-light-thm";;

export_theory_thm_names "hardware"
  ["hardware-def";
   "hardware-thm";
   "hardware-wire-def";
   "hardware-wire-thm";
   "hardware-bus-def";
   "hardware-bus-thm";
   "hardware-adder-def";
   "hardware-adder-thm";
   "hardware-counter-def";
   "hardware-counter-thm";
   "hardware-multiplier-def";
   "hardware-multiplier-thm"];;

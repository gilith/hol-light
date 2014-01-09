(* ========================================================================= *)
(* HARDWARE DEVICES                                                          *)
(* Joe Leslie-Hurd                                                           *)
(*                                                                           *)
(* Modelling hardware in higher order logic in the Gordon style [1].         *)
(*                                                                           *)
(* 1. "Why higher order logic is a good formalism for specifying and         *)
(*    verifying hardware", http://www.cl.cam.ac.uk/~mjcg/WhyHOL.pdf          *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for hardware devices.                                     *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/hardware/hardware.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of the hardware model.                                         *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-def.ml";;

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

logfile_end ();;

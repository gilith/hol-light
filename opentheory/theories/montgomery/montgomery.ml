(* ========================================================================= *)
(* MONTGOMERY MULTIPLICATION                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "natural-bits";
   "natural-divides";
   "hardware"];;

needs "opentheory/theories/natural-divides/natural-divides-tools.ml";;
needs "opentheory/theories/hardware/hardware-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/montgomery/montgomery.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/montgomery-def.ml";;

(* ------------------------------------------------------------------------- *)
(* Properties of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/montgomery-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of a Montgomery multiplication circuit.                        *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/montgomery-hardware-def.ml";;

(* ------------------------------------------------------------------------- *)
(* Correctness of the Montgomery multiplication circuit.                     *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/montgomery-hardware-thm.ml";;

(* ------------------------------------------------------------------------- *)
(* Automatically synthesizing Montgomery multiplication circuits.            *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/montgomery-hardware-synthesis.ml";;

(* ------------------------------------------------------------------------- *)
(* A Montgomery multiplication circuit to open a crypto timelock.            *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/montgomery/timelock.ml";;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "montgomery-hol-light-thm";;

export_theory_thm_names "montgomery"
  ["montgomery-def";
   "montgomery-thm";
   "montgomery-hardware-def";
   "montgomery-hardware-thm"];;

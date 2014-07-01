(* ========================================================================= *)
(* MONTGOMERY MULTIPLICATION                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Montgomery multiplication.                            *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/montgomery/montgomery.int";;

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

logfile_end ();;

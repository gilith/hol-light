(* ========================================================================= *)
(* PROPERTIES OF THE HARDWARE MODEL                                          *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

logfile "hardware-thm";;

(* ------------------------------------------------------------------------- *)
(* Cycles are the primitive time steps.                                      *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Wires are streams of signals.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Wires generate signals at each cycle.                                     *)
(* ------------------------------------------------------------------------- *)

let mk_wire_signal = prove
 (`!s t. signal (mk_wire s) t = snth s t`,
  REWRITE_TAC [signal_def; wire_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Power and ground wires.                                                   *)
(* ------------------------------------------------------------------------- *)

let ground_signal = prove
 (`!t. ~signal ground t`,
  REWRITE_TAC [ground_def; mk_wire_signal; snth_sreplicate]);;

export_thm ground_signal;;

let power_signal = prove
 (`!t. signal power t`,
  REWRITE_TAC [power_def; mk_wire_signal; snth_sreplicate]);;

export_thm power_signal;;

let bit_to_num_ground = prove
  (`!t. bit_to_num (signal ground t) = 0`,
   REWRITE_TAC [ground_signal; bit_to_num_false]);;

export_thm bit_to_num_ground;;

let bit_to_num_power = prove
  (`!t. bit_to_num (signal power t) = 1`,
   REWRITE_TAC [power_signal; bit_to_num_true]);;

export_thm bit_to_num_power;;

(* ------------------------------------------------------------------------- *)
(* Buses are lists of wires.                                                 *)
(* ------------------------------------------------------------------------- *)

let dest_bus_inj_imp = prove
 (`!x y. dest_bus x = dest_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

let dest_bus_inj = prove
 (`!x y. dest_bus x = dest_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC dest_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

let mk_bus_inj_imp = prove
 (`!x y. mk_bus x = mk_bus y ==> x = y`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM bus_tybij] THEN
  ASM_REWRITE_TAC []);;

let mk_bus_inj = prove
 (`!x y. mk_bus x = mk_bus y <=> x = y`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC mk_bus_inj_imp;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Bus constructors.                                                         *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Bus widths.                                                               *)
(* ------------------------------------------------------------------------- *)

let bnil_width = prove
 (`width bnil = 0`,
  REWRITE_TAC [width_def; bnil_def; bus_tybij; LENGTH_NIL]);;

export_thm bnil_width;;

let bwire_width = prove
 (`!w. width (bwire w) = 1`,
  REWRITE_TAC [width_def; bwire_def; bus_tybij; LENGTH_CONS; LENGTH_NIL; ONE]);;

export_thm bwire_width;;

let width_zero = prove
 (`!x. width x = 0 <=> x = bnil`,
  GEN_TAC THEN
  REWRITE_TAC [width_def; LENGTH_EQ_NIL] THEN
  ONCE_REWRITE_TAC [GSYM dest_bus_inj] THEN
  REWRITE_TAC [bnil_def; bus_tybij]);;

export_thm width_zero;;

(* ------------------------------------------------------------------------- *)
(* Buses generate signal lists at each cycle.                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Sub-buses.                                                                *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Power and ground buses.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile_end ();;

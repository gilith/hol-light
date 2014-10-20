(* ========================================================================= *)
(* A collection of tiny theories to test the opentheory tool.                *)
(*                                                                           *)
(* To use this, comment out everything after loads "equal.ml";; in hol.ml,   *)
(* then launch ocaml and type #use "hol.ml";; #use "opentheory/tiny.ml";;    *)
(* ========================================================================= *)

Export.debug_export_thm_enable := false;;
loads "bool.ml";;
Export.debug_export_thm_enable := true;;

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-true-def";;

export_thm T_DEF;;

logfile "bool-true-thm";;

export_thm TRUTH;;

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-forall-def";;

export_thm FORALL_DEF;;

logfile "bool-forall-thm";;

let FORALL_T = GEN `x:A` TRUTH;;

export_thm FORALL_T;;

(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "bool-and-def";;

export_thm AND_DEF;;

(***
logfile "bool-and-thm";;

let X_AND_T = REWRITE_CONV
GEN `x:bool` TRUTH;;

export_thm FORALL_T;;
***)

(* ------------------------------------------------------------------------- *)
(* Rules for ==>                                                             *)
(* ------------------------------------------------------------------------- *)

logfile "bool-imp-def";;

export_thm IMP_DEF;;

(* ------------------------------------------------------------------------- *)
(* Rules for ?                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-exists-def";;

export_thm EXISTS_DEF;;

(* ------------------------------------------------------------------------- *)
(* Rules for \/                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "bool-or-def";;

export_thm OR_DEF;;

(* ------------------------------------------------------------------------- *)
(* Rules for negation and falsity.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "bool-false-def";;

export_thm F_DEF;;

logfile "bool-not-def";;

export_thm NOT_DEF;;

logfile_end ();;

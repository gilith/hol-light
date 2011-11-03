(* ------------------------------------------------------------------------- *)
(* OpenTheory test theory.                                                   *)
(* ------------------------------------------------------------------------- *)

start_logging ();;

(* ------------------------------------------------------------------------- *)
(* Setup                                                                     *)
(* ------------------------------------------------------------------------- *)

new_constant ("a", `:bool`);;

new_constant ("b", `:bool`);;

let unwanted_id = new_definition
  `unwanted_id = \x. (x : bool)`;;

delete_const_definition ["unwanted_id"];;
delete_proof unwanted_id;;

(* ------------------------------------------------------------------------- *)
(* Testing the argument order of the eqMp command                            *)
(* ------------------------------------------------------------------------- *)

logfile "example5";;

let test_ax1 = new_axiom `a = b`;;

let test_ax2 = new_axiom `a`;;

let test_th = EQ_MP test_ax1 test_ax2;;

export_thm test_th;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Testing the QBF cloud tactic                                              *)
(* ------------------------------------------------------------------------- *)

logfile "qbf";;

let qbf_query = new_axiom `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

export_thm qbf_query;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Testing removal of Unwanted.id constants                                  *)
(* ------------------------------------------------------------------------- *)

(* Clean removal of appTerm *)

logfile "example4";;

let test_ax1 = new_axiom `a = I b`;;

let test_ax2 = new_axiom `a`;;

let test_th = EQ_MP test_ax1 test_ax2;;

export_thm test_th;;

logfile_end ();;

(* Clean removal of appThm *)

logfile "example6";;

let test_ax1 = new_axiom `a <=> b`;;

let test_th1 = REFL `unwanted_id`;;

let test_th2 = MK_COMB (test_th1,test_ax1);;

export_thm test_th2;;

logfile_end ();;

stop_logging ();;

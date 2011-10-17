(* ------------------------------------------------------------------------- *)
(* OpenTheory test theory.                                                   *)
(* ------------------------------------------------------------------------- *)

start_logging ();;

logfile "test";;

(***
new_constant ("a", `:bool`);;

new_constant ("b", `:bool`);;

let test_ax1 = new_axiom `a = b`;;

let test_ax2 = new_axiom `a`;;

let test_th = EQ_MP test_ax1 test_ax2;;

export_thm test_th;;
***)

let qbf_query = new_axiom `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

export_thm qbf_query;;

logfile_end ();;

stop_logging ();;

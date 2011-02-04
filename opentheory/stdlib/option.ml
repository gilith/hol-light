(* ------------------------------------------------------------------------- *)
(* Additions to the standard option theory.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "option-thm";;

let option_distinct = distinctness "option";;

export_thm option_distinct;;

let option_inj = injectivity "option";;

export_thm option_inj;;

let option_cases = prove_cases_thm option_INDUCT;;

export_thm option_cases;;

logfile "option-case";;

let case_option_def = new_recursive_definition option_RECURSION
  `(!b f. case_option b f NONE = (b:B)) /\
   (!b f a. case_option b f (SOME a) = f (a:A))`;;

export_thm case_option_def;;

logfile_end ();;

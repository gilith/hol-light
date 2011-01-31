(* ------------------------------------------------------------------------- *)
(* Additions to the standard library.                                        *)
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
  `(case_option f b NONE = (b:B)) /\
   (case_option f b (SOME a) = f (a:A))`;;

export_thm case_option_def;;

logfile "list-case";;

let case_list_def = new_recursive_definition list_RECURSION
  `(case_list f b [] = (b:B)) /\
   (case_list f b (CONS h t) = f (h:A) t)`;;

export_thm case_list_def;;

logfile_end ();;

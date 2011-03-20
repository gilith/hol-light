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

logfile "option-dest-def";;

let case_option_def = new_recursive_definition option_RECURSION
  `(!b f. case_option b f NONE = (b:B)) /\
   (!b f a. case_option b f (SOME a) = f (a:A))`;;

export_thm case_option_def;;

logfile "option-dest-thm";;

let case_option_id = prove
  (`!(x : A option). case_option NONE SOME x = x`,
   GEN_TAC THEN
   MP_TAC (ISPEC `x : A option` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm case_option_id;;

logfile_end ();;

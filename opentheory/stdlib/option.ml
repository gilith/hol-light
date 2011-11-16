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

let (case_option_none,case_option_some) =
  let def = new_recursive_definition option_RECURSION
    `(!b f. case_option b f NONE = (b:B)) /\
     (!b f a. case_option b f (SOME a) = f (a:A))` in
  CONJ_PAIR def;;

export_thm case_option_none;;
export_thm case_option_some;;

let case_option_def = CONJ case_option_none case_option_some;;

let (is_some_none,is_some_some) =
  let def = new_recursive_definition option_RECURSION
    `(is_some (NONE : A option) <=> F) /\
     (!a. is_some (SOME (a : A)) <=> T)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm is_some_none;;
export_thm is_some_some;;

let is_some_def = CONJ is_some_none is_some_some;;

let (is_none_none,is_none_some) =
  let def = new_recursive_definition option_RECURSION
    `(is_none (NONE : A option) <=> T) /\
     (!a. is_none (SOME (a : A)) <=> F)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm is_none_none;;
export_thm is_none_some;;

let is_none_def = CONJ is_none_none is_none_some;;

logfile "option-dest-thm";;

let case_option_id = prove
  (`!(x : A option). case_option NONE SOME x = x`,
   GEN_TAC THEN
   MP_TAC (ISPEC `x : A option` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm case_option_id;;

logfile_end ();;

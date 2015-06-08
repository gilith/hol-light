(* ========================================================================= *)
(* OPTION TYPES                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for option types.                                         *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/option/option.int";;

(* ------------------------------------------------------------------------- *)
(* Properties of option types.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "option-thm";;

let option_distinct = prove
 (`!(a : A). ~(SOME a = NONE)`,
  MATCH_ACCEPT_TAC (GSYM (prove_constructors_distinct option_RECURSION)));;

export_thm option_distinct;;

let option_inj = prove
 (`!a b : A. SOME a = SOME b <=> a = b`,
  MATCH_ACCEPT_TAC (prove_constructors_injective option_RECURSION));;

export_thm option_inj;;

let option_cases = prove
 (`!x : A option. x = NONE \/ ?a. x = SOME a`,
  MATCH_ACCEPT_TAC (prove_cases_thm option_INDUCT));;

export_thm option_cases;;

let option_cases_tac = CASES_TAC option_cases;;

(* ------------------------------------------------------------------------- *)
(* Definition of option type destructors.                                    *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Properties of option type destructors.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "option-dest-thm";;

let case_option_id = prove
  (`!(x : A option). case_option NONE SOME x = x`,
   GEN_TAC THEN
   MP_TAC (ISPEC `x : A option` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm case_option_id;;

(* ------------------------------------------------------------------------- *)
(* Definition of the option map function.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "option-map-def";;

let (map_option_none,map_option_some) =
  let def = new_recursive_definition option_RECURSION
    `(!(f : A -> B). map_option f NONE = NONE) /\
     (!f a. map_option f (SOME a) = SOME (f a))` in
  CONJ_PAIR def;;

export_thm map_option_none;;
export_thm map_option_some;;

let map_option_def = CONJ map_option_none map_option_some;;

(* ------------------------------------------------------------------------- *)
(* Properties of the option map function.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "option-map-thm";;

let map_option_id = prove
  (`map_option I = (I : A option -> A option)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM] THEN
   X_GEN_TAC `x : A option` THEN
   option_cases_tac `x : A option` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; I_THM]);;

export_thm map_option_id;;

let map_option_o = prove
 (`!(f : B -> C) (g : A -> B) x.
      map_option (f o g) x = map_option f (map_option g x)`,
  REPEAT GEN_TAC THEN
  option_cases_tac `x : A option` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_none];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_some; o_THM]]);;

export_thm map_option_o;;

let map_option_o' = prove
  (`!(f : B -> C) (g : A -> B).
      map_option f o map_option g = map_option (f o g)`,
   REWRITE_TAC [FUN_EQ_THM; map_option_o; o_THM]);;

export_thm map_option_o';;

logfile_end ();;

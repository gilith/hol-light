(* ------------------------------------------------------------------------- *)
(* A functor theory of modular arithmetic.                                   *)
(* ------------------------------------------------------------------------- *)

new_constant ("mod_N", `:num`);;

let mod_N_positive = new_axiom `0 < mod_N`;;

logfile "modular";;

let mod_exists = prove
  (`(\x. x < mod_N) 0`,
   REWRITE_TAC [mod_N_positive]);;

let (mod_abs_rep,mod_rep_abs) = new_basic_type_definition
  "mod" ("mod_from_num","mod_to_num") mod_exists;;

let mod_abs_rep = GEN_ALL mod_abs_rep;;

export_thm mod_abs_rep;;

let mod_rep_abs = GEN_ALL (REWRITE_RULE [] mod_rep_abs);;

export_thm mod_rep_abs;;

logfile_end ();;

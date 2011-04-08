(* ------------------------------------------------------------------------- *)
(* A type of 12-bit words.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "word12-def";;

let word12_width_def = new_definition
  `word12_width = 12`;;

export_thm word12_width_def;;

logfile_end ();;

(* Parametric theory instantiation: word *)

loads "opentheory/examples/word12-word.ml";;

logfile "word12-bits";;

let word12_list_cases = prove_word12_list_cases 12;;

export_thm word12_list_cases;;

logfile_end ();;

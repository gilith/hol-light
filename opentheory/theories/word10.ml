(* ------------------------------------------------------------------------- *)
(* A type of 10-bit words.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "word10-def";;

let word10_width_def = new_definition
  `word10_width = 10`;;

export_thm word10_width_def;;

logfile_end ();;

(* Parametric theory instantiation: word *)

loads "opentheory/theories/word10-word.ml";;

logfile "word10-bits";;

let word10_list_cases = prove_word10_list_cases 10;;

export_thm word10_list_cases;;

logfile_end ();;

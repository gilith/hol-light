(* ========================================================================= *)
(* 12-BIT WORDS                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for 12-bit words.                                         *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/word12/word12.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of 12-bit words.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "word12-def";;

let word12_width_def = new_definition
  `word12_width = 12`;;

export_thm word12_width_def;;

(* Parametric theory instantiation: word *)

loads "opentheory/theories/word12/word12-word.ml";;

(* ------------------------------------------------------------------------- *)
(* 12-bit word to bit-list conversions.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "word12-bits";;

let word12_list_cases = prove_word12_list_cases 12;;

export_thm word12_list_cases;;

logfile_end ();;

(* ========================================================================= *)
(* 10-BIT WORDS                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for 10-bit words.                                         *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/word10/word10.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of 10-bit words.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "word10-def";;

let word10_width_def = new_definition
  `word10_width = 10`;;

export_thm word10_width_def;;

(* Parametric theory instantiation: word *)

loads "opentheory/theories/word10/word10-word.ml";;

(* ------------------------------------------------------------------------- *)
(* 10-bit word to bit-list conversions.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "word10-bits";;

let word10_list_cases = prove_word10_list_cases 10;;

export_thm word10_list_cases;;

logfile_end ();;

(* ========================================================================= *)
(* 12-BIT WORDS                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "probability";
   "natural-bits";
   "natural-divides"];;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/word12/word12.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of 12-bit words.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "word12-def";;

let word12_width_def = new_definition
  `word12_width = 12`;;

export_thm word12_width_def;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "word";
   Import.interpretation = "opentheory/theories/word12/word12-def-word.int";
   Import.theorem_renamer = Import.replace "word" "word12";
   Import.destination_theory = "word12-def"};;

(* Load parametric proof tools *)

loads "opentheory/theories/word12/word12-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* 12-bit word to bit-list conversions.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "word12-bits";;

let word12_list_cases = prove_word12_list_cases 12;;

export_thm word12_list_cases;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "word12-hol-light-thm";;

export_theory_thm_names "word12"
  ["word12-def";
   "word12-bits"];;

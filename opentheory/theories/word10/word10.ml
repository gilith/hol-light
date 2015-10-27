(* ========================================================================= *)
(* 10-BIT WORDS                                                              *)
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

export_interpretation "opentheory/theories/word10/word10.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of 10-bit words.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "word10-def";;

let word10_width_def = new_definition
  `word10_width = 10`;;

export_thm word10_width_def;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "word";
   Import.interpretation = "opentheory/theories/word10/word10-def-word.int";
   Import.theorem_renamer = Import.replace "word" "word10";
   Import.destination_theory = "word10-def"};;

(* Load parametric proof tools *)

loads "opentheory/theories/word10/word10-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* 10-bit word to bit-list conversions.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "word10-bits";;

let word10_list_cases = prove_word10_list_cases 10;;

export_thm word10_list_cases;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "word10-hol-light-thm";;

export_theory_thm_names "word10"
  ["word10-def";
   "word10-bits"];;

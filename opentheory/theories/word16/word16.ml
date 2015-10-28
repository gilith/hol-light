(* ========================================================================= *)
(* 16-BIT WORDS                                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "probability";
   "natural-bits";
   "natural-divides";
   "byte"];;

needs "opentheory/theories/byte/byte-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/word16/word16.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of 16-bit words.                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "word16-def";;

let word16_width_def = new_definition
  `word16_width = 16`;;

export_thm word16_width_def;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "word";
   Import.interpretation = "opentheory/theories/word16/word16-def-word.int";
   Import.theorem_renamer = Import.replace "word" "word16";
   Import.destination_theory = "word16-def"};;

(* Load parametric proof tools *)

loads "opentheory/theories/word16/word16-word-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* 16-bit word to bit-list conversions.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "word16-bits";;

let word16_list_cases = prove_word16_list_cases 16;;

export_thm word16_list_cases;;

(* ------------------------------------------------------------------------- *)
(* Definition of 16-bit word to byte pair conversions.                       *)
(* ------------------------------------------------------------------------- *)

export_theory "word16-bytes-def";;

let word16_to_bytes_def = new_definition
  `!w.
     word16_to_bytes w =
     (num_to_byte (word16_to_num w),
      num_to_byte (word16_to_num (word16_shr w 8)))`;;

export_thm word16_to_bytes_def;;

let bytes_to_word16_def = new_definition
  `!b0 b1.
     bytes_to_word16 b0 b1 =
     word16_or
       (num_to_word16 (byte_to_num b0))
       (word16_shl (num_to_word16 (byte_to_num b1)) 8)`;;

export_thm bytes_to_word16_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of 16-bit word to byte pair conversions.                       *)
(* ------------------------------------------------------------------------- *)

export_theory "word16-bytes-thm";;

let byte_to_word16_list = prove
 (`!b. num_to_word16 (byte_to_num b) = list_to_word16 (byte_to_list b)`,
  REWRITE_TAC
    [list_to_word16_def; byte_to_list_def; num_to_bitvec_to_num;
     bit_bound_byte_to_num]);;

export_thm byte_to_word16_list;;

let word16_to_byte_list = prove
 (`!w. num_to_byte (word16_to_num w) = list_to_byte (word16_to_list w)`,
  REWRITE_TAC
    [word16_to_list_def; list_to_byte_def; num_to_bitvec_to_num;
     bit_bound_word16_to_num]);;

export_thm word16_to_byte_list;;

let bytes_to_word16_list = prove
 (`!b0 b1.
     list_to_word16 (APPEND (byte_to_list b0) (byte_to_list b1)) =
     bytes_to_word16 b0 b1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bytes_to_word16_def; byte_to_word16_list] THEN
  MP_TAC (SPEC `b0 : byte` byte_list_cases) THEN
  STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
  STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  bit_blast_tac);;

export_thm bytes_to_word16_list;;

let word16_to_bytes_list = prove
 (`!w.
     (list_to_byte (take 8 (word16_to_list w)),
      list_to_byte (drop 8 (word16_to_list w))) =
     word16_to_bytes w`,
  GEN_TAC THEN
  REWRITE_TAC [word16_to_bytes_def; word16_to_byte_list; PAIR_EQ] THEN
  MP_TAC (SPEC `w : word16` word16_list_cases) THEN
  STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  bit_blast_tac);;

export_thm word16_to_bytes_list;;

let dest_bytes_to_word16_cases = prove
 (`!w. ?b0 b1. w = bytes_to_word16 b0 b1 /\ word16_to_bytes w = (b0,b1)`,
  GEN_TAC THEN
  EXISTS_TAC `FST (word16_to_bytes w)` THEN
  EXISTS_TAC `SND (word16_to_bytes w)` THEN
  REWRITE_TAC [] THEN
  REWRITE_TAC [word16_to_bytes_def; bytes_to_word16_def] THEN
  REWRITE_TAC [byte_to_word16_list; word16_to_byte_list] THEN
  MP_TAC (SPEC `w : word16` word16_list_cases) THEN
  STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  bit_blast_tac THEN
  REWRITE_TAC []);;

export_thm dest_bytes_to_word16_cases;;

let bytes_to_word16_cases = prove
 (`!w. ?b0 b1. w = bytes_to_word16 b0 b1`,
  GEN_TAC THEN
  MP_TAC (SPEC `w : word16` dest_bytes_to_word16_cases) THEN
  STRIP_TAC THEN
  EXISTS_TAC `b0 : byte` THEN
  EXISTS_TAC `b1 : byte` THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm bytes_to_word16_cases;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "word16-hol-light-thm";;

export_theory_thm_names "word16"
  ["word16-def";
   "word16-bits";
   "word16-bytes-def";
   "word16-bytes-thm"];;

(* ------------------------------------------------------------------------- *)
(* Proof tools for 16-bit words.                                             *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/word16/word16-tools.ml";;

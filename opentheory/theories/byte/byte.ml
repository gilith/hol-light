(* ========================================================================= *)
(* BYTES                                                                     *)
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

export_interpretation "opentheory/theories/byte/byte.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of bytes.                                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "byte-def";;

let byte_width_def = new_definition
  `byte_width = 8`;;

export_thm byte_width_def;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "word";
   Import.interpretation = "opentheory/theories/byte/byte-def-word.int";
   Import.theorem_renamer = Import.replace "word" "byte";
   Import.destination_theory = "byte-def"};;

(* Load parametric proof tools *)

loads "opentheory/theories/byte/byte-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Byte to bit-list conversions.                                             *)
(* ------------------------------------------------------------------------- *)

export_theory "byte-bits";;

let byte_list_cases = prove
  (`!b. ?x0 x1 x2 x3 x4 x5 x6 x7.
      b = list_to_byte [x0; x1; x2; x3; x4; x5; x6; x7]`,
   GEN_TAC THEN
   CONV_TAC (funpow 8 (RAND_CONV o ABS_CONV)
               (LAND_CONV (ONCE_REWRITE_CONV [GSYM byte_to_list_to_byte]))) THEN
   KNOW_TAC
     `LENGTH (byte_to_list b) =
      SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))` THENL
   [REWRITE_TAC [length_byte_to_list; byte_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   SPEC_TAC (`byte_to_list b`, `l : bool list`) THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `HD (l : bool list)` THEN
   EXISTS_TAC `HD (TL (l : bool list))` THEN
   EXISTS_TAC `HD (TL (TL (l : bool list)))` THEN
   EXISTS_TAC `HD (TL (TL (TL (l : bool list))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (l : bool list)))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (l : bool list))))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (TL (l : bool list)))))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (TL (TL (l : bool list))))))))` THEN
   AP_TERM_TAC THEN
   POP_ASSUM MP_TAC THEN
   N_TAC 8
     (MP_TAC (ISPEC `l : bool list` list_cases) THEN
      STRIP_TAC THENL
      [ASM_REWRITE_TAC [LENGTH; NOT_SUC];
       ALL_TAC] THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      REWRITE_TAC [LENGTH; SUC_INJ; HD; TL; CONS_11] THEN
      SPEC_TAC (`t : bool list`, `l : bool list`) THEN
      GEN_TAC) THEN
   REWRITE_TAC [LENGTH_EQ_NIL]);;

export_thm byte_list_cases;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "byte-hol-light-thm";;

export_theory_thm_names "byte"
  ["byte-def";
   "byte-bits"];;

(* ------------------------------------------------------------------------- *)
(* Haskell source.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "byte-haskell-src";;

export_thm byte_width_def;;  (* Haskell *)
export_thm byte_size_def;;  (* Haskell *)
export_thm random_byte_def;;  (* Haskell *)

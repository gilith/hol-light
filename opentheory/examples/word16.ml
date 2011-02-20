(* ------------------------------------------------------------------------- *)
(* A type of 16-bit words.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "word16-def";;

let word16_width_def = new_definition
  `word16_width = 16`;;

export_thm word16_width_def;;

logfile_end ();;

(* Parametric theory instantiation: word *)

loads "opentheory/examples/word16-word.ml";;

logfile "word16-bytes-def";;

let word16_to_bytes_def = new_definition
  `!w.
     word16_to_bytes w =
     (num_to_byte (word16_to_num (word16_shr w 8)),
      num_to_byte (word16_to_num (word16_and w (num_to_word16 255))))`;;

export_thm word16_to_bytes_def;;

let bytes_to_word16_def = new_definition
  `!b1 b2.
     bytes_to_word16 b1 b2 =
     word16_or
       (word16_shl (num_to_word16 (byte_to_num b1)) 8)
       (num_to_word16 (byte_to_num b2))`;;

export_thm bytes_to_word16_def;;

logfile "word16-bytes-thm";;

(***
let byte_to_word16_list = prove
  (`!b. num_to_word16 (byte_to_num b) = list_to_word16 (byte_to_list b)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (word16_to_bytes w)` THEN
   EXISTS_TAC `SND (word16_to_bytes w)` THEN
   REWRITE_TAC [] THEN
   REWRITE_TAC [word16_to_bytes_def; bytes_to_word16_def] THEN
   REWRITE_TAC [num_to_byte_to_num; word16_to_num_to_word16]

let word16_to_byte_list = prove
  (`!w. num_to_byte (word16_to_num b) = list_to_byte (word16_to_list w)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (word16_to_bytes w)` THEN
   EXISTS_TAC `SND (word16_to_bytes w)` THEN
   REWRITE_TAC [] THEN
   REWRITE_TAC [word16_to_bytes_def; bytes_to_word16_def] THEN
   REWRITE_TAC [num_to_byte_to_num; word16_to_num_to_word16]

let dest_bytes_to_word16_cases = prove
  (`!w. ?b0 b1. w = bytes_to_word16 b0 b1 /\ word16_to_bytes w = (b0,b1)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (word16_to_bytes w)` THEN
   EXISTS_TAC `SND (word16_to_bytes w)` THEN
   REWRITE_TAC [] THEN
   REWRITE_TAC [word16_to_bytes_def; bytes_to_word16_def] THEN
   REWRITE_TAC [num_to_byte_to_num; word16_to_num_to_word16]

export_thm dest_bytes_to_word16_cases;;

let bytes_to_word16_cases = prove
  (`!w. ?b0 b1. w = bytes_to_word16 b0 b1`,

export_thm bytes_to_word16_cases;;
***)

logfile_end ();;


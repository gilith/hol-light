(* ------------------------------------------------------------------------- *)
(* A type of bytes.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "byte-def";;

let byte_width_def = new_definition
  `byte_width = 8`;;

export_thm byte_width_def;;

logfile_end ();;

(* Parametric theory instantiation: word *)

loads "opentheory/examples/byte-word.ml";;

(* A reduction conversion *)

let byte_reduce_conv =
    REWRITE_CONV
      [byte_to_num_to_byte;
       byte_le_def; byte_lt_def] THENC
    REWRITE_CONV
      [num_to_byte_to_num] THENC
    REWRITE_CONV
      [byte_width_def; byte_size_def; num_to_byte_eq] THENC
    NUM_REDUCE_CONV;;

logfile_end ();;

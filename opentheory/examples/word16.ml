(* ------------------------------------------------------------------------- *)
(* A type of 16-bit words.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "word16-def";;

let word16_width_def = new_definition
  `word16_width = 16`;;

export_thm word16_width_def;;

logfile_end ();;

(* Apply theory functor word *)

new_type ("word16",0);;

new_constant ("word16_add", `:word16 -> word16 -> word16`);;
new_constant ("word16_mult", `:word16 -> word16 -> word16`);;
new_constant ("word16_neg", `:word16 -> word16`);;
new_constant ("word16_sub", `:word16 -> word16 -> word16`);;
new_constant ("word16_le", `:word16 -> word16 -> bool`);;
new_constant ("word16_lt", `:word16 -> word16 -> bool`);;
new_constant ("word16_and", `:word16 -> word16 -> word16`);;
new_constant ("word16_bit", `:word16 -> num -> bool`);;
new_constant ("list_to_word16", `:bool list -> word16`);;
new_constant ("num_to_word16", `:num -> word16`);;
new_constant ("word16_not", `:word16 -> word16`);;
new_constant ("word16_or", `:word16 -> word16 -> word16`);;
new_constant ("word16_shl", `:word16 -> num -> word16`);;
new_constant ("word16_shr", `:word16 -> num -> word16`);;
new_constant ("word16_size", `:num`);;
new_constant ("word16_to_list", `:word16 -> bool list`);;
new_constant ("word16_to_num", `:word16 -> num`);;

logfile "word16-bytes";;

let word16_to_bytes_def = new_definition
  `word16_to_bytes w =
     (num_to_byte (word16_to_num (word16_shr w 8)),
      num_to_byte (word16_to_num (word16_and w (num_to_word16 255))))`;;

export_thm word16_to_bytes_def;;

let bytes_to_word16_def = new_definition
  `bytes_to_word16 b1 b2 =
     word16_or
       (word16_shl (num_to_word16 (byte_to_num b1)) 8)
       (num_to_word16 (byte_to_num b2))`;;

export_thm bytes_to_word16_def;;

logfile_end ();;


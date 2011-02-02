(* ------------------------------------------------------------------------- *)
(* A type of bytes.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "byte-def";;

let byte_width_def = new_definition
  `byte_width = 8`;;

export_thm byte_width_def;;

logfile_end ();;

(* Apply theory functor word *)

new_type ("byte",0);;

new_constant ("byte_add", `:byte -> byte -> byte`);;
new_constant ("byte_mult", `:byte -> byte -> byte`);;
new_constant ("byte_neg", `:byte -> byte`);;
new_constant ("byte_sub", `:byte -> byte -> byte`);;
new_constant ("byte_le", `:byte -> byte -> bool`);;
new_constant ("byte_lt", `:byte -> byte -> bool`);;
new_constant ("byte_and", `:byte -> byte -> byte`);;
new_constant ("byte_bit", `:byte -> num -> bool`);;
new_constant ("list_to_byte", `:bool list -> byte`);;
new_constant ("num_to_byte", `:num -> byte`);;
new_constant ("byte_not", `:byte -> byte`);;
new_constant ("byte_or", `:byte -> byte -> byte`);;
new_constant ("byte_shl", `:byte -> num -> byte`);;
new_constant ("byte_shr", `:byte -> num -> byte`);;
new_constant ("byte_size", `:num`);;
new_constant ("byte_to_list", `:byte -> bool list`);;
new_constant ("byte_to_num", `:byte -> num`);;

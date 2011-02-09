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

let byte_size_def = new_axiom
  `byte_size = 2 EXP byte_width`;;

let byte_size_nonzero = new_axiom
  `~(byte_size = 0)`;;

let byte_to_num_to_byte = new_axiom
  `!x. num_to_byte (byte_to_num x) = x`;;

let num_to_byte_inj = new_axiom
  `!x y. x < byte_size /\ y < byte_size /\ num_to_byte x = num_to_byte y ==> x = y`;;

let num_to_byte_to_num = new_axiom
  `!x. byte_to_num (num_to_byte x) = x MOD byte_size`;;

let num_to_byte_add = new_axiom
  `!x1 y1. num_to_byte (x1 + y1) = byte_add (num_to_byte x1) (num_to_byte y1)`;;

let num_to_byte_mult = new_axiom
  `!x1 y1. num_to_byte (x1 * y1) = byte_mult (num_to_byte x1) (num_to_byte y1)`;;

let byte_neg_def = new_axiom
  `!x. byte_neg x = num_to_byte (byte_size - byte_to_num x)`;;

let byte_sub_def = new_axiom
  `!x y. byte_sub x y = byte_add x (byte_neg y)`;;

let byte_le_def = new_axiom
  `!x y. byte_le x y = byte_to_num x <= byte_to_num y`;;

let byte_lt_def = new_axiom
  `!x y. byte_lt x y = ~(byte_le y x)`;;

let byte_to_num_inj = new_axiom
  `!x y. byte_to_num x = byte_to_num y ==> x = y`;;

let num_to_byte_eq = new_axiom
  `!x y. num_to_byte x = num_to_byte y <=> x MOD byte_size = y MOD byte_size`;;

let byte_to_num_bound = new_axiom
  `!x. byte_to_num x < byte_size`;;

let byte_shl_def = new_axiom
 `!w n. byte_shl w n = num_to_byte (byte_to_num w * (2 EXP n))`;;

let byte_shr_def = new_axiom
 `!w n. byte_shr w n = num_to_byte (byte_to_num w DIV (2 EXP n))`;;

let byte_bit_def = new_axiom
 `!w n. byte_bit w n = ODD (byte_to_num (byte_shr w n))`;;

let byte_to_list_def = new_axiom
 `!w. byte_to_list w = MAP (byte_bit w) (interval 0 byte_width)`;;

let list_to_byte_def = new_axiom
  `(list_to_byte [] = num_to_byte 0) /\
   (!h t.
      list_to_byte (CONS h t) =
      if h then byte_add (byte_shl (list_to_byte t) 1) (num_to_byte 1)
      else byte_shl (list_to_byte t) 1)`;;

let byte_and_def = new_axiom
  `!w1 w2.
     byte_and w1 w2 =
     list_to_byte (zipwith ( /\ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_or_def = new_axiom
  `!w1 w2.
     byte_or w1 w2 =
     list_to_byte (zipwith ( \/ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_not_def = new_axiom
  `!w. byte_not w = list_to_byte (MAP (~) (byte_to_list w))`;;

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

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

let word16_size_def = new_axiom
  `word16_size = 2 EXP word16_width`;;

let word16_size_nonzero = new_axiom
  `~(word16_size = 0)`;;

let word16_to_num_to_word16 = new_axiom
  `!x. num_to_word16 (word16_to_num x) = x`;;

let num_to_word16_inj = new_axiom
  `!x y. x < word16_size /\ y < word16_size /\ num_to_word16 x = num_to_word16 y ==> x = y`;;

let num_to_word16_to_num = new_axiom
  `!x. word16_to_num (num_to_word16 x) = x MOD word16_size`;;

let num_to_word16_add = new_axiom
  `!x1 y1. num_to_word16 (x1 + y1) = word16_add (num_to_word16 x1) (num_to_word16 y1)`;;

let num_to_word16_mult = new_axiom
  `!x1 y1. num_to_word16 (x1 * y1) = word16_mult (num_to_word16 x1) (num_to_word16 y1)`;;

let word16_neg_def = new_axiom
  `!x. word16_neg x = num_to_word16 (word16_size - word16_to_num x)`;;

let word16_sub_def = new_axiom
  `!x y. word16_sub x y = word16_add x (word16_neg y)`;;

let word16_le_def = new_axiom
  `!x y. word16_le x y = word16_to_num x <= word16_to_num y`;;

let word16_lt_def = new_axiom
  `!x y. word16_lt x y = ~(word16_le y x)`;;

let word16_to_num_inj = new_axiom
  `!x y. word16_to_num x = word16_to_num y ==> x = y`;;

let num_to_word16_eq = new_axiom
  `!x y. num_to_word16 x = num_to_word16 y <=> x MOD word16_size = y MOD word16_size`;;

let word16_shl_def = new_axiom
 `!w n. word16_shl w n = num_to_word16 (word16_to_num w * (2 EXP n))`;;

let word16_shr_def = new_axiom
 `!w n. word16_shr w n = num_to_word16 (word16_to_num w DIV (2 EXP n))`;;

let word16_bit_def = new_axiom
 `!w n. word16_bit w n = ODD (word16_to_num (word16_shr w n))`;;

let word16_to_list_def = new_axiom
 `!w. word16_to_list w = MAP (word16_bit w) (interval 0 word16_width)`;;

let list_to_word16_def = new_axiom
  `(list_to_word16 [] = num_to_word16 0) /\
   (!h t.
      list_to_word16 (CONS h t) =
      if h then word16_add (word16_shl (list_to_word16 t) 1) (num_to_word16 1)
      else word16_shl (list_to_word16 t) 1)`;;

let word16_and_def = new_axiom
  `!w1 w2.
     word16_and w1 w2 =
     list_to_word16 (zipwith ( /\ ) (word16_to_list w1) (word16_to_list w2))`;;

let word16_or_def = new_axiom
  `!w1 w2.
     word16_or w1 w2 =
     list_to_word16 (zipwith ( \/ ) (word16_to_list w1) (word16_to_list w2))`;;

let word16_not_def = new_axiom
  `!w. word16_not w = list_to_word16 (MAP (~) (word16_to_list w))`;;

logfile "word16-bytes";;

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

logfile_end ();;


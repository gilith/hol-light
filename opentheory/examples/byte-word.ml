(* byte *)

(* byte-def *)

new_constant ("byte_size", `:num`);;

let byte_size_def = new_axiom
  `byte_size = 2 EXP byte_width`;;

let byte_size_nonzero = new_axiom
  `~(byte_size = 0)`;;

(* byte *)

(* byte-mod *)

let mod_lt_byte_size = new_axiom
  `!n. n < byte_size ==> n MOD byte_size = n`;;

let lt_mod_byte_size = new_axiom
  `!n. n MOD byte_size < byte_size`;;

let mod_mod_refl_byte_size = new_axiom
  `!n. n MOD byte_size MOD byte_size = n MOD byte_size`;;

let mod_add_mod_byte_size = new_axiom
  `!m n. (m MOD byte_size + n MOD byte_size) MOD byte_size = (m + n) MOD byte_size`;;

let mod_mult_mod2_byte_size = new_axiom
  `!m n. (m MOD byte_size * n MOD byte_size) MOD byte_size = (m * n) MOD byte_size`;;

(* byte-def *)

new_type ("byte",0);;

new_constant ("num_to_byte", `:num -> byte`);;

new_constant ("byte_to_num", `:byte -> num`);;

let byte_to_num_to_byte = new_axiom
  `!x. num_to_byte (byte_to_num x) = x`;;

let num_to_byte_inj = new_axiom
   `!x y.
      x < byte_size /\ y < byte_size /\ num_to_byte x = num_to_byte y ==>
      x = y`;;

let num_to_byte_to_num = new_axiom
  `!x. byte_to_num (num_to_byte x) = x MOD byte_size`;;

new_constant ("byte_add", `:byte -> byte -> byte`);;

let num_to_byte_add = new_axiom
  `!x1 y1.
     num_to_byte (x1 + y1) =
     byte_add (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_mult", `:byte -> byte -> byte`);;

let num_to_byte_mult = new_axiom
  `!x1 y1.
     num_to_byte (x1 * y1) =
     byte_mult (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_neg", `:byte -> byte`);;

let byte_neg_def = new_axiom
  `!x. byte_neg x = num_to_byte (byte_size - byte_to_num x)`;;

new_constant ("byte_sub", `:byte -> byte -> byte`);;

let byte_sub_def = new_axiom
  `!x y. byte_sub x y = byte_add x (byte_neg y)`;;

new_constant ("byte_le", `:byte -> byte -> bool`);;

let byte_le_def = new_axiom
  `!x y. byte_le x y = byte_to_num x <= byte_to_num y`;;

new_constant ("byte_lt", `:byte -> byte -> bool`);;

let byte_lt_def = new_axiom
  `!x y. byte_lt x y = ~(byte_le y x)`;;

(* byte-thm *)

let byte_to_num_inj = new_axiom
  `!x y. byte_to_num x = byte_to_num y ==> x = y`;;

let num_to_byte_eq = new_axiom
   `!x y.
      num_to_byte x = num_to_byte y <=> x MOD byte_size = y MOD byte_size`;;

let byte_to_num_bound = new_axiom
  `!x. byte_to_num x < byte_size`;;

let byte_to_num_div_bound = new_axiom
  `!x. byte_to_num x DIV byte_size = 0`;;

let byte_add_to_num = new_axiom
   `!x y.
      byte_to_num (byte_add x y) =
      (byte_to_num x + byte_to_num y) MOD byte_size`;;

(* byte-bits-def *)

new_constant ("byte_shl", `:byte -> num -> byte`);;

let byte_shl_def = new_axiom
  `!w n. byte_shl w n = num_to_byte ((2 EXP n) * byte_to_num w)`;;

new_constant ("byte_shr", `:byte -> num -> byte`);;

let byte_shr_def = new_axiom
  `!w n. byte_shr w n = num_to_byte (byte_to_num w DIV (2 EXP n))`;;

new_constant ("byte_bit", `:byte -> num -> bool`);;

let byte_bit_def = new_axiom
  `!w n. byte_bit w n = ODD (byte_to_num (byte_shr w n))`;;

new_constant ("byte_to_list", `:byte -> bool list`);;

let byte_to_list_def = new_axiom
  `!w. byte_to_list w = MAP (byte_bit w) (interval 0 byte_width)`;;

new_constant ("list_to_byte", `:bool list -> byte`);;

let list_to_byte_def = new_axiom
  `(list_to_byte [] = num_to_byte 0) /\
   (!h t.
      list_to_byte (CONS h t) =
      if h then byte_add (byte_shl (list_to_byte t) 1) (num_to_byte 1)
      else byte_shl (list_to_byte t) 1)`;;

new_constant ("is_byte_list", `:bool list -> bool`);;

let is_byte_list_def = new_axiom
  `!l. is_byte_list (l : bool list) <=> LENGTH l = byte_width`;;

new_constant ("byte_and", `:byte -> byte -> byte`);;

let byte_and_def = new_axiom
  `!w1 w2.
     byte_and w1 w2 =
     list_to_byte (zipwith ( /\ ) (byte_to_list w1) (byte_to_list w2))`;;

new_constant ("byte_or", `:byte -> byte -> byte`);;

let byte_or_def = new_axiom
  `!w1 w2.
     byte_or w1 w2 =
     list_to_byte (zipwith ( \/ ) (byte_to_list w1) (byte_to_list w2))`;;

new_constant ("byte_not", `:byte -> byte`);;

let byte_not_def = new_axiom
  `!w. byte_not w = list_to_byte (MAP (~) (byte_to_list w))`;;

(* byte-bits-thm *)

let length_byte_to_list = new_axiom
  `!w. LENGTH (byte_to_list w) = byte_width`;;

let is_byte_to_list = new_axiom
  `!w. is_byte_list (byte_to_list w)`;;

let byte_bit_div = new_axiom
  `!w n. byte_bit w n = ODD (byte_to_num w DIV (2 EXP n))`;;

let nil_to_byte_to_num = new_axiom
  `byte_to_num (list_to_byte []) = 0`;;

let cons_to_byte_to_num = new_axiom
   `!h t.
      byte_to_num (list_to_byte (CONS h t)) =
      (2 * byte_to_num (list_to_byte t) + (if h then 1 else 0)) MOD byte_size`;;

let list_to_byte_to_num_bound = new_axiom
  `!l. byte_to_num (list_to_byte l) < 2 EXP (LENGTH l)`;;

let list_to_byte_to_num_bound_suc = new_axiom
  `!l. 2 * byte_to_num (list_to_byte l) + 1 < 2 EXP (SUC (LENGTH l))`;;

let cons_to_byte_to_num_bound = new_axiom
   `!h t.
      2 * byte_to_num (list_to_byte t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`;;

let byte_to_list_to_byte = new_axiom
  `!w. list_to_byte (byte_to_list w) = w`;;

let byte_to_list_inj = new_axiom
  `!w1 w2. byte_to_list w1 = byte_to_list w2 ==> w1 = w2`;;

let list_to_byte_bit = new_axiom
   `!l n.
      byte_bit (list_to_byte l) n =
      (n < byte_width /\ n < LENGTH l /\ EL n l)`;;

let short_list_to_byte_to_list = new_axiom
   `!l.
      LENGTH l <= byte_width ==>
      byte_to_list (list_to_byte l) =
      APPEND l (REPLICATE (byte_width - LENGTH l) F)`;;

let long_list_to_byte_to_list = new_axiom
   `!l.
      byte_width <= LENGTH l ==>
      byte_to_list (list_to_byte l) = take byte_width l`;;

let list_to_byte_to_list_eq = new_axiom
   `!l.
      byte_to_list (list_to_byte l) =
      if LENGTH l <= byte_width then
        APPEND l (REPLICATE (byte_width - LENGTH l) F)
      else
        take byte_width l`;;

let list_to_byte_to_list = new_axiom
  `!l. LENGTH l = byte_width <=> byte_to_list (list_to_byte l) = l`;;

let byte_shl_list = new_axiom
   `!l n.
      byte_shl (list_to_byte l) n =
      list_to_byte (APPEND (REPLICATE n F) l)`;;

let short_byte_shr_list = new_axiom
   `!l n.
      LENGTH l <= byte_width ==>
      byte_shr (list_to_byte l) n =
      (if LENGTH l <= n then list_to_byte []
       else list_to_byte (drop n l))`;;

let long_byte_shr_list = new_axiom
   `!l n.
      byte_width <= LENGTH l ==>
      byte_shr (list_to_byte l) n =
      if byte_width <= n then list_to_byte []
      else list_to_byte (drop n (take byte_width l))`;;

let byte_shr_list = new_axiom
   `!l n.
      byte_shr (list_to_byte l) n =
      (if LENGTH l <= byte_width then
         if LENGTH l <= n then list_to_byte []
         else list_to_byte (drop n l)
       else
         if byte_width <= n then list_to_byte []
         else list_to_byte (drop n (take byte_width l)))`;;

let byte_eq_bits = new_axiom
  `!w1 w2. (!i. i < byte_width ==> byte_bit w1 i = byte_bit w2 i) ==> w1 = w2`;;

(* word *)

(* word-mod *)

let mod_lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let lt_mod_word_size = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_refl_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let mod_add_mod_word_size = new_axiom
  `!m n. (m MOD word_size + n MOD word_size) MOD word_size = (m + n) MOD word_size`;;

let mod_mult_mod2_word_size = new_axiom
  `!m n. (m MOD word_size * n MOD word_size) MOD word_size = (m * n) MOD word_size`;;

(* word-def *)

new_type ("word",0);;

new_constant ("num_to_word", `:num -> word`);;

new_constant ("word_to_num", `:word -> num`);;

let word_to_num_to_word = new_axiom
  `!x. num_to_word (word_to_num x) = x`;;

let num_to_word_inj = new_axiom
   `!x y.
      x < word_size /\ y < word_size /\ num_to_word x = num_to_word y ==>
      x = y`;;

let num_to_word_to_num = new_axiom
  `!x. word_to_num (num_to_word x) = x MOD word_size`;;

new_constant ("word_add", `:word -> word -> word`);;

let num_to_word_add = new_axiom
  `!x1 y1.
     num_to_word (x1 + y1) =
     word_add (num_to_word x1) (num_to_word y1)`;;

new_constant ("word_mult", `:word -> word -> word`);;

let num_to_word_mult = new_axiom
  `!x1 y1.
     num_to_word (x1 * y1) =
     word_mult (num_to_word x1) (num_to_word y1)`;;

new_constant ("word_neg", `:word -> word`);;

let word_neg_def = new_axiom
  `!x. word_neg x = num_to_word (word_size - word_to_num x)`;;

new_constant ("word_sub", `:word -> word -> word`);;

let word_sub_def = new_axiom
  `!x y. word_sub x y = word_add x (word_neg y)`;;

new_constant ("word_le", `:word -> word -> bool`);;

let word_le_def = new_axiom
  `!x y. word_le x y = word_to_num x <= word_to_num y`;;

new_constant ("word_lt", `:word -> word -> bool`);;

let word_lt_def = new_axiom
  `!x y. word_lt x y = ~(word_le y x)`;;

(* word-thm *)

let word_to_num_inj = new_axiom
  `!x y. word_to_num x = word_to_num y ==> x = y`;;

let num_to_word_eq = new_axiom
   `!x y.
      num_to_word x = num_to_word y <=> x MOD word_size = y MOD word_size`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_add_to_num = new_axiom
   `!x y.
      word_to_num (word_add x y) =
      (word_to_num x + word_to_num y) MOD word_size`;;

let word_lt_alt = new_axiom
   `!x y. word_lt x y = word_to_num x < word_to_num y`;;

(*PARAMETRIC
(* word *)

(* word-mod *)

let mod_lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let lt_mod_word_size = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_refl_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let mod_add_mod_word_size = new_axiom
  `!m n. (m MOD word_size + n MOD word_size) MOD word_size = (m + n) MOD word_size`;;

let mod_mult_mod2_word_size = new_axiom
  `!m n. (m MOD word_size * n MOD word_size) MOD word_size = (m * n) MOD word_size`;;

(* word-def *)

new_type ("word",0);;

new_constant ("num_to_word", `:num -> word`);;

new_constant ("word_to_num", `:word -> num`);;

let word_to_num_to_word = new_axiom
  `!x. num_to_word (word_to_num x) = x`;;

let num_to_word_inj = new_axiom
   `!x y.
      x < word_size /\ y < word_size /\ num_to_word x = num_to_word y ==>
      x = y`;;

let num_to_word_to_num = new_axiom
  `!x. word_to_num (num_to_word x) = x MOD word_size`;;

new_constant ("word_add", `:word -> word -> word`);;

let num_to_word_add = new_axiom
  `!x1 y1.
     num_to_word (x1 + y1) =
     word_add (num_to_word x1) (num_to_word y1)`;;

new_constant ("word_mult", `:word -> word -> word`);;

let num_to_word_mult = new_axiom
  `!x1 y1.
     num_to_word (x1 * y1) =
     word_mult (num_to_word x1) (num_to_word y1)`;;

new_constant ("word_neg", `:word -> word`);;

let word_neg_def = new_axiom
  `!x. word_neg x = num_to_word (word_size - word_to_num x)`;;

new_constant ("word_sub", `:word -> word -> word`);;

let word_sub_def = new_axiom
  `!x y. word_sub x y = word_add x (word_neg y)`;;

new_constant ("word_le", `:word -> word -> bool`);;

let word_le_def = new_axiom
  `!x y. word_le x y = word_to_num x <= word_to_num y`;;

new_constant ("word_lt", `:word -> word -> bool`);;

let word_lt_def = new_axiom
  `!x y. word_lt x y = ~(word_le y x)`;;

(* word-thm *)

let word_to_num_inj = new_axiom
  `!x y. word_to_num x = word_to_num y ==> x = y`;;

let num_to_word_eq = new_axiom
   `!x y.
      num_to_word x = num_to_word y <=> x MOD word_size = y MOD word_size`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_add_to_num = new_axiom
   `!x y.
      word_to_num (word_add x y) =
      (word_to_num x + word_to_num y) MOD word_size`;;

let word_lt_alt = new_axiom
   `!x y. word_lt x y = word_to_num x < word_to_num y`;;
*)

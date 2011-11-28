(* word *)

(* word-def *)

let mod_refl_word_size = new_axiom
  `word_size MOD word_size = 0`;;

let mod_lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let zero_mod_word_size = new_axiom
  `0 MOD word_size = 0`;;

let lt_mod_word_size = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_refl_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let mod_add_mod_word_size = new_axiom
  `!m n. (m MOD word_size + n MOD word_size) MOD word_size = (m + n) MOD word_size`;;

let mod_mult_mod_word_size = new_axiom
  `!m n. (m MOD word_size * n MOD word_size) MOD word_size = (m * n) MOD word_size`;;

let divides_mod_word_size = new_axiom
   `!n. divides word_size n <=> n MOD word_size = 0`;;

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

let num_to_word_is_zero = new_axiom
   `!x. num_to_word x = num_to_word 0 <=> divides word_size x`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_to_num_mod_bound = new_axiom
  `!x. word_to_num x MOD word_size = word_to_num x`;;

let word_add_to_num = new_axiom
   `!x y.
      word_to_num (word_add x y) =
      (word_to_num x + word_to_num y) MOD word_size`;;

let word_mult_to_num = new_axiom
   `!x y.
      word_to_num (word_mult x y) =
      (word_to_num x * word_to_num y) MOD word_size`;;

let word_lt_alt = new_axiom
   `!x y. word_lt x y = word_to_num x < word_to_num y`;;

let num_to_word_word_size = new_axiom
   `num_to_word word_size = num_to_word 0`;;

let word_add_comm = new_axiom
   `!x y. word_add x y = word_add y x`;;

let word_add_assoc = new_axiom
   `!x y z. word_add (word_add x y) z = word_add x (word_add y z)`;;

let word_add_left_zero = new_axiom
   `!x. word_add (num_to_word 0) x = x`;;

let word_add_right_zero = new_axiom
   `!x. word_add x (num_to_word 0) = x`;;

let word_add_left_neg = new_axiom
   `!x. word_add (word_neg x) x = num_to_word 0`;;

let word_add_right_neg = new_axiom
   `!x. word_add x (word_neg x) = num_to_word 0`;;

let word_add_left_cancel = new_axiom
   `!x y z. word_add x y = word_add x z <=> y = z`;;

let word_add_right_cancel = new_axiom
   `!x y z. word_add y x = word_add z x <=> y = z`;;

let word_add_left_cancel_zero = new_axiom
   `!x y. word_add x y = x <=> y = num_to_word 0`;;

let word_add_right_cancel_zero = new_axiom
   `!x y. word_add y x = x <=> y = num_to_word 0`;;

let word_neg_neg = new_axiom
   `!x. word_neg (word_neg x) = x`;;

let word_neg_inj = new_axiom
   `!x y. word_neg x = word_neg y ==> x = y`;;

let word_neg_zero = new_axiom
   `word_neg (num_to_word 0) = num_to_word 0`;;

let word_neg_is_zero = new_axiom
   `!x. word_neg x = num_to_word 0 <=> x = num_to_word 0`;;

let word_neg_add = new_axiom
   `!x y.
      word_add (word_neg x) (word_neg y) =
      word_neg (word_add x y)`;;

let word_mult_comm = new_axiom
   `!x y. word_mult x y = word_mult y x`;;

let word_mult_assoc = new_axiom
   `!x y z.
      word_mult (word_mult x y) z = word_mult x (word_mult y z)`;;

let word_add_left_distrib = new_axiom
   `!x y z.
      word_mult x (word_add y z) =
      word_add (word_mult x y) (word_mult x z)`;;

let word_add_right_distrib = new_axiom
   `!x y z.
      word_mult (word_add y z) x =
      word_add (word_mult y x) (word_mult z x)`;;

let word_mult_left_zero = new_axiom
   `!x. word_mult (num_to_word 0) x = num_to_word 0`;;

let word_mult_right_zero = new_axiom
   `!x. word_mult x (num_to_word 0) = num_to_word 0`;;

let word_mult_left_one = new_axiom
   `!x. word_mult (num_to_word 1) x = x`;;

let word_mult_right_one = new_axiom
   `!x. word_mult x (num_to_word 1) = x`;;

let word_mult_left_neg = new_axiom
   `!x y. word_mult (word_neg x) y = word_neg (word_mult x y)`;;

let word_mult_right_neg = new_axiom
   `!x y. word_mult x (word_neg y) = word_neg (word_mult x y)`;;

(*PARAMETRIC
(* word *)

(* word-def *)

let mod_refl_word_size = new_axiom
  `word_size MOD word_size = 0`;;

let mod_lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let zero_mod_word_size = new_axiom
  `0 MOD word_size = 0`;;

let lt_mod_word_size = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_refl_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let mod_add_mod_word_size = new_axiom
  `!m n. (m MOD word_size + n MOD word_size) MOD word_size = (m + n) MOD word_size`;;

let mod_mult_mod_word_size = new_axiom
  `!m n. (m MOD word_size * n MOD word_size) MOD word_size = (m * n) MOD word_size`;;

let divides_mod_word_size = new_axiom
   `!n. divides word_size n <=> n MOD word_size = 0`;;

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

let num_to_word_is_zero = new_axiom
   `!x. num_to_word x = num_to_word 0 <=> divides word_size x`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_to_num_mod_bound = new_axiom
  `!x. word_to_num x MOD word_size = word_to_num x`;;

let word_add_to_num = new_axiom
   `!x y.
      word_to_num (word_add x y) =
      (word_to_num x + word_to_num y) MOD word_size`;;

let word_mult_to_num = new_axiom
   `!x y.
      word_to_num (word_mult x y) =
      (word_to_num x * word_to_num y) MOD word_size`;;

let word_lt_alt = new_axiom
   `!x y. word_lt x y = word_to_num x < word_to_num y`;;

let num_to_word_word_size = new_axiom
   `num_to_word word_size = num_to_word 0`;;

let word_add_comm = new_axiom
   `!x y. word_add x y = word_add y x`;;

let word_add_assoc = new_axiom
   `!x y z. word_add (word_add x y) z = word_add x (word_add y z)`;;

let word_add_left_zero = new_axiom
   `!x. word_add (num_to_word 0) x = x`;;

let word_add_right_zero = new_axiom
   `!x. word_add x (num_to_word 0) = x`;;

let word_add_left_neg = new_axiom
   `!x. word_add (word_neg x) x = num_to_word 0`;;

let word_add_right_neg = new_axiom
   `!x. word_add x (word_neg x) = num_to_word 0`;;

let word_add_left_cancel = new_axiom
   `!x y z. word_add x y = word_add x z <=> y = z`;;

let word_add_right_cancel = new_axiom
   `!x y z. word_add y x = word_add z x <=> y = z`;;

let word_add_left_cancel_zero = new_axiom
   `!x y. word_add x y = x <=> y = num_to_word 0`;;

let word_add_right_cancel_zero = new_axiom
   `!x y. word_add y x = x <=> y = num_to_word 0`;;

let word_neg_neg = new_axiom
   `!x. word_neg (word_neg x) = x`;;

let word_neg_inj = new_axiom
   `!x y. word_neg x = word_neg y ==> x = y`;;

let word_neg_zero = new_axiom
   `word_neg (num_to_word 0) = num_to_word 0`;;

let word_neg_is_zero = new_axiom
   `!x. word_neg x = num_to_word 0 <=> x = num_to_word 0`;;

let word_neg_add = new_axiom
   `!x y.
      word_add (word_neg x) (word_neg y) =
      word_neg (word_add x y)`;;

let word_mult_comm = new_axiom
   `!x y. word_mult x y = word_mult y x`;;

let word_mult_assoc = new_axiom
   `!x y z.
      word_mult (word_mult x y) z = word_mult x (word_mult y z)`;;

let word_add_left_distrib = new_axiom
   `!x y z.
      word_mult x (word_add y z) =
      word_add (word_mult x y) (word_mult x z)`;;

let word_add_right_distrib = new_axiom
   `!x y z.
      word_mult (word_add y z) x =
      word_add (word_mult y x) (word_mult z x)`;;

let word_mult_left_zero = new_axiom
   `!x. word_mult (num_to_word 0) x = num_to_word 0`;;

let word_mult_right_zero = new_axiom
   `!x. word_mult x (num_to_word 0) = num_to_word 0`;;

let word_mult_left_one = new_axiom
   `!x. word_mult (num_to_word 1) x = x`;;

let word_mult_right_one = new_axiom
   `!x. word_mult x (num_to_word 1) = x`;;

let word_mult_left_neg = new_axiom
   `!x y. word_mult (word_neg x) y = word_neg (word_mult x y)`;;

let word_mult_right_neg = new_axiom
   `!x y. word_mult x (word_neg y) = word_neg (word_mult x y)`;;
*)

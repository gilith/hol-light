(* gfp *)

(* gfp-def *)

let mod_refl_oddprime = new_axiom
  `oddprime MOD oddprime = 0`;;

let mod_lt_oddprime = new_axiom
  `!n. n < oddprime ==> n MOD oddprime = n`;;

let zero_mod_oddprime = new_axiom
  `0 MOD oddprime = 0`;;

let lt_mod_oddprime = new_axiom
  `!n. n MOD oddprime < oddprime`;;

let mod_mod_refl_oddprime = new_axiom
  `!n. n MOD oddprime MOD oddprime = n MOD oddprime`;;

let mod_add_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime + n MOD oddprime) MOD oddprime = (m + n) MOD oddprime`;;

let mod_mult_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime * n MOD oddprime) MOD oddprime = (m * n) MOD oddprime`;;

let divides_mod_oddprime = new_axiom
   `!n. divides oddprime n <=> n MOD oddprime = 0`;;

new_type ("gfp",0);;

new_constant ("num_to_gfp", `:num -> gfp`);;

new_constant ("gfp_to_num", `:gfp -> num`);;

let gfp_to_num_to_gfp = new_axiom
  `!x. num_to_gfp (gfp_to_num x) = x`;;

let num_to_gfp_inj = new_axiom
   `!x y.
      x < oddprime /\ y < oddprime /\ num_to_gfp x = num_to_gfp y ==>
      x = y`;;

let num_to_gfp_to_num = new_axiom
  `!x. gfp_to_num (num_to_gfp x) = x MOD oddprime`;;

new_constant ("gfp_add", `:gfp -> gfp -> gfp`);;

let num_to_gfp_add = new_axiom
  `!x1 y1.
     num_to_gfp (x1 + y1) =
     gfp_add (num_to_gfp x1) (num_to_gfp y1)`;;

new_constant ("gfp_mult", `:gfp -> gfp -> gfp`);;

let num_to_gfp_mult = new_axiom
  `!x1 y1.
     num_to_gfp (x1 * y1) =
     gfp_mult (num_to_gfp x1) (num_to_gfp y1)`;;

new_constant ("gfp_neg", `:gfp -> gfp`);;

let gfp_neg_def = new_axiom
  `!x. gfp_neg x = num_to_gfp (oddprime - gfp_to_num x)`;;

new_constant ("gfp_sub", `:gfp -> gfp -> gfp`);;

let gfp_sub_def = new_axiom
  `!x y. gfp_sub x y = gfp_add x (gfp_neg y)`;;

new_constant ("gfp_le", `:gfp -> gfp -> bool`);;

let gfp_le_def = new_axiom
  `!x y. gfp_le x y = gfp_to_num x <= gfp_to_num y`;;

new_constant ("gfp_lt", `:gfp -> gfp -> bool`);;

let gfp_lt_def = new_axiom
  `!x y. gfp_lt x y = ~(gfp_le y x)`;;

(* gfp-thm *)

let gfp_to_num_inj = new_axiom
  `!x y. gfp_to_num x = gfp_to_num y ==> x = y`;;

let num_to_gfp_eq = new_axiom
   `!x y.
      num_to_gfp x = num_to_gfp y <=> x MOD oddprime = y MOD oddprime`;;

let num_to_gfp_is_zero = new_axiom
   `!x. num_to_gfp x = num_to_gfp 0 <=> divides oddprime x`;;

let gfp_to_num_bound = new_axiom
  `!x. gfp_to_num x < oddprime`;;

let gfp_to_num_div_bound = new_axiom
  `!x. gfp_to_num x DIV oddprime = 0`;;

let gfp_to_num_mod_bound = new_axiom
  `!x. gfp_to_num x MOD oddprime = gfp_to_num x`;;

let gfp_add_to_num = new_axiom
   `!x y.
      gfp_to_num (gfp_add x y) =
      (gfp_to_num x + gfp_to_num y) MOD oddprime`;;

let gfp_mult_to_num = new_axiom
   `!x y.
      gfp_to_num (gfp_mult x y) =
      (gfp_to_num x * gfp_to_num y) MOD oddprime`;;

let gfp_lt_alt = new_axiom
   `!x y. gfp_lt x y = gfp_to_num x < gfp_to_num y`;;

let num_to_gfp_oddprime = new_axiom
   `num_to_gfp oddprime = num_to_gfp 0`;;

let gfp_add_comm = new_axiom
   `!x y. gfp_add x y = gfp_add y x`;;

let gfp_add_assoc = new_axiom
   `!x y z. gfp_add (gfp_add x y) z = gfp_add x (gfp_add y z)`;;

let gfp_add_left_zero = new_axiom
   `!x. gfp_add (num_to_gfp 0) x = x`;;

let gfp_add_right_zero = new_axiom
   `!x. gfp_add x (num_to_gfp 0) = x`;;

let gfp_add_left_neg = new_axiom
   `!x. gfp_add (gfp_neg x) x = num_to_gfp 0`;;

let gfp_add_right_neg = new_axiom
   `!x. gfp_add x (gfp_neg x) = num_to_gfp 0`;;

let gfp_add_left_cancel = new_axiom
   `!x y z. gfp_add x y = gfp_add x z <=> y = z`;;

let gfp_add_right_cancel = new_axiom
   `!x y z. gfp_add y x = gfp_add z x <=> y = z`;;

let gfp_add_left_cancel_zero = new_axiom
   `!x y. gfp_add x y = x <=> y = num_to_gfp 0`;;

let gfp_add_right_cancel_zero = new_axiom
   `!x y. gfp_add y x = x <=> y = num_to_gfp 0`;;

let gfp_neg_neg = new_axiom
   `!x. gfp_neg (gfp_neg x) = x`;;

let gfp_neg_inj = new_axiom
   `!x y. gfp_neg x = gfp_neg y ==> x = y`;;

let gfp_neg_zero = new_axiom
   `gfp_neg (num_to_gfp 0) = num_to_gfp 0`;;

let gfp_neg_is_zero = new_axiom
   `!x. gfp_neg x = num_to_gfp 0 <=> x = num_to_gfp 0`;;

let gfp_neg_add = new_axiom
   `!x y.
      gfp_add (gfp_neg x) (gfp_neg y) =
      gfp_neg (gfp_add x y)`;;

let gfp_mult_comm = new_axiom
   `!x y. gfp_mult x y = gfp_mult y x`;;

let gfp_mult_assoc = new_axiom
   `!x y z.
      gfp_mult (gfp_mult x y) z = gfp_mult x (gfp_mult y z)`;;

let gfp_add_left_distrib = new_axiom
   `!x y z.
      gfp_mult x (gfp_add y z) =
      gfp_add (gfp_mult x y) (gfp_mult x z)`;;

let gfp_add_right_distrib = new_axiom
   `!x y z.
      gfp_mult (gfp_add y z) x =
      gfp_add (gfp_mult y x) (gfp_mult z x)`;;

let gfp_mult_left_zero = new_axiom
   `!x. gfp_mult (num_to_gfp 0) x = num_to_gfp 0`;;

let gfp_mult_right_zero = new_axiom
   `!x. gfp_mult x (num_to_gfp 0) = num_to_gfp 0`;;

let gfp_mult_left_one = new_axiom
   `!x. gfp_mult (num_to_gfp 1) x = x`;;

let gfp_mult_right_one = new_axiom
   `!x. gfp_mult x (num_to_gfp 1) = x`;;

let gfp_mult_left_neg = new_axiom
   `!x y. gfp_mult (gfp_neg x) y = gfp_neg (gfp_mult x y)`;;

let gfp_mult_right_neg = new_axiom
   `!x y. gfp_mult x (gfp_neg y) = gfp_neg (gfp_mult x y)`;;

(*PARAMETRIC
(* gfp *)

(* gfp-def *)

let mod_refl_oddprime = new_axiom
  `oddprime MOD oddprime = 0`;;

let mod_lt_oddprime = new_axiom
  `!n. n < oddprime ==> n MOD oddprime = n`;;

let zero_mod_oddprime = new_axiom
  `0 MOD oddprime = 0`;;

let lt_mod_oddprime = new_axiom
  `!n. n MOD oddprime < oddprime`;;

let mod_mod_refl_oddprime = new_axiom
  `!n. n MOD oddprime MOD oddprime = n MOD oddprime`;;

let mod_add_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime + n MOD oddprime) MOD oddprime = (m + n) MOD oddprime`;;

let mod_mult_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime * n MOD oddprime) MOD oddprime = (m * n) MOD oddprime`;;

let divides_mod_oddprime = new_axiom
   `!n. divides oddprime n <=> n MOD oddprime = 0`;;

new_type ("gfp",0);;

new_constant ("num_to_gfp", `:num -> gfp`);;

new_constant ("gfp_to_num", `:gfp -> num`);;

let gfp_to_num_to_gfp = new_axiom
  `!x. num_to_gfp (gfp_to_num x) = x`;;

let num_to_gfp_inj = new_axiom
   `!x y.
      x < oddprime /\ y < oddprime /\ num_to_gfp x = num_to_gfp y ==>
      x = y`;;

let num_to_gfp_to_num = new_axiom
  `!x. gfp_to_num (num_to_gfp x) = x MOD oddprime`;;

new_constant ("gfp_add", `:gfp -> gfp -> gfp`);;

let num_to_gfp_add = new_axiom
  `!x1 y1.
     num_to_gfp (x1 + y1) =
     gfp_add (num_to_gfp x1) (num_to_gfp y1)`;;

new_constant ("gfp_mult", `:gfp -> gfp -> gfp`);;

let num_to_gfp_mult = new_axiom
  `!x1 y1.
     num_to_gfp (x1 * y1) =
     gfp_mult (num_to_gfp x1) (num_to_gfp y1)`;;

new_constant ("gfp_neg", `:gfp -> gfp`);;

let gfp_neg_def = new_axiom
  `!x. gfp_neg x = num_to_gfp (oddprime - gfp_to_num x)`;;

new_constant ("gfp_sub", `:gfp -> gfp -> gfp`);;

let gfp_sub_def = new_axiom
  `!x y. gfp_sub x y = gfp_add x (gfp_neg y)`;;

new_constant ("gfp_le", `:gfp -> gfp -> bool`);;

let gfp_le_def = new_axiom
  `!x y. gfp_le x y = gfp_to_num x <= gfp_to_num y`;;

new_constant ("gfp_lt", `:gfp -> gfp -> bool`);;

let gfp_lt_def = new_axiom
  `!x y. gfp_lt x y = ~(gfp_le y x)`;;

(* gfp-thm *)

let gfp_to_num_inj = new_axiom
  `!x y. gfp_to_num x = gfp_to_num y ==> x = y`;;

let num_to_gfp_eq = new_axiom
   `!x y.
      num_to_gfp x = num_to_gfp y <=> x MOD oddprime = y MOD oddprime`;;

let num_to_gfp_is_zero = new_axiom
   `!x. num_to_gfp x = num_to_gfp 0 <=> divides oddprime x`;;

let gfp_to_num_bound = new_axiom
  `!x. gfp_to_num x < oddprime`;;

let gfp_to_num_div_bound = new_axiom
  `!x. gfp_to_num x DIV oddprime = 0`;;

let gfp_to_num_mod_bound = new_axiom
  `!x. gfp_to_num x MOD oddprime = gfp_to_num x`;;

let gfp_add_to_num = new_axiom
   `!x y.
      gfp_to_num (gfp_add x y) =
      (gfp_to_num x + gfp_to_num y) MOD oddprime`;;

let gfp_mult_to_num = new_axiom
   `!x y.
      gfp_to_num (gfp_mult x y) =
      (gfp_to_num x * gfp_to_num y) MOD oddprime`;;

let gfp_lt_alt = new_axiom
   `!x y. gfp_lt x y = gfp_to_num x < gfp_to_num y`;;

let num_to_gfp_oddprime = new_axiom
   `num_to_gfp oddprime = num_to_gfp 0`;;

let gfp_add_comm = new_axiom
   `!x y. gfp_add x y = gfp_add y x`;;

let gfp_add_assoc = new_axiom
   `!x y z. gfp_add (gfp_add x y) z = gfp_add x (gfp_add y z)`;;

let gfp_add_left_zero = new_axiom
   `!x. gfp_add (num_to_gfp 0) x = x`;;

let gfp_add_right_zero = new_axiom
   `!x. gfp_add x (num_to_gfp 0) = x`;;

let gfp_add_left_neg = new_axiom
   `!x. gfp_add (gfp_neg x) x = num_to_gfp 0`;;

let gfp_add_right_neg = new_axiom
   `!x. gfp_add x (gfp_neg x) = num_to_gfp 0`;;

let gfp_add_left_cancel = new_axiom
   `!x y z. gfp_add x y = gfp_add x z <=> y = z`;;

let gfp_add_right_cancel = new_axiom
   `!x y z. gfp_add y x = gfp_add z x <=> y = z`;;

let gfp_add_left_cancel_zero = new_axiom
   `!x y. gfp_add x y = x <=> y = num_to_gfp 0`;;

let gfp_add_right_cancel_zero = new_axiom
   `!x y. gfp_add y x = x <=> y = num_to_gfp 0`;;

let gfp_neg_neg = new_axiom
   `!x. gfp_neg (gfp_neg x) = x`;;

let gfp_neg_inj = new_axiom
   `!x y. gfp_neg x = gfp_neg y ==> x = y`;;

let gfp_neg_zero = new_axiom
   `gfp_neg (num_to_gfp 0) = num_to_gfp 0`;;

let gfp_neg_is_zero = new_axiom
   `!x. gfp_neg x = num_to_gfp 0 <=> x = num_to_gfp 0`;;

let gfp_neg_add = new_axiom
   `!x y.
      gfp_add (gfp_neg x) (gfp_neg y) =
      gfp_neg (gfp_add x y)`;;

let gfp_mult_comm = new_axiom
   `!x y. gfp_mult x y = gfp_mult y x`;;

let gfp_mult_assoc = new_axiom
   `!x y z.
      gfp_mult (gfp_mult x y) z = gfp_mult x (gfp_mult y z)`;;

let gfp_add_left_distrib = new_axiom
   `!x y z.
      gfp_mult x (gfp_add y z) =
      gfp_add (gfp_mult x y) (gfp_mult x z)`;;

let gfp_add_right_distrib = new_axiom
   `!x y z.
      gfp_mult (gfp_add y z) x =
      gfp_add (gfp_mult y x) (gfp_mult z x)`;;

let gfp_mult_left_zero = new_axiom
   `!x. gfp_mult (num_to_gfp 0) x = num_to_gfp 0`;;

let gfp_mult_right_zero = new_axiom
   `!x. gfp_mult x (num_to_gfp 0) = num_to_gfp 0`;;

let gfp_mult_left_one = new_axiom
   `!x. gfp_mult (num_to_gfp 1) x = x`;;

let gfp_mult_right_one = new_axiom
   `!x. gfp_mult x (num_to_gfp 1) = x`;;

let gfp_mult_left_neg = new_axiom
   `!x y. gfp_mult (gfp_neg x) y = gfp_neg (gfp_mult x y)`;;

let gfp_mult_right_neg = new_axiom
   `!x y. gfp_mult x (gfp_neg y) = gfp_neg (gfp_mult x y)`;;
*)

(* gfp *)

(* gfp-mod *)

let mod_lt_oddprime = new_axiom
  `!n. n < oddprime ==> n MOD oddprime = n`;;

let lt_mod_oddprime = new_axiom
  `!n. n MOD oddprime < oddprime`;;

let mod_mod_refl_oddprime = new_axiom
  `!n. n MOD oddprime MOD oddprime = n MOD oddprime`;;

let mod_add_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime + n MOD oddprime) MOD oddprime = (m + n) MOD oddprime`;;

let mod_mult_mod2_oddprime = new_axiom
  `!m n. (m MOD oddprime * n MOD oddprime) MOD oddprime = (m * n) MOD oddprime`;;

(* gfp-def *)

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

let gfp_lt_alt = new_axiom
   `!x y. gfp_lt x y = gfp_to_num x < gfp_to_num y`;;

(*PARAMETRIC
(* gfp *)

(* gfp-mod *)

let mod_lt_oddprime = new_axiom
  `!n. n < oddprime ==> n MOD oddprime = n`;;

let lt_mod_oddprime = new_axiom
  `!n. n MOD oddprime < oddprime`;;

let mod_mod_refl_oddprime = new_axiom
  `!n. n MOD oddprime MOD oddprime = n MOD oddprime`;;

let mod_add_mod_oddprime = new_axiom
  `!m n. (m MOD oddprime + n MOD oddprime) MOD oddprime = (m + n) MOD oddprime`;;

let mod_mult_mod2_oddprime = new_axiom
  `!m n. (m MOD oddprime * n MOD oddprime) MOD oddprime = (m * n) MOD oddprime`;;

(* gfp-def *)

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

let gfp_lt_alt = new_axiom
   `!x y. gfp_lt x y = gfp_to_num x < gfp_to_num y`;;
*)

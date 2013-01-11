(*BEGIN-PARAMETRIC*)
let ring_comm_left_one = new_axiom
   `!x. ring_mult ring_one x = ring_mult x ring_one`;;

let ring_comm_right_one = new_axiom
   `!x. ring_mult x ring_one = ring_mult ring_one x`;;

let ring_comm_left_mult = new_axiom
   `!x y z.
      ring_mult x z = ring_mult z x /\
      ring_mult y z = ring_mult z y ==>
      ring_mult (ring_mult x y) z = ring_mult z (ring_mult x y)`;;

let ring_comm_right_mult = new_axiom
   `!x y z.
      ring_mult z x = ring_mult x z /\
      ring_mult z y = ring_mult y z ==>
      ring_mult z (ring_mult x y) = ring_mult (ring_mult x y) z`;;

new_constant ("ring_exp", `:ring -> num -> ring`);;

let ring_exp_right_zero = new_axiom
  `!x. ring_exp x 0 = ring_one`;;

let ring_exp_right_suc = new_axiom
  `!x n. ring_exp x (SUC n) = ring_mult x (ring_exp x n)`;;

let ring_exp_def = CONJ ring_exp_right_zero ring_exp_right_suc;;

let ring_exp_left_one = new_axiom
   `!n. ring_exp ring_one n = ring_one`;;

let ring_exp_right_one = new_axiom
   `!x. ring_exp x 1 = x`;;

let ring_exp_right_two = new_axiom
   `!x. ring_exp x 2 = ring_mult x x`;;

let ring_exp_right_add = new_axiom
   `!x m n.
      ring_exp x (m + n) = ring_mult (ring_exp x m) (ring_exp x n)`;;

let ring_exp_right_suc' = new_axiom
   `!x n. ring_exp x (SUC n) = ring_mult (ring_exp x n) x`;;

let ring_exp_right_mult = new_axiom
   `!x m n. ring_exp x (m * n) = ring_exp (ring_exp x m) n`;;

let ring_comm_left_exp = new_axiom
   `!x n y.
      ring_mult x y = ring_mult y x ==>
      ring_mult (ring_exp x n) y = ring_mult y (ring_exp x n)`;;

let ring_comm_right_exp = new_axiom
   `!x n y.
      ring_mult y x = ring_mult x y ==>
      ring_mult y (ring_exp x n) = ring_mult (ring_exp x n) y`;;

new_constant ("ring_exp_mult", `:ring -> ring -> bool list -> ring`);;

let ring_exp_mult_nil = new_axiom
    `!z x. ring_exp_mult z x [] = z`;;

let ring_exp_mult_cons = new_axiom
     `!z x h t.
        ring_exp_mult z x (CONS h t) =
        ring_exp_mult (if h then ring_mult z x else z)
          (ring_mult x x) t`;;

let ring_exp_mult_def = CONJ ring_exp_mult_nil ring_exp_mult_cons;;

let ring_exp_mult_invariant = new_axiom
   `!z x l.
      ring_exp_mult z x l =
      ring_mult z (ring_exp x (bits_to_num l))`;;

let ring_exp_mult_correct = new_axiom
   `!x n.
      ring_exp x n =
      ring_exp_mult ring_one x (num_to_bits n)`;;
(*END-PARAMETRIC*)

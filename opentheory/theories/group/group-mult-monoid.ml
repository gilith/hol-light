(*BEGIN-PARAMETRIC*)
new_constant ("group_mult", `:group -> num -> group`);;

let group_mult_right_zero = new_axiom
  `!x. group_mult x 0 = group_zero`;;

let group_mult_right_suc = new_axiom
  `!x n. group_mult x (SUC n) = group_add x (group_mult x n)`;;

let group_mult_def = CONJ group_mult_right_zero group_mult_right_suc;;

let group_mult_left_zero = new_axiom
   `!n. group_mult group_zero n = group_zero`;;

let group_mult_right_one = new_axiom
   `!x. group_mult x 1 = x`;;

let group_mult_right_two = new_axiom
   `!x. group_mult x 2 = group_add x x`;;

let group_mult_right_add = new_axiom
   `!x m n.
      group_mult x (m + n) = group_add (group_mult x m) (group_mult x n)`;;

let group_mult_right_suc' = new_axiom
   `!x n. group_mult x (SUC n) = group_add (group_mult x n) x`;;

let group_mult_right_mult = new_axiom
   `!x m n. group_mult x (m * n) = group_mult (group_mult x m) n`;;

let group_comm_left_mult = new_axiom
   `!x n y.
      group_add x y = group_add y x ==>
      group_add (group_mult x n) y = group_add y (group_mult x n)`;;

let group_comm_right_mult = new_axiom
   `!x n y.
      group_add y x = group_add x y ==>
      group_add y (group_mult x n) = group_add (group_mult x n) y`;;

new_constant ("group_mult_add", `:group -> group -> bool list -> group`);;

let group_mult_add_nil = new_axiom
    `!z x. group_mult_add z x [] = z`;;

let group_mult_add_cons = new_axiom
     `!z x h t.
        group_mult_add z x (CONS h t) =
        group_mult_add (if h then group_add z x else z)
          (group_add x x) t`;;

let group_mult_add_def = CONJ group_mult_add_nil group_mult_add_cons;;

let group_mult_add_invariant = new_axiom
   `!z x l.
      group_mult_add z x l =
      group_add z (group_mult x (bits_to_num l))`;;

let group_mult_add_correct = new_axiom
   `!x n.
      group_mult x n =
      group_mult_add group_zero x (num_to_bits n)`;;
(*END-PARAMETRIC*)

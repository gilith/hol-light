(*BEGIN-PARAMETRIC*)
let ring_add_left_neg' = new_axiom
   `!x y. ring_add (ring_neg x) (ring_add x y) = y`;;

let ring_add_right_neg = new_axiom
   `!x. ring_add x (ring_neg x) = ring_zero`;;

let ring_add_right_neg' = new_axiom
   `!x y. ring_add x (ring_add (ring_neg x) y) = y`;;

let ring_add_right_zero = new_axiom
   `!x. ring_add x ring_zero = x`;;

let ring_add_left_cancel_imp = new_axiom
   `!x y z. ring_add x y = ring_add x z ==> y = z`;;

let ring_add_left_cancel = new_axiom
   `!x y z. ring_add x y = ring_add x z <=> y = z`;;

let ring_add_left_cancel_zero_imp = new_axiom
   `!x y. ring_add x y = x ==> y = ring_zero`;;

let ring_add_left_cancel_zero = new_axiom
   `!x y. ring_add x y = x <=> y = ring_zero`;;

let ring_add_right_cancel_imp = new_axiom
   `!x y z. ring_add y x = ring_add z x ==> y = z`;;

let ring_add_right_cancel = new_axiom
   `!x y z. ring_add y x = ring_add z x <=> y = z`;;

let ring_add_right_cancel_zero_imp = new_axiom
   `!x y. ring_add y x = x ==> y = ring_zero`;;

let ring_add_right_cancel_zero = new_axiom
   `!x y. ring_add y x = x <=> y = ring_zero`;;

let ring_neg_inj_imp = new_axiom
   `!x y. ring_neg x = ring_neg y ==> x = y`;;

let ring_neg_inj = new_axiom
   `!x y. ring_neg x = ring_neg y <=> x = y`;;

let ring_neg_zero = new_axiom
   `ring_neg ring_zero = ring_zero`;;

let ring_neg_neg = new_axiom
   `!x. ring_neg (ring_neg x) = x`;;

let ring_neg_add = new_axiom
   `!x y. ring_neg (ring_add x y) = ring_add (ring_neg y) (ring_neg x)`;;

let ring_comm_left_neg_imp = new_axiom
   `!x y.
      ring_add x y = ring_add y x ==>
      ring_add (ring_neg x) y = ring_add y (ring_neg x)`;;

let ring_comm_left_neg = new_axiom
   `!x y.
      ring_add (ring_neg x) y = ring_add y (ring_neg x) <=>
      ring_add x y = ring_add y x`;;

let ring_comm_right_neg_imp = new_axiom
   `!x y.
      ring_add y x = ring_add x y ==>
      ring_add y (ring_neg x) = ring_add (ring_neg x) y`;;

let ring_comm_right_neg = new_axiom
   `!x y.
      ring_add y (ring_neg x) = ring_add (ring_neg x) y <=>
      ring_add y x = ring_add x y`;;

let ring_comm_left_zero = new_axiom
   `!x. ring_add ring_zero x = ring_add x ring_zero`;;

let ring_comm_right_zero = new_axiom
   `!x. ring_add x ring_zero = ring_add ring_zero x`;;

let ring_comm_left_add = new_axiom
   `!x y z.
      ring_add x z = ring_add z x /\
      ring_add y z = ring_add z y ==>
      ring_add (ring_add x y) z = ring_add z (ring_add x y)`;;

let ring_comm_right_add = new_axiom
   `!x y z.
      ring_add z x = ring_add x z /\
      ring_add z y = ring_add y z ==>
      ring_add z (ring_add x y) = ring_add (ring_add x y) z`;;

new_constant ("ring_sub", `:ring -> ring -> ring`);;

let ring_sub_def = new_axiom
  `!(x : ring) (y : ring). ring_sub x y = ring_add x (ring_neg y)`;;

let ring_sub_left_zero = new_axiom
   `!x. ring_sub ring_zero x = ring_neg x`;;

let ring_sub_right_zero = new_axiom
   `!x. ring_sub x ring_zero = x`;;

let ring_sub_refl = new_axiom
   `!x. ring_sub x x = ring_zero`;;

let ring_neg_sub = new_axiom
   `!x y. ring_neg (ring_sub x y) = ring_sub y x`;;

let ring_comm_left_sub = new_axiom
   `!x y z.
      ring_add x z = ring_add z x /\
      ring_add y z = ring_add z y ==>
      ring_add (ring_sub x y) z = ring_add z (ring_sub x y)`;;

let ring_comm_right_sub = new_axiom
   `!x y z.
      ring_add z x = ring_add x z /\
      ring_add z y = ring_add y z ==>
      ring_add z (ring_sub x y) = ring_add (ring_sub x y) z`;;
(*END-PARAMETRIC*)

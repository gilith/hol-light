(*BEGIN-PARAMETRIC*)
let ring_unit_add_left_neg' = new_axiom
   `!x y. ring_unit_add (ring_unit_neg x) (ring_unit_add x y) = y`;;

let ring_unit_add_right_neg = new_axiom
   `!x. ring_unit_add x (ring_unit_neg x) = ring_unit_zero`;;

let ring_unit_add_right_neg' = new_axiom
   `!x y. ring_unit_add x (ring_unit_add (ring_unit_neg x) y) = y`;;

let ring_unit_add_right_zero = new_axiom
   `!x. ring_unit_add x ring_unit_zero = x`;;

let ring_unit_add_left_cancel_imp = new_axiom
   `!x y z. ring_unit_add x y = ring_unit_add x z ==> y = z`;;

let ring_unit_add_left_cancel = new_axiom
   `!x y z. ring_unit_add x y = ring_unit_add x z <=> y = z`;;

let ring_unit_add_left_cancel_zero_imp = new_axiom
   `!x y. ring_unit_add x y = x ==> y = ring_unit_zero`;;

let ring_unit_add_left_cancel_zero = new_axiom
   `!x y. ring_unit_add x y = x <=> y = ring_unit_zero`;;

let ring_unit_add_right_cancel_imp = new_axiom
   `!x y z. ring_unit_add y x = ring_unit_add z x ==> y = z`;;

let ring_unit_add_right_cancel = new_axiom
   `!x y z. ring_unit_add y x = ring_unit_add z x <=> y = z`;;

let ring_unit_add_right_cancel_zero_imp = new_axiom
   `!x y. ring_unit_add y x = x ==> y = ring_unit_zero`;;

let ring_unit_add_right_cancel_zero = new_axiom
   `!x y. ring_unit_add y x = x <=> y = ring_unit_zero`;;

let ring_unit_neg_inj_imp = new_axiom
   `!x y. ring_unit_neg x = ring_unit_neg y ==> x = y`;;

let ring_unit_neg_inj = new_axiom
   `!x y. ring_unit_neg x = ring_unit_neg y <=> x = y`;;

let ring_unit_neg_zero = new_axiom
   `ring_unit_neg ring_unit_zero = ring_unit_zero`;;

let ring_unit_neg_neg = new_axiom
   `!x. ring_unit_neg (ring_unit_neg x) = x`;;

let ring_unit_neg_add = new_axiom
   `!x y. ring_unit_neg (ring_unit_add x y) = ring_unit_add (ring_unit_neg y) (ring_unit_neg x)`;;

let ring_unit_neg_left_eq = new_axiom
   `!x y. ring_unit_add y x = ring_unit_zero ==> ring_unit_neg x = y`;;

let ring_unit_neg_right_eq = new_axiom
   `!x y. ring_unit_add x y = ring_unit_zero ==> ring_unit_neg x = y`;;

let ring_unit_comm_left_neg_imp = new_axiom
   `!x y.
      ring_unit_add x y = ring_unit_add y x ==>
      ring_unit_add (ring_unit_neg x) y = ring_unit_add y (ring_unit_neg x)`;;

let ring_unit_comm_left_neg = new_axiom
   `!x y.
      ring_unit_add (ring_unit_neg x) y = ring_unit_add y (ring_unit_neg x) <=>
      ring_unit_add x y = ring_unit_add y x`;;

let ring_unit_comm_right_neg_imp = new_axiom
   `!x y.
      ring_unit_add y x = ring_unit_add x y ==>
      ring_unit_add y (ring_unit_neg x) = ring_unit_add (ring_unit_neg x) y`;;

let ring_unit_comm_right_neg = new_axiom
   `!x y.
      ring_unit_add y (ring_unit_neg x) = ring_unit_add (ring_unit_neg x) y <=>
      ring_unit_add y x = ring_unit_add x y`;;

let ring_unit_comm_left_zero = new_axiom
   `!x. ring_unit_add ring_unit_zero x = ring_unit_add x ring_unit_zero`;;

let ring_unit_comm_right_zero = new_axiom
   `!x. ring_unit_add x ring_unit_zero = ring_unit_add ring_unit_zero x`;;

let ring_unit_comm_left_add = new_axiom
   `!x y z.
      ring_unit_add x z = ring_unit_add z x /\
      ring_unit_add y z = ring_unit_add z y ==>
      ring_unit_add (ring_unit_add x y) z = ring_unit_add z (ring_unit_add x y)`;;

let ring_unit_comm_right_add = new_axiom
   `!x y z.
      ring_unit_add z x = ring_unit_add x z /\
      ring_unit_add z y = ring_unit_add y z ==>
      ring_unit_add z (ring_unit_add x y) = ring_unit_add (ring_unit_add x y) z`;;

new_constant ("ring_unit_sub", `:ring_unit -> ring_unit -> ring_unit`);;

let ring_unit_sub_def = new_axiom
  `!(x : ring_unit) (y : ring_unit). ring_unit_sub x y = ring_unit_add x (ring_unit_neg y)`;;

let ring_unit_sub_left_zero = new_axiom
   `!x. ring_unit_sub ring_unit_zero x = ring_unit_neg x`;;

let ring_unit_sub_right_zero = new_axiom
   `!x. ring_unit_sub x ring_unit_zero = x`;;

let ring_unit_sub_refl = new_axiom
   `!x. ring_unit_sub x x = ring_unit_zero`;;

let ring_unit_neg_sub = new_axiom
   `!x y. ring_unit_neg (ring_unit_sub x y) = ring_unit_sub y x`;;

let ring_unit_comm_left_sub = new_axiom
   `!x y z.
      ring_unit_add x z = ring_unit_add z x /\
      ring_unit_add y z = ring_unit_add z y ==>
      ring_unit_add (ring_unit_sub x y) z = ring_unit_add z (ring_unit_sub x y)`;;

let ring_unit_comm_right_sub = new_axiom
   `!x y z.
      ring_unit_add z x = ring_unit_add x z /\
      ring_unit_add z y = ring_unit_add y z ==>
      ring_unit_add z (ring_unit_sub x y) = ring_unit_add (ring_unit_sub x y) z`;;

new_constant ("ring_unit_mult", `:ring_unit -> num -> ring_unit`);;

let ring_unit_mult_right_zero = new_axiom
  `!x. ring_unit_mult x 0 = ring_unit_zero`;;

let ring_unit_mult_right_suc = new_axiom
  `!x n. ring_unit_mult x (SUC n) = ring_unit_add x (ring_unit_mult x n)`;;

let ring_unit_mult_def = CONJ ring_unit_mult_right_zero ring_unit_mult_right_suc;;

let ring_unit_mult_left_zero = new_axiom
   `!n. ring_unit_mult ring_unit_zero n = ring_unit_zero`;;

let ring_unit_mult_right_one = new_axiom
   `!x. ring_unit_mult x 1 = x`;;

let ring_unit_mult_right_two = new_axiom
   `!x. ring_unit_mult x 2 = ring_unit_add x x`;;

let ring_unit_mult_right_add = new_axiom
   `!x m n.
      ring_unit_mult x (m + n) = ring_unit_add (ring_unit_mult x m) (ring_unit_mult x n)`;;

let ring_unit_mult_right_suc' = new_axiom
   `!x n. ring_unit_mult x (SUC n) = ring_unit_add (ring_unit_mult x n) x`;;

let ring_unit_mult_right_mult = new_axiom
   `!x m n. ring_unit_mult x (m * n) = ring_unit_mult (ring_unit_mult x m) n`;;

let ring_unit_comm_left_mult = new_axiom
   `!x n y.
      ring_unit_add x y = ring_unit_add y x ==>
      ring_unit_add (ring_unit_mult x n) y = ring_unit_add y (ring_unit_mult x n)`;;

let ring_unit_comm_right_mult = new_axiom
   `!x n y.
      ring_unit_add y x = ring_unit_add x y ==>
      ring_unit_add y (ring_unit_mult x n) = ring_unit_add (ring_unit_mult x n) y`;;

new_constant ("ring_unit_mult_add", `:ring_unit -> ring_unit -> bool list -> ring_unit`);;

let ring_unit_mult_add_nil = new_axiom
    `!z x. ring_unit_mult_add z x [] = z`;;

let ring_unit_mult_add_cons = new_axiom
     `!z x h t.
        ring_unit_mult_add z x (CONS h t) =
        ring_unit_mult_add (if h then ring_unit_add z x else z)
          (ring_unit_add x x) t`;;

let ring_unit_mult_add_def = CONJ ring_unit_mult_add_nil ring_unit_mult_add_cons;;

let ring_unit_mult_add_invariant = new_axiom
   `!z x l.
      ring_unit_mult_add z x l =
      ring_unit_add z (ring_unit_mult x (bits_to_num l))`;;

let ring_unit_mult_add_correct = new_axiom
   `!x n.
      ring_unit_mult x n =
      ring_unit_mult_add ring_unit_zero x (num_to_bits n)`;;

let ring_unit_neg_mult = new_axiom
   `!x n. ring_unit_neg (ring_unit_mult x n) = ring_unit_mult (ring_unit_neg x) n`;;

new_constant
  ("ring_unit_mult_sub",
   `:bool -> ring_unit -> ring_unit -> ring_unit -> ring_unit -> bool list -> ring_unit`);;

let ring_unit_mult_sub_nil = new_axiom
    `(!b n d f p.
        ring_unit_mult_sub b n d f p [] =
        if b then ring_unit_sub n d else ring_unit_sub d n)`;;

let ring_unit_mult_sub_cons = new_axiom
    `(!b n d f p h t.
        ring_unit_mult_sub b n d f p (CONS h t) =
        let s = ring_unit_sub p f in
        ring_unit_mult_sub (~b) d (if h then ring_unit_sub n s else n) s f t)`;;

let ring_unit_mult_sub_def = CONJ ring_unit_mult_sub_nil ring_unit_mult_sub_cons;;

let ring_unit_mult_sub_invariant = new_axiom
   `!x n d f p l.
      ring_unit_add x n = ring_unit_add n x /\
      ring_unit_add x d = ring_unit_add d x ==>
      ring_unit_mult_sub T n d (ring_unit_mult x f) (ring_unit_neg (ring_unit_mult x p)) l =
      ring_unit_add (ring_unit_sub n d) (ring_unit_mult x (decode_fib_dest f p l)) /\
      ring_unit_mult_sub F n d (ring_unit_neg (ring_unit_mult x f)) (ring_unit_mult x p) l =
      ring_unit_add (ring_unit_sub d n) (ring_unit_mult x (decode_fib_dest f p l))`;;

let ring_unit_mult_sub_correct = new_axiom
   `!x n.
      ring_unit_mult x n =
      ring_unit_mult_sub T ring_unit_zero ring_unit_zero x ring_unit_zero (encode_fib n)`;;

new_constant
  ("ring_unit_elgamal_encrypt",
   `:ring_unit -> ring_unit -> ring_unit -> num -> ring_unit # ring_unit`);;

let ring_unit_elgamal_encrypt_def = new_axiom
  `!g h m k.
     ring_unit_elgamal_encrypt g h m k =
     (ring_unit_mult g k, ring_unit_add (ring_unit_mult h k) m)`;;

new_constant
  ("ring_unit_elgamal_decrypt",
   `:num -> ring_unit # ring_unit -> ring_unit`);;

let ring_unit_elgamal_decrypt_def = new_axiom
  `!x a b.
     ring_unit_elgamal_decrypt x (a,b) =
     ring_unit_add (ring_unit_neg (ring_unit_mult a x)) b`;;

let ring_unit_elgamal_correct = new_axiom
   `!g h m k x.
      (h = ring_unit_mult g x) ==>
      (ring_unit_elgamal_decrypt x (ring_unit_elgamal_encrypt g h m k) = m)`;;

let ring_unit_add_comm' = new_axiom
   `!x y z. ring_unit_add x (ring_unit_add y z) = ring_unit_add y (ring_unit_add x z)`;;
(*END-PARAMETRIC*)

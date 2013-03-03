(*BEGIN-PARAMETRIC*)
let field_star_add_left_neg' = new_axiom
   `!x y. field_star_add (field_star_neg x) (field_star_add x y) = y`;;

let field_star_add_right_neg = new_axiom
   `!x. field_star_add x (field_star_neg x) = field_star_zero`;;

let field_star_add_right_neg' = new_axiom
   `!x y. field_star_add x (field_star_add (field_star_neg x) y) = y`;;

let field_star_add_right_zero = new_axiom
   `!x. field_star_add x field_star_zero = x`;;

let field_star_add_left_cancel_imp = new_axiom
   `!x y z. field_star_add x y = field_star_add x z ==> y = z`;;

let field_star_add_left_cancel = new_axiom
   `!x y z. field_star_add x y = field_star_add x z <=> y = z`;;

let field_star_add_left_cancel_zero_imp = new_axiom
   `!x y. field_star_add x y = x ==> y = field_star_zero`;;

let field_star_add_left_cancel_zero = new_axiom
   `!x y. field_star_add x y = x <=> y = field_star_zero`;;

let field_star_add_right_cancel_imp = new_axiom
   `!x y z. field_star_add y x = field_star_add z x ==> y = z`;;

let field_star_add_right_cancel = new_axiom
   `!x y z. field_star_add y x = field_star_add z x <=> y = z`;;

let field_star_add_right_cancel_zero_imp = new_axiom
   `!x y. field_star_add y x = x ==> y = field_star_zero`;;

let field_star_add_right_cancel_zero = new_axiom
   `!x y. field_star_add y x = x <=> y = field_star_zero`;;

let field_star_neg_inj_imp = new_axiom
   `!x y. field_star_neg x = field_star_neg y ==> x = y`;;

let field_star_neg_inj = new_axiom
   `!x y. field_star_neg x = field_star_neg y <=> x = y`;;

let field_star_neg_zero = new_axiom
   `field_star_neg field_star_zero = field_star_zero`;;

let field_star_neg_neg = new_axiom
   `!x. field_star_neg (field_star_neg x) = x`;;

let field_star_neg_add = new_axiom
   `!x y. field_star_neg (field_star_add x y) = field_star_add (field_star_neg y) (field_star_neg x)`;;

let field_star_neg_left_eq = new_axiom
   `!x y. field_star_add y x = field_star_zero ==> field_star_neg x = y`;;

let field_star_neg_right_eq = new_axiom
   `!x y. field_star_add x y = field_star_zero ==> field_star_neg x = y`;;

let field_star_comm_left_neg_imp = new_axiom
   `!x y.
      field_star_add x y = field_star_add y x ==>
      field_star_add (field_star_neg x) y = field_star_add y (field_star_neg x)`;;

let field_star_comm_left_neg = new_axiom
   `!x y.
      field_star_add (field_star_neg x) y = field_star_add y (field_star_neg x) <=>
      field_star_add x y = field_star_add y x`;;

let field_star_comm_right_neg_imp = new_axiom
   `!x y.
      field_star_add y x = field_star_add x y ==>
      field_star_add y (field_star_neg x) = field_star_add (field_star_neg x) y`;;

let field_star_comm_right_neg = new_axiom
   `!x y.
      field_star_add y (field_star_neg x) = field_star_add (field_star_neg x) y <=>
      field_star_add y x = field_star_add x y`;;

let field_star_comm_left_zero = new_axiom
   `!x. field_star_add field_star_zero x = field_star_add x field_star_zero`;;

let field_star_comm_right_zero = new_axiom
   `!x. field_star_add x field_star_zero = field_star_add field_star_zero x`;;

let field_star_comm_left_add = new_axiom
   `!x y z.
      field_star_add x z = field_star_add z x /\
      field_star_add y z = field_star_add z y ==>
      field_star_add (field_star_add x y) z = field_star_add z (field_star_add x y)`;;

let field_star_comm_right_add = new_axiom
   `!x y z.
      field_star_add z x = field_star_add x z /\
      field_star_add z y = field_star_add y z ==>
      field_star_add z (field_star_add x y) = field_star_add (field_star_add x y) z`;;

new_constant ("field_star_sub", `:field_star -> field_star -> field_star`);;

let field_star_sub_def = new_axiom
  `!(x : field_star) (y : field_star). field_star_sub x y = field_star_add x (field_star_neg y)`;;

let field_star_sub_left_zero = new_axiom
   `!x. field_star_sub field_star_zero x = field_star_neg x`;;

let field_star_sub_right_zero = new_axiom
   `!x. field_star_sub x field_star_zero = x`;;

let field_star_sub_refl = new_axiom
   `!x. field_star_sub x x = field_star_zero`;;

let field_star_neg_sub = new_axiom
   `!x y. field_star_neg (field_star_sub x y) = field_star_sub y x`;;

let field_star_comm_left_sub = new_axiom
   `!x y z.
      field_star_add x z = field_star_add z x /\
      field_star_add y z = field_star_add z y ==>
      field_star_add (field_star_sub x y) z = field_star_add z (field_star_sub x y)`;;

let field_star_comm_right_sub = new_axiom
   `!x y z.
      field_star_add z x = field_star_add x z /\
      field_star_add z y = field_star_add y z ==>
      field_star_add z (field_star_sub x y) = field_star_add (field_star_sub x y) z`;;

new_constant ("field_star_mult", `:field_star -> num -> field_star`);;

let field_star_mult_right_zero = new_axiom
  `!x. field_star_mult x 0 = field_star_zero`;;

let field_star_mult_right_suc = new_axiom
  `!x n. field_star_mult x (SUC n) = field_star_add x (field_star_mult x n)`;;

let field_star_mult_def = CONJ field_star_mult_right_zero field_star_mult_right_suc;;

let field_star_mult_left_zero = new_axiom
   `!n. field_star_mult field_star_zero n = field_star_zero`;;

let field_star_mult_right_one = new_axiom
   `!x. field_star_mult x 1 = x`;;

let field_star_mult_right_two = new_axiom
   `!x. field_star_mult x 2 = field_star_add x x`;;

let field_star_mult_right_add = new_axiom
   `!x m n.
      field_star_mult x (m + n) = field_star_add (field_star_mult x m) (field_star_mult x n)`;;

let field_star_mult_right_suc' = new_axiom
   `!x n. field_star_mult x (SUC n) = field_star_add (field_star_mult x n) x`;;

let field_star_mult_right_mult = new_axiom
   `!x m n. field_star_mult x (m * n) = field_star_mult (field_star_mult x m) n`;;

let field_star_comm_left_mult = new_axiom
   `!x n y.
      field_star_add x y = field_star_add y x ==>
      field_star_add (field_star_mult x n) y = field_star_add y (field_star_mult x n)`;;

let field_star_comm_right_mult = new_axiom
   `!x n y.
      field_star_add y x = field_star_add x y ==>
      field_star_add y (field_star_mult x n) = field_star_add (field_star_mult x n) y`;;

new_constant ("field_star_mult_add", `:field_star -> field_star -> bool list -> field_star`);;

let field_star_mult_add_nil = new_axiom
    `!z x. field_star_mult_add z x [] = z`;;

let field_star_mult_add_cons = new_axiom
     `!z x h t.
        field_star_mult_add z x (CONS h t) =
        field_star_mult_add (if h then field_star_add z x else z)
          (field_star_add x x) t`;;

let field_star_mult_add_def = CONJ field_star_mult_add_nil field_star_mult_add_cons;;

let field_star_mult_add_invariant = new_axiom
   `!z x l.
      field_star_mult_add z x l =
      field_star_add z (field_star_mult x (bits_to_num l))`;;

let field_star_mult_add_correct = new_axiom
   `!x n.
      field_star_mult x n =
      field_star_mult_add field_star_zero x (num_to_bits n)`;;

let field_star_neg_mult = new_axiom
   `!x n. field_star_neg (field_star_mult x n) = field_star_mult (field_star_neg x) n`;;

new_constant
  ("field_star_mult_sub",
   `:bool -> field_star -> field_star -> field_star -> field_star -> bool list -> field_star`);;

let field_star_mult_sub_nil = new_axiom
    `(!b n d f p.
        field_star_mult_sub b n d f p [] =
        if b then field_star_sub n d else field_star_sub d n)`;;

let field_star_mult_sub_cons = new_axiom
    `(!b n d f p h t.
        field_star_mult_sub b n d f p (CONS h t) =
        let s = field_star_sub p f in
        field_star_mult_sub (~b) d (if h then field_star_sub n s else n) s f t)`;;

let field_star_mult_sub_def = CONJ field_star_mult_sub_nil field_star_mult_sub_cons;;

let field_star_mult_sub_invariant = new_axiom
   `!x n d f p l.
      field_star_add x n = field_star_add n x /\
      field_star_add x d = field_star_add d x ==>
      field_star_mult_sub T n d (field_star_mult x f) (field_star_neg (field_star_mult x p)) l =
      field_star_add (field_star_sub n d) (field_star_mult x (decode_fib_dest f p l)) /\
      field_star_mult_sub F n d (field_star_neg (field_star_mult x f)) (field_star_mult x p) l =
      field_star_add (field_star_sub d n) (field_star_mult x (decode_fib_dest f p l))`;;

let field_star_mult_sub_correct = new_axiom
   `!x n.
      field_star_mult x n =
      field_star_mult_sub T field_star_zero field_star_zero x field_star_zero (encode_fib n)`;;

new_constant
  ("field_star_elgamal_encrypt",
   `:field_star -> field_star -> field_star -> num -> field_star # field_star`);;

let field_star_elgamal_encrypt_def = new_axiom
  `!g h m k.
     field_star_elgamal_encrypt g h m k =
     (field_star_mult g k, field_star_add (field_star_mult h k) m)`;;

new_constant
  ("field_star_elgamal_decrypt",
   `:num -> field_star # field_star -> field_star`);;

let field_star_elgamal_decrypt_def = new_axiom
  `!x a b.
     field_star_elgamal_decrypt x (a,b) =
     field_star_add (field_star_neg (field_star_mult a x)) b`;;

let field_star_elgamal_correct = new_axiom
   `!g h m k x.
      (h = field_star_mult g x) ==>
      (field_star_elgamal_decrypt x (field_star_elgamal_encrypt g h m k) = m)`;;

let field_star_add_comm' = new_axiom
   `!x y z. field_star_add x (field_star_add y z) = field_star_add y (field_star_add x z)`;;
(*END-PARAMETRIC*)

(*BEGIN-PARAMETRIC*)
(* field_star-def *)

new_constant ("field_star_sub", `:field_star -> field_star -> field_star`);;

let field_star_sub_def = new_axiom
  `!(x : field_star) (y : field_star). field_star_sub x y = field_star_add x (field_star_neg y)`;;

(* field_star-thm *)

let field_star_add_left_neg' = new_axiom
   `!x y. field_star_add (field_star_neg x) (field_star_add x y) = y`;;

let field_star_add_right_neg = new_axiom
   `!x. field_star_add x (field_star_neg x) = field_star_zero`;;

let field_star_add_right_neg' = new_axiom
   `!x y. field_star_add x (field_star_add (field_star_neg x) y) = y`;;

let field_star_add_right_zero = new_axiom
   `!x. field_star_add x field_star_zero = x`;;

let field_star_comm_left_zero = new_axiom
   `!x. field_star_add field_star_zero x = field_star_add x field_star_zero`;;

let field_star_comm_right_zero = new_axiom
   `!x. field_star_add x field_star_zero = field_star_add field_star_zero x`;;

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

(* field_star-mult-def *)

new_constant ("field_star_scale", `:field_star -> num -> field_star`);;

let field_star_scale_zero = new_axiom
  `!x. field_star_scale x 0 = field_star_zero`;;

let field_star_scale_suc = new_axiom
  `!x n. field_star_scale x (SUC n) = field_star_add x (field_star_scale x n)`;;

let field_star_scale_def = CONJ field_star_scale_zero field_star_scale_suc;;

(* field_star-mult-thm *)

let field_star_zero_scale = new_axiom
   `!n. field_star_scale field_star_zero n = field_star_zero`;;

let field_star_scale_one = new_axiom
   `!x. field_star_scale x 1 = x`;;

let field_star_scale_two = new_axiom
   `!x. field_star_scale x 2 = field_star_add x x`;;

let field_star_scale_add = new_axiom
   `!x m n.
      field_star_scale x (m + n) = field_star_add (field_star_scale x m) (field_star_scale x n)`;;

let field_star_scale_suc' = new_axiom
   `!x n. field_star_scale x (SUC n) = field_star_add (field_star_scale x n) x`;;

let field_star_scale_scale = new_axiom
   `!x m n. field_star_scale x (m * n) = field_star_scale (field_star_scale x m) n`;;

let field_star_comm_left_scale = new_axiom
   `!x n y.
      field_star_add x y = field_star_add y x ==>
      field_star_add (field_star_scale x n) y = field_star_add y (field_star_scale x n)`;;

let field_star_comm_right_scale = new_axiom
   `!x n y.
      field_star_add y x = field_star_add x y ==>
      field_star_add y (field_star_scale x n) = field_star_add (field_star_scale x n) y`;;

(* field_star-mult-add-def *)

new_constant ("field_star_scale_add", `:field_star -> field_star -> bool list -> field_star`);;

let field_star_scale_add_nil = new_axiom
    `!z x. field_star_scale_add z x [] = z`;;

let field_star_scale_add_cons = new_axiom
     `!z x h t.
        field_star_scale_add z x (CONS h t) =
        field_star_scale_add (if h then field_star_add z x else z) (field_star_add x x) t`;;

let field_star_scale_add_def = CONJ field_star_scale_add_nil field_star_scale_add_cons;;

(* field_star-mult-add-thm *)

let field_star_scale_add_invariant = new_axiom
   `!z x l.
      field_star_scale_add z x l =
      field_star_add z (field_star_scale x (bits_to_num l))`;;

let field_star_scale_add_correct = new_axiom
   `!x n.
      field_star_scale x n =
      field_star_scale_add field_star_zero x (num_to_bits n)`;;

(* field_star-mult-sub-def *)

new_constant
  ("field_star_scale_sub",
   `:bool -> field_star -> field_star -> field_star -> field_star -> bool list -> field_star`);;

let field_star_scale_sub_nil = new_axiom
    `(!b n d f p.
        field_star_scale_sub b n d f p [] =
        if b then field_star_sub n d else field_star_sub d n)`;;

let field_star_scale_sub_cons = new_axiom
    `(!b n d f p h t.
        field_star_scale_sub b n d f p (CONS h t) =
        let s = field_star_sub p f in
        field_star_scale_sub (~b) d (if h then field_star_sub n s else n) s f t)`;;

let field_star_scale_sub_def = CONJ field_star_scale_sub_nil field_star_scale_sub_cons;;

(* field_star-mult-sub-thm *)

let field_star_scale_sub_invariant = new_axiom
   `!x n d f p l.
      field_star_add x n = field_star_add n x /\
      field_star_add x d = field_star_add d x ==>
      field_star_scale_sub T n d (field_star_scale x f) (field_star_neg (field_star_scale x p)) l =
      field_star_add (field_star_sub n d) (field_star_scale x (decode_fib_dest f p l)) /\
      field_star_scale_sub F n d (field_star_neg (field_star_scale x f)) (field_star_scale x p) l =
      field_star_add (field_star_sub d n) (field_star_scale x (decode_fib_dest f p l))`;;

let field_star_scale_sub_correct = new_axiom
   `!x n.
      field_star_scale x n =
      field_star_scale_sub T field_star_zero field_star_zero x field_star_zero (encode_fib n)`;;

(* field_star-crypt-def *)

new_constant
  ("field_star_elgamal_encrypt",
   `:field_star -> field_star -> field_star -> num -> field_star # field_star`);;

let field_star_elgamal_encrypt_def = new_axiom
  `!g h m k.
     field_star_elgamal_encrypt g h m k =
     (field_star_scale g k, field_star_add (field_star_scale h k) m)`;;

new_constant
  ("field_star_elgamal_decrypt",
   `:num -> field_star # field_star -> field_star`);;

let field_star_elgamal_decrypt_def = new_axiom
  `!x a b.
     field_star_elgamal_decrypt x (a,b) =
     field_star_add (field_star_neg (field_star_scale a x)) b`;;

(* field_star-crypt-thm *)

let field_star_elgamal_correct = new_axiom
   `!g h m k x.
      (h = field_star_scale g x) ==>
      (field_star_elgamal_decrypt x (field_star_elgamal_encrypt g h m k) = m)`;;

(* field_star-abelian *)

let field_star_add_comm' = new_axiom
   `!x y z. field_star_add x (field_star_add y z) = field_star_add y (field_star_add x z)`;;
(*END-PARAMETRIC*)

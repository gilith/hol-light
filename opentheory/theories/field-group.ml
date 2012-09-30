(* field *)

(* field-def *)

new_constant ("field_sub", `:field -> field -> field`);;

let field_sub_def = new_axiom
  `!(x : field) (y : field). field_sub x y = field_add x (field_neg y)`;;

(* field-thm *)

let field_add_left_neg' = new_axiom
   `!x y. field_add (field_neg x) (field_add x y) = y`;;

let field_add_right_neg = new_axiom
   `!x. field_add x (field_neg x) = field_zero`;;

let field_add_right_neg' = new_axiom
   `!x y. field_add x (field_add (field_neg x) y) = y`;;

let field_add_right_zero = new_axiom
   `!x. field_add x field_zero = x`;;

let field_comm_left_zero = new_axiom
   `!x. field_add field_zero x = field_add x field_zero`;;

let field_comm_right_zero = new_axiom
   `!x. field_add x field_zero = field_add field_zero x`;;

let field_add_left_cancel_imp = new_axiom
   `!x y z. field_add x y = field_add x z ==> y = z`;;

let field_add_left_cancel = new_axiom
   `!x y z. field_add x y = field_add x z <=> y = z`;;

let field_add_left_cancel_zero_imp = new_axiom
   `!x y. field_add x y = x ==> y = field_zero`;;

let field_add_left_cancel_zero = new_axiom
   `!x y. field_add x y = x <=> y = field_zero`;;

let field_add_right_cancel_imp = new_axiom
   `!x y z. field_add y x = field_add z x ==> y = z`;;

let field_add_right_cancel = new_axiom
   `!x y z. field_add y x = field_add z x <=> y = z`;;

let field_add_right_cancel_zero_imp = new_axiom
   `!x y. field_add y x = x ==> y = field_zero`;;

let field_add_right_cancel_zero = new_axiom
   `!x y. field_add y x = x <=> y = field_zero`;;

let field_comm_left_add = new_axiom
   `!x y z.
      field_add x z = field_add z x /\
      field_add y z = field_add z y ==>
      field_add (field_add x y) z = field_add z (field_add x y)`;;

let field_comm_right_add = new_axiom
   `!x y z.
      field_add z x = field_add x z /\
      field_add z y = field_add y z ==>
      field_add z (field_add x y) = field_add (field_add x y) z`;;

let field_neg_inj_imp = new_axiom
   `!x y. field_neg x = field_neg y ==> x = y`;;

let field_neg_inj = new_axiom
   `!x y. field_neg x = field_neg y <=> x = y`;;

let field_neg_zero = new_axiom
   `field_neg field_zero = field_zero`;;

let field_neg_neg = new_axiom
   `!x. field_neg (field_neg x) = x`;;

let field_neg_add = new_axiom
   `!x y. field_neg (field_add x y) = field_add (field_neg y) (field_neg x)`;;

let field_comm_left_neg_imp = new_axiom
   `!x y.
      field_add x y = field_add y x ==>
      field_add (field_neg x) y = field_add y (field_neg x)`;;

let field_comm_left_neg = new_axiom
   `!x y.
      field_add (field_neg x) y = field_add y (field_neg x) <=>
      field_add x y = field_add y x`;;

let field_comm_right_neg_imp = new_axiom
   `!x y.
      field_add y x = field_add x y ==>
      field_add y (field_neg x) = field_add (field_neg x) y`;;

let field_comm_right_neg = new_axiom
   `!x y.
      field_add y (field_neg x) = field_add (field_neg x) y <=>
      field_add y x = field_add x y`;;

let field_sub_left_zero = new_axiom
   `!x. field_sub field_zero x = field_neg x`;;

let field_sub_right_zero = new_axiom
   `!x. field_sub x field_zero = x`;;

let field_sub_refl = new_axiom
   `!x. field_sub x x = field_zero`;;

let field_neg_sub = new_axiom
   `!x y. field_neg (field_sub x y) = field_sub y x`;;

let field_comm_left_sub = new_axiom
   `!x y z.
      field_add x z = field_add z x /\
      field_add y z = field_add z y ==>
      field_add (field_sub x y) z = field_add z (field_sub x y)`;;

let field_comm_right_sub = new_axiom
   `!x y z.
      field_add z x = field_add x z /\
      field_add z y = field_add y z ==>
      field_add z (field_sub x y) = field_add (field_sub x y) z`;;

(* field-mult-def *)

new_constant ("field_scale", `:field -> num -> field`);;

let field_scale_zero = new_axiom
  `!x. field_scale x 0 = field_zero`;;

let field_scale_suc = new_axiom
  `!x n. field_scale x (SUC n) = field_add x (field_scale x n)`;;

let field_scale_def = CONJ field_scale_zero field_scale_suc;;

(* field-mult-thm *)

let field_zero_scale = new_axiom
   `!n. field_scale field_zero n = field_zero`;;

let field_scale_one = new_axiom
   `!x. field_scale x 1 = x`;;

let field_scale_two = new_axiom
   `!x. field_scale x 2 = field_add x x`;;

let field_scale_add = new_axiom
   `!x m n.
      field_scale x (m + n) = field_add (field_scale x m) (field_scale x n)`;;

let field_scale_suc' = new_axiom
   `!x n. field_scale x (SUC n) = field_add (field_scale x n) x`;;

let field_scale_scale = new_axiom
   `!x m n. field_scale x (m * n) = field_scale (field_scale x m) n`;;

let field_comm_left_scale = new_axiom
   `!x n y.
      field_add x y = field_add y x ==>
      field_add (field_scale x n) y = field_add y (field_scale x n)`;;

let field_comm_right_scale = new_axiom
   `!x n y.
      field_add y x = field_add x y ==>
      field_add y (field_scale x n) = field_add (field_scale x n) y`;;

(* field-mult-add-def *)

new_constant ("field_scale_add", `:field -> field -> bool list -> field`);;

let field_scale_add_nil = new_axiom
    `!z x. field_scale_add z x [] = z`;;

let field_scale_add_cons = new_axiom
     `!z x h t.
        field_scale_add z x (CONS h t) =
        field_scale_add (if h then field_add z x else z) (field_add x x) t`;;

let field_scale_add_def = CONJ field_scale_add_nil field_scale_add_cons;;

(* field-mult-add-thm *)

let field_scale_add_invariant = new_axiom
   `!z x l.
      field_scale_add z x l =
      field_add z (field_scale x (bits_to_num l))`;;

let field_scale_add_correct = new_axiom
   `!x n.
      field_scale x n =
      field_scale_add field_zero x (num_to_bits n)`;;

(* field-mult-sub-def *)

new_constant
  ("field_scale_sub",
   `:bool -> field -> field -> field -> field -> bool list -> field`);;

let field_scale_sub_nil = new_axiom
    `(!b n d f p.
        field_scale_sub b n d f p [] =
        if b then field_sub n d else field_sub d n)`;;

let field_scale_sub_cons = new_axiom
    `(!b n d f p h t.
        field_scale_sub b n d f p (CONS h t) =
        let s = field_sub p f in
        field_scale_sub (~b) d (if h then field_sub n s else n) s f t)`;;

let field_scale_sub_def = CONJ field_scale_sub_nil field_scale_sub_cons;;

(* field-mult-sub-thm *)

let field_scale_sub_invariant = new_axiom
   `!x n d f p l.
      field_add x n = field_add n x /\
      field_add x d = field_add d x ==>
      field_scale_sub T n d (field_scale x f) (field_neg (field_scale x p)) l =
      field_add (field_sub n d) (field_scale x (decode_fib_dest f p l)) /\
      field_scale_sub F n d (field_neg (field_scale x f)) (field_scale x p) l =
      field_add (field_sub d n) (field_scale x (decode_fib_dest f p l))`;;

let field_scale_sub_correct = new_axiom
   `!x n.
      field_scale x n =
      field_scale_sub T field_zero field_zero x field_zero (encode_fib n)`;;

(* field-crypt-def *)

new_constant
  ("field_elgamal_encrypt",
   `:field -> field -> field -> num -> field # field`);;

let field_elgamal_encrypt_def = new_axiom
  `!g h m k.
     field_elgamal_encrypt g h m k =
     (field_scale g k, field_add (field_scale h k) m)`;;

new_constant
  ("field_elgamal_decrypt",
   `:num -> field # field -> field`);;

let field_elgamal_decrypt_def = new_axiom
  `!x a b.
     field_elgamal_decrypt x (a,b) =
     field_add (field_neg (field_scale a x)) b`;;

(* field-crypt-thm *)

let field_elgamal_correct = new_axiom
   `!g h m k x.
      (h = field_scale g x) ==>
      (field_elgamal_decrypt x (field_elgamal_encrypt g h m k) = m)`;;

(* field-abelian *)

let field_add_comm' = new_axiom
   `!x y z. field_add x (field_add y z) = field_add y (field_add x z)`;;

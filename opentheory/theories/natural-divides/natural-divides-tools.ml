(* ========================================================================= *)
(* PROOF TOOLS FOR THE DIVIDES RELATION ON NATURAL NUMBERS                   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Divides functions operating on ML numerals.                               *)
(* ------------------------------------------------------------------------- *)

(* Given a and b such that ~(a = 0), returns (s,t,g) satisfying *)
(* s * a = t * b + g /\ g = gcd a b *)
let egcd_num =
    let rec egcd a b =
        if eq_num b num_0 then (num_1,num_0,a)
        else if le_num a b then
          let q = quo_num b a in
          let b = sub_num b (mult_num q a) in
          let (s,t,g) = egcd a b in
          (add_num s (mult_num q t), t, g)
        else
          let q = quo_num a b in
          let a = sub_num a (mult_num q b) in
          if eq_num a num_0 then (num_1, sub_num q num_1, b) else
          let (s,t,g) = egcd a b in
          (s, add_num (mult_num q s) t, g) in
    egcd;;

(* ------------------------------------------------------------------------- *)
(* A simple proof tool to calculate the gcd of two numerals.                 *)
(* ------------------------------------------------------------------------- *)

let prove_egcd a b =
    let (s,t,g) = egcd_num (dest_numeral a) (dest_numeral b) in
    let mk_mult = mk_binop `( * ) : num -> num -> num` in
    let mk_add = mk_binop `( + ) : num -> num -> num` in
    let tm =
        mk_eq (mk_mult (mk_numeral s) a,
               mk_add (mk_mult (mk_numeral t) b) (mk_numeral g)) in
    EQT_ELIM (NUM_REDUCE_CONV tm);;

(* word10 *)

(* word10-def *)

new_constant ("word10_size", `:num`);;

let word10_size_def = new_axiom
  `word10_size = 2 EXP word10_width`;;

let word10_size_nonzero = new_axiom
  `~(word10_size = 0)`;;

(* word10 *)

(* word10-def *)

let mod_refl_word10_size = new_axiom
  `word10_size MOD word10_size = 0`;;

let mod_lt_word10_size = new_axiom
  `!n. n < word10_size ==> n MOD word10_size = n`;;

let zero_mod_word10_size = new_axiom
  `0 MOD word10_size = 0`;;

let lt_mod_word10_size = new_axiom
  `!n. n MOD word10_size < word10_size`;;

let mod_mod_refl_word10_size = new_axiom
  `!n. n MOD word10_size MOD word10_size = n MOD word10_size`;;

let mod_add_mod_word10_size = new_axiom
  `!m n. (m MOD word10_size + n MOD word10_size) MOD word10_size = (m + n) MOD word10_size`;;

let mod_mult_mod_word10_size = new_axiom
  `!m n. (m MOD word10_size * n MOD word10_size) MOD word10_size = (m * n) MOD word10_size`;;

let divides_mod_word10_size = new_axiom
   `!n. divides word10_size n <=> n MOD word10_size = 0`;;

new_type ("word10",0);;

new_constant ("num_to_word10", `:num -> word10`);;

new_constant ("word10_to_num", `:word10 -> num`);;

let word10_to_num_to_word10 = new_axiom
  `!x. num_to_word10 (word10_to_num x) = x`;;

let num_to_word10_inj = new_axiom
   `!x y.
      x < word10_size /\ y < word10_size /\ num_to_word10 x = num_to_word10 y ==>
      x = y`;;

let num_to_word10_to_num = new_axiom
  `!x. word10_to_num (num_to_word10 x) = x MOD word10_size`;;

new_constant ("word10_add", `:word10 -> word10 -> word10`);;

let num_to_word10_add = new_axiom
  `!x1 y1.
     num_to_word10 (x1 + y1) =
     word10_add (num_to_word10 x1) (num_to_word10 y1)`;;

new_constant ("word10_mult", `:word10 -> word10 -> word10`);;

let num_to_word10_mult = new_axiom
  `!x1 y1.
     num_to_word10 (x1 * y1) =
     word10_mult (num_to_word10 x1) (num_to_word10 y1)`;;

new_constant ("word10_neg", `:word10 -> word10`);;

let word10_neg_def = new_axiom
  `!x. word10_neg x = num_to_word10 (word10_size - word10_to_num x)`;;

new_constant ("word10_sub", `:word10 -> word10 -> word10`);;

let word10_sub_def = new_axiom
  `!x y. word10_sub x y = word10_add x (word10_neg y)`;;

new_constant ("word10_le", `:word10 -> word10 -> bool`);;

let word10_le_def = new_axiom
  `!x y. word10_le x y = word10_to_num x <= word10_to_num y`;;

new_constant ("word10_lt", `:word10 -> word10 -> bool`);;

let word10_lt_def = new_axiom
  `!x y. word10_lt x y = ~(word10_le y x)`;;

(* word10-thm *)

let word10_to_num_inj = new_axiom
  `!x y. word10_to_num x = word10_to_num y ==> x = y`;;

let num_to_word10_eq = new_axiom
   `!x y.
      num_to_word10 x = num_to_word10 y <=> x MOD word10_size = y MOD word10_size`;;

let num_to_word10_is_zero = new_axiom
   `!x. num_to_word10 x = num_to_word10 0 <=> divides word10_size x`;;

let word10_to_num_bound = new_axiom
  `!x. word10_to_num x < word10_size`;;

let word10_to_num_div_bound = new_axiom
  `!x. word10_to_num x DIV word10_size = 0`;;

let word10_to_num_mod_bound = new_axiom
  `!x. word10_to_num x MOD word10_size = word10_to_num x`;;

let word10_add_to_num = new_axiom
   `!x y.
      word10_to_num (word10_add x y) =
      (word10_to_num x + word10_to_num y) MOD word10_size`;;

let word10_mult_to_num = new_axiom
   `!x y.
      word10_to_num (word10_mult x y) =
      (word10_to_num x * word10_to_num y) MOD word10_size`;;

let word10_lt_alt = new_axiom
   `!x y. word10_lt x y = word10_to_num x < word10_to_num y`;;

let num_to_word10_word10_size = new_axiom
   `num_to_word10 word10_size = num_to_word10 0`;;

let word10_add_comm = new_axiom
   `!x y. word10_add x y = word10_add y x`;;

let word10_add_assoc = new_axiom
   `!x y z. word10_add (word10_add x y) z = word10_add x (word10_add y z)`;;

let word10_add_left_zero = new_axiom
   `!x. word10_add (num_to_word10 0) x = x`;;

let word10_add_right_zero = new_axiom
   `!x. word10_add x (num_to_word10 0) = x`;;

let word10_add_left_neg = new_axiom
   `!x. word10_add (word10_neg x) x = num_to_word10 0`;;

let word10_add_right_neg = new_axiom
   `!x. word10_add x (word10_neg x) = num_to_word10 0`;;

let word10_add_left_cancel = new_axiom
   `!x y z. word10_add x y = word10_add x z <=> y = z`;;

let word10_add_right_cancel = new_axiom
   `!x y z. word10_add y x = word10_add z x <=> y = z`;;

let word10_add_left_cancel_zero = new_axiom
   `!x y. word10_add x y = x <=> y = num_to_word10 0`;;

let word10_add_right_cancel_zero = new_axiom
   `!x y. word10_add y x = x <=> y = num_to_word10 0`;;

let word10_neg_neg = new_axiom
   `!x. word10_neg (word10_neg x) = x`;;

let word10_neg_inj = new_axiom
   `!x y. word10_neg x = word10_neg y ==> x = y`;;

let word10_neg_zero = new_axiom
   `word10_neg (num_to_word10 0) = num_to_word10 0`;;

let word10_neg_is_zero = new_axiom
   `!x. word10_neg x = num_to_word10 0 <=> x = num_to_word10 0`;;

let word10_neg_add = new_axiom
   `!x y.
      word10_add (word10_neg x) (word10_neg y) =
      word10_neg (word10_add x y)`;;

let word10_mult_comm = new_axiom
   `!x y. word10_mult x y = word10_mult y x`;;

let word10_mult_assoc = new_axiom
   `!x y z.
      word10_mult (word10_mult x y) z = word10_mult x (word10_mult y z)`;;

let word10_add_left_distrib = new_axiom
   `!x y z.
      word10_mult x (word10_add y z) =
      word10_add (word10_mult x y) (word10_mult x z)`;;

let word10_add_right_distrib = new_axiom
   `!x y z.
      word10_mult (word10_add y z) x =
      word10_add (word10_mult y x) (word10_mult z x)`;;

let word10_mult_left_zero = new_axiom
   `!x. word10_mult (num_to_word10 0) x = num_to_word10 0`;;

let word10_mult_right_zero = new_axiom
   `!x. word10_mult x (num_to_word10 0) = num_to_word10 0`;;

let word10_mult_left_one = new_axiom
   `!x. word10_mult (num_to_word10 1) x = x`;;

let word10_mult_right_one = new_axiom
   `!x. word10_mult x (num_to_word10 1) = x`;;

let word10_mult_left_neg = new_axiom
   `!x y. word10_mult (word10_neg x) y = word10_neg (word10_mult x y)`;;

let word10_mult_right_neg = new_axiom
   `!x y. word10_mult x (word10_neg y) = word10_neg (word10_mult x y)`;;

(* word10-bits-def *)

new_constant ("word10_shl", `:word10 -> num -> word10`);;

let word10_shl_def = new_axiom
  `!w n. word10_shl w n = num_to_word10 ((2 EXP n) * word10_to_num w)`;;

new_constant ("word10_shr", `:word10 -> num -> word10`);;

let word10_shr_def = new_axiom
  `!w n. word10_shr w n = num_to_word10 (word10_to_num w DIV (2 EXP n))`;;

new_constant ("word10_bit", `:word10 -> num -> bool`);;

let word10_bit_def = new_axiom
  `!w n. word10_bit w n = ODD (word10_to_num (word10_shr w n))`;;

new_constant ("word10_to_list", `:word10 -> bool list`);;

let word10_to_list_def = new_axiom
  `!w. word10_to_list w = MAP (word10_bit w) (interval 0 word10_width)`;;

new_constant ("list_to_word10", `:bool list -> word10`);;

let list_to_word10_nil = new_axiom
  `list_to_word10 [] = num_to_word10 0`
and list_to_word10_cons = new_axiom
  `!h t.
     list_to_word10 (CONS h t) =
     if h then word10_add (word10_shl (list_to_word10 t) 1) (num_to_word10 1)
     else word10_shl (list_to_word10 t) 1`;;

let list_to_word10_def = CONJ list_to_word10_nil list_to_word10_cons;;

new_constant ("is_word10_list", `:bool list -> bool`);;

let is_word10_list_def = new_axiom
  `!l. is_word10_list (l : bool list) <=> LENGTH l = word10_width`;;

new_constant ("word10_and", `:word10 -> word10 -> word10`);;

let word10_and_def = new_axiom
  `!w1 w2.
     word10_and w1 w2 =
     list_to_word10 (zipwith ( /\ ) (word10_to_list w1) (word10_to_list w2))`;;

new_constant ("word10_or", `:word10 -> word10 -> word10`);;

let word10_or_def = new_axiom
  `!w1 w2.
     word10_or w1 w2 =
     list_to_word10 (zipwith ( \/ ) (word10_to_list w1) (word10_to_list w2))`;;

new_constant ("word10_not", `:word10 -> word10`);;

let word10_not_def = new_axiom
  `!w. word10_not w = list_to_word10 (MAP (~) (word10_to_list w))`;;

new_constant ("word10_bits_lte", `:bool -> bool list -> bool list -> bool`);;

let word10_bits_lte_nil = new_axiom
   `!q. word10_bits_lte q [] [] = q`
and word10_bits_lte_cons = new_axiom
   `!q h1 h2 t1 t2.
      word10_bits_lte q (CONS h1 t1) (CONS h2 t2) =
      word10_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`;;

let word10_bits_lte_def = CONJ word10_bits_lte_nil word10_bits_lte_cons;;

(* word10-bits-thm *)

let length_word10_to_list = new_axiom
  `!w. LENGTH (word10_to_list w) = word10_width`;;

let is_word10_to_list = new_axiom
  `!w. is_word10_list (word10_to_list w)`;;

let word10_bit_div = new_axiom
  `!w n. word10_bit w n = ODD (word10_to_num w DIV (2 EXP n))`;;

let nil_to_word10_to_num = new_axiom
  `word10_to_num (list_to_word10 []) = 0`;;

let cons_to_word10_to_num = new_axiom
   `!h t.
      word10_to_num (list_to_word10 (CONS h t)) =
      (2 * word10_to_num (list_to_word10 t) + (if h then 1 else 0)) MOD word10_size`;;

let list_to_word10_to_num_bound = new_axiom
  `!l. word10_to_num (list_to_word10 l) < 2 EXP (LENGTH l)`;;

let list_to_word10_to_num_bound_suc = new_axiom
  `!l. 2 * word10_to_num (list_to_word10 l) + 1 < 2 EXP (SUC (LENGTH l))`;;

let cons_to_word10_to_num_bound = new_axiom
   `!h t.
      2 * word10_to_num (list_to_word10 t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`;;

let word10_to_list_to_word10 = new_axiom
  `!w. list_to_word10 (word10_to_list w) = w`;;

let word10_to_list_inj = new_axiom
  `!w1 w2. word10_to_list w1 = word10_to_list w2 ==> w1 = w2`;;

let word10_to_list_inj_eq = new_axiom
  `!w1 w2. word10_to_list w1 = word10_to_list w2 <=> w1 = w2`;;

let list_to_word10_bit = new_axiom
   `!l n.
      word10_bit (list_to_word10 l) n =
      (n < word10_width /\ n < LENGTH l /\ EL n l)`;;

let short_list_to_word10_to_list = new_axiom
   `!l.
      LENGTH l <= word10_width ==>
      word10_to_list (list_to_word10 l) =
      APPEND l (REPLICATE (word10_width - LENGTH l) F)`;;

let long_list_to_word10_to_list = new_axiom
   `!l.
      word10_width <= LENGTH l ==>
      word10_to_list (list_to_word10 l) = take word10_width l`;;

let list_to_word10_to_list_eq = new_axiom
   `!l.
      word10_to_list (list_to_word10 l) =
      if LENGTH l <= word10_width then
        APPEND l (REPLICATE (word10_width - LENGTH l) F)
      else
        take word10_width l`;;

let list_to_word10_to_list = new_axiom
  `!l. LENGTH l = word10_width <=> word10_to_list (list_to_word10 l) = l`;;

let word10_shl_list = new_axiom
   `!l n.
      word10_shl (list_to_word10 l) n =
      list_to_word10 (APPEND (REPLICATE n F) l)`;;

let short_word10_shr_list = new_axiom
   `!l n.
      LENGTH l <= word10_width ==>
      word10_shr (list_to_word10 l) n =
      (if LENGTH l <= n then list_to_word10 []
       else list_to_word10 (drop n l))`;;

let long_word10_shr_list = new_axiom
   `!l n.
      word10_width <= LENGTH l ==>
      word10_shr (list_to_word10 l) n =
      if word10_width <= n then list_to_word10 []
      else list_to_word10 (drop n (take word10_width l))`;;

let word10_shr_list = new_axiom
   `!l n.
      word10_shr (list_to_word10 l) n =
      (if LENGTH l <= word10_width then
         if LENGTH l <= n then list_to_word10 []
         else list_to_word10 (drop n l)
       else
         if word10_width <= n then list_to_word10 []
         else list_to_word10 (drop n (take word10_width l)))`;;

let word10_eq_bits = new_axiom
  `!w1 w2. (!i. i < word10_width ==> word10_bit w1 i = word10_bit w2 i) ==> w1 = w2`;;

let num_to_word10_cons = new_axiom
  `!n.
     list_to_word10 (CONS (ODD n) (word10_to_list (num_to_word10 (n DIV 2)))) =
     num_to_word10 n`;;

let num_to_word10_list = new_axiom
  `!n.
     num_to_word10 n =
     list_to_word10
       (if n = 0 then []
        else CONS (ODD n) (word10_to_list (num_to_word10 (n DIV 2))))`;;

let word10_lte_list = new_axiom
   `!q w1 w2.
      word10_bits_lte q (word10_to_list w1) (word10_to_list w2) <=>
      (if q then word10_le w1 w2 else word10_lt w1 w2)`;;

let word10_le_list = new_axiom
   `!w1 w2.
      word10_bits_lte T (word10_to_list w1) (word10_to_list w2) <=> word10_le w1 w2`;;

let word10_lt_list = new_axiom
   `!w1 w2.
      word10_bits_lte F (word10_to_list w1) (word10_to_list w2) <=> word10_lt w1 w2`;;

let word10_le_refl = new_axiom
  `!w. word10_le w w`;;

let word10_le_trans = new_axiom
  `!w1 w2 w3. word10_le w1 w2 /\ word10_le w2 w3 ==> word10_le w1 w3`;;

let word10_lt_refl = new_axiom
  `!w. ~word10_lt w w`;;

let word10_lte_trans = new_axiom
  `!w1 w2 w3. word10_lt w1 w2 /\ word10_le w2 w3 ==> word10_lt w1 w3`;;

let word10_let_trans = new_axiom
  `!w1 w2 w3. word10_le w1 w2 /\ word10_lt w2 w3 ==> word10_lt w1 w3`;;

let word10_lt_trans = new_axiom
  `!w1 w2 w3. word10_lt w1 w2 /\ word10_lt w2 w3 ==> word10_lt w1 w3`;;

let word10_reduce_conv =
    REWRITE_CONV
      [word10_to_num_to_word10;
       word10_le_def; word10_lt_def] THENC
    REWRITE_CONV
      [num_to_word10_to_num] THENC
    REWRITE_CONV
      [word10_width_def; word10_size_def; num_to_word10_eq] THENC
    NUM_REDUCE_CONV;;

let word10_width_conv = REWR_CONV word10_width_def;;

let list_to_word10_to_list_conv =
    REWR_CONV list_to_word10_to_list_eq THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word10_width_conv THENC
       NUM_REDUCE_CONV)
      (RAND_CONV
         ((RATOR_CONV o RAND_CONV)
            (RATOR_CONV (RAND_CONV word10_width_conv) THENC
             RAND_CONV length_conv THENC
             NUM_REDUCE_CONV) THENC
          replicate_conv) THENC
       append_conv)
      (RATOR_CONV (RAND_CONV word10_width_conv) THENC
       take_conv);;

let numeral_to_word10_list_conv =
    let zero_conv = REWR_CONV (SYM (CONJUNCT1 list_to_word10_def)) in
    let numeral_conv = REWR_CONV (SYM (SPEC `NUMERAL n` num_to_word10_cons)) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (numeral_conv THENC
          RAND_CONV
            (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV) THENC
             RAND_CONV
               (RAND_CONV
                  (RAND_CONV NUM_REDUCE_CONV THENC
                   rewr_conv) THENC
                list_to_word10_to_list_conv)))) tm in
    rewr_conv;;

let word10_and_list_conv =
    let th = SPECL [`list_to_word10 l1`; `list_to_word10 l2`] word10_and_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word10_to_list_conv) THENC
       RAND_CONV list_to_word10_to_list_conv THENC
       zipwith_conv and_simp_conv);;

let word10_or_list_conv =
    let th = SPECL [`list_to_word10 l1`; `list_to_word10 l2`] word10_or_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word10_to_list_conv) THENC
       RAND_CONV list_to_word10_to_list_conv THENC
       zipwith_conv or_simp_conv);;

let word10_shr_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word10_shr_list in
    REWR_CONV th THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word10_width_conv THENC
       NUM_REDUCE_CONV)
      (cond_conv
        (RATOR_CONV (RAND_CONV length_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV drop_conv))
      (cond_conv
        (RATOR_CONV (RAND_CONV word10_width_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV
           (RAND_CONV
              (RATOR_CONV (RAND_CONV word10_width_conv) THENC
               take_conv) THENC
            drop_conv)));;

let word10_shl_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word10_shl_list in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV replicate_conv) THENC
       append_conv);;

let word10_bit_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_word10_bit in
    REWR_CONV th THENC
    andalso_conv
      (RAND_CONV word10_width_conv THENC
       NUM_REDUCE_CONV)
      (andalso_conv
        (RAND_CONV length_conv THENC
         NUM_REDUCE_CONV)
        el_conv);;

let word10_bits_lte_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 word10_bits_lte_def) in
    let cons_conv = REWR_CONV (CONJUNCT2 word10_bits_lte_def) in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          (RATOR_CONV o RATOR_CONV o RAND_CONV)
            ((RATOR_CONV o RAND_CONV)
               (RATOR_CONV (RAND_CONV (TRY_CONV not_simp_conv)) THENC
                TRY_CONV and_simp_conv) THENC
             RAND_CONV
               ((RATOR_CONV o RAND_CONV)
                  (RAND_CONV
                    (RAND_CONV (TRY_CONV not_simp_conv) THENC
                     TRY_CONV and_simp_conv) THENC
                   TRY_CONV not_simp_conv) THENC
                TRY_CONV and_simp_conv) THENC
             TRY_CONV or_simp_conv) THENC
          rewr_conv)) tm in
    rewr_conv;;

let word10_le_list_conv =
    let th = SYM (SPECL [`list_to_word10 l1`; `list_to_word10 l2`] word10_le_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word10_to_list_conv) THENC
    RAND_CONV list_to_word10_to_list_conv THENC
    word10_bits_lte_conv;;

let word10_lt_list_conv =
    let th = SYM (SPECL [`list_to_word10 l1`; `list_to_word10 l2`] word10_lt_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word10_to_list_conv) THENC
    RAND_CONV list_to_word10_to_list_conv THENC
    word10_bits_lte_conv;;

let word10_eq_list_conv =
    let th = SYM (SPECL [`list_to_word10 l1`; `list_to_word10 l2`]
                    word10_to_list_inj_eq) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word10_to_list_conv) THENC
    RAND_CONV list_to_word10_to_list_conv THENC
    list_eq_conv iff_simp_conv;;

let word10_bit_conv =
    word10_width_conv ORELSEC
    list_to_word10_to_list_conv ORELSEC
    numeral_to_word10_list_conv ORELSEC
    word10_and_list_conv ORELSEC
    word10_or_list_conv ORELSEC
    word10_shr_list_conv ORELSEC
    word10_shl_list_conv ORELSEC
    word10_bit_list_conv ORELSEC
    word10_le_list_conv ORELSEC
    word10_lt_list_conv ORELSEC
    word10_eq_list_conv;;

let bit_blast_subterm_conv = word10_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;
let bit_blast_tac = CONV_TAC bit_blast_conv;;

let prove_word10_list_cases n =
    let interval =
        let rec intv i n = if n = 0 then [] else i :: intv (i + 1) (n - 1) in
        intv 0 in
    let lemma1 =
        let nunary = funpow n (fun t -> mk_comb (`SUC`,t)) `0` in
        let goal = mk_eq (`LENGTH (word10_to_list w)`,nunary) in
        let tac =
            REWRITE_TAC [length_word10_to_list; word10_width_def] THEN
            NUM_REDUCE_TAC in
        prove (goal,tac) in
    let witnesses =
        let addtl l = mk_comb (`TL : bool list -> bool list`, hd l) :: l in
        let tls = rev (funpow (n - 1) addtl [`l : bool list`]) in
        map (fun t -> mk_comb (`HD : bool list -> bool`, t)) tls in
    let goal =
        let is = interval n in
        let xs = map (fun i -> mk_var ("x" ^ string_of_int i, bool_ty)) is in
        let w = mk_var ("w", `:word10`) in
        let body = mk_eq (w, mk_comb (`list_to_word10`, mk_list (xs,bool_ty))) in
        mk_forall (w, list_mk_exists (xs,body)) in
    let tac =
        GEN_TAC THEN
        CONV_TAC
          (funpow n (RAND_CONV o ABS_CONV)
             (LAND_CONV (ONCE_REWRITE_CONV [GSYM word10_to_list_to_word10]))) THEN
        MP_TAC lemma1 THEN
        SPEC_TAC (`word10_to_list w`, `l : bool list`) THEN
        REPEAT STRIP_TAC THEN
        EVERY (map EXISTS_TAC witnesses) THEN
        AP_TERM_TAC THEN
        POP_ASSUM MP_TAC THEN
        N_TAC n
          (MP_TAC (ISPEC `l : bool list` list_CASES) THEN
           STRIP_TAC THENL
           [ASM_REWRITE_TAC [LENGTH; NOT_SUC];
            ALL_TAC] THEN
           POP_ASSUM SUBST_VAR_TAC THEN
           REWRITE_TAC [LENGTH; SUC_INJ; HD; TL; CONS_11] THEN
           SPEC_TAC (`t : bool list`, `l : bool list`) THEN
           GEN_TAC) THEN
        REWRITE_TAC [LENGTH_EQ_NIL] in
    prove (goal,tac);;

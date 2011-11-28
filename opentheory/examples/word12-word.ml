(* word12 *)

(* word12-def *)

new_constant ("word12_size", `:num`);;

let word12_size_def = new_axiom
  `word12_size = 2 EXP word12_width`;;

let word12_size_nonzero = new_axiom
  `~(word12_size = 0)`;;

(* word12 *)

(* word12-def *)

let mod_refl_word12_size = new_axiom
  `word12_size MOD word12_size = 0`;;

let mod_lt_word12_size = new_axiom
  `!n. n < word12_size ==> n MOD word12_size = n`;;

let zero_mod_word12_size = new_axiom
  `0 MOD word12_size = 0`;;

let lt_mod_word12_size = new_axiom
  `!n. n MOD word12_size < word12_size`;;

let mod_mod_refl_word12_size = new_axiom
  `!n. n MOD word12_size MOD word12_size = n MOD word12_size`;;

let mod_add_mod_word12_size = new_axiom
  `!m n. (m MOD word12_size + n MOD word12_size) MOD word12_size = (m + n) MOD word12_size`;;

let mod_mult_mod_word12_size = new_axiom
  `!m n. (m MOD word12_size * n MOD word12_size) MOD word12_size = (m * n) MOD word12_size`;;

let divides_mod_word12_size = new_axiom
   `!n. divides word12_size n <=> n MOD word12_size = 0`;;

new_type ("word12",0);;

new_constant ("num_to_word12", `:num -> word12`);;

new_constant ("word12_to_num", `:word12 -> num`);;

let word12_to_num_to_word12 = new_axiom
  `!x. num_to_word12 (word12_to_num x) = x`;;

let num_to_word12_inj = new_axiom
   `!x y.
      x < word12_size /\ y < word12_size /\ num_to_word12 x = num_to_word12 y ==>
      x = y`;;

let num_to_word12_to_num = new_axiom
  `!x. word12_to_num (num_to_word12 x) = x MOD word12_size`;;

new_constant ("word12_add", `:word12 -> word12 -> word12`);;

let num_to_word12_add = new_axiom
  `!x1 y1.
     num_to_word12 (x1 + y1) =
     word12_add (num_to_word12 x1) (num_to_word12 y1)`;;

new_constant ("word12_mult", `:word12 -> word12 -> word12`);;

let num_to_word12_mult = new_axiom
  `!x1 y1.
     num_to_word12 (x1 * y1) =
     word12_mult (num_to_word12 x1) (num_to_word12 y1)`;;

new_constant ("word12_neg", `:word12 -> word12`);;

let word12_neg_def = new_axiom
  `!x. word12_neg x = num_to_word12 (word12_size - word12_to_num x)`;;

new_constant ("word12_sub", `:word12 -> word12 -> word12`);;

let word12_sub_def = new_axiom
  `!x y. word12_sub x y = word12_add x (word12_neg y)`;;

new_constant ("word12_le", `:word12 -> word12 -> bool`);;

let word12_le_def = new_axiom
  `!x y. word12_le x y = word12_to_num x <= word12_to_num y`;;

new_constant ("word12_lt", `:word12 -> word12 -> bool`);;

let word12_lt_def = new_axiom
  `!x y. word12_lt x y = ~(word12_le y x)`;;

(* word12-thm *)

let word12_to_num_inj = new_axiom
  `!x y. word12_to_num x = word12_to_num y ==> x = y`;;

let num_to_word12_eq = new_axiom
   `!x y.
      num_to_word12 x = num_to_word12 y <=> x MOD word12_size = y MOD word12_size`;;

let num_to_word12_is_zero = new_axiom
   `!x. num_to_word12 x = num_to_word12 0 <=> divides word12_size x`;;

let word12_to_num_bound = new_axiom
  `!x. word12_to_num x < word12_size`;;

let word12_to_num_div_bound = new_axiom
  `!x. word12_to_num x DIV word12_size = 0`;;

let word12_to_num_mod_bound = new_axiom
  `!x. word12_to_num x MOD word12_size = word12_to_num x`;;

let word12_add_to_num = new_axiom
   `!x y.
      word12_to_num (word12_add x y) =
      (word12_to_num x + word12_to_num y) MOD word12_size`;;

let word12_mult_to_num = new_axiom
   `!x y.
      word12_to_num (word12_mult x y) =
      (word12_to_num x * word12_to_num y) MOD word12_size`;;

let word12_lt_alt = new_axiom
   `!x y. word12_lt x y = word12_to_num x < word12_to_num y`;;

let num_to_word12_word12_size = new_axiom
   `num_to_word12 word12_size = num_to_word12 0`;;

let word12_add_comm = new_axiom
   `!x y. word12_add x y = word12_add y x`;;

let word12_add_assoc = new_axiom
   `!x y z. word12_add (word12_add x y) z = word12_add x (word12_add y z)`;;

let word12_add_left_zero = new_axiom
   `!x. word12_add (num_to_word12 0) x = x`;;

let word12_add_right_zero = new_axiom
   `!x. word12_add x (num_to_word12 0) = x`;;

let word12_add_left_neg = new_axiom
   `!x. word12_add (word12_neg x) x = num_to_word12 0`;;

let word12_add_right_neg = new_axiom
   `!x. word12_add x (word12_neg x) = num_to_word12 0`;;

let word12_add_left_cancel = new_axiom
   `!x y z. word12_add x y = word12_add x z <=> y = z`;;

let word12_add_right_cancel = new_axiom
   `!x y z. word12_add y x = word12_add z x <=> y = z`;;

let word12_add_left_cancel_zero = new_axiom
   `!x y. word12_add x y = x <=> y = num_to_word12 0`;;

let word12_add_right_cancel_zero = new_axiom
   `!x y. word12_add y x = x <=> y = num_to_word12 0`;;

let word12_neg_neg = new_axiom
   `!x. word12_neg (word12_neg x) = x`;;

let word12_neg_inj = new_axiom
   `!x y. word12_neg x = word12_neg y ==> x = y`;;

let word12_neg_zero = new_axiom
   `word12_neg (num_to_word12 0) = num_to_word12 0`;;

let word12_neg_is_zero = new_axiom
   `!x. word12_neg x = num_to_word12 0 <=> x = num_to_word12 0`;;

let word12_neg_add = new_axiom
   `!x y.
      word12_add (word12_neg x) (word12_neg y) =
      word12_neg (word12_add x y)`;;

let word12_mult_comm = new_axiom
   `!x y. word12_mult x y = word12_mult y x`;;

let word12_mult_assoc = new_axiom
   `!x y z.
      word12_mult (word12_mult x y) z = word12_mult x (word12_mult y z)`;;

let word12_add_left_distrib = new_axiom
   `!x y z.
      word12_mult x (word12_add y z) =
      word12_add (word12_mult x y) (word12_mult x z)`;;

let word12_add_right_distrib = new_axiom
   `!x y z.
      word12_mult (word12_add y z) x =
      word12_add (word12_mult y x) (word12_mult z x)`;;

let word12_mult_left_zero = new_axiom
   `!x. word12_mult (num_to_word12 0) x = num_to_word12 0`;;

let word12_mult_right_zero = new_axiom
   `!x. word12_mult x (num_to_word12 0) = num_to_word12 0`;;

let word12_mult_left_one = new_axiom
   `!x. word12_mult (num_to_word12 1) x = x`;;

let word12_mult_right_one = new_axiom
   `!x. word12_mult x (num_to_word12 1) = x`;;

let word12_mult_left_neg = new_axiom
   `!x y. word12_mult (word12_neg x) y = word12_neg (word12_mult x y)`;;

let word12_mult_right_neg = new_axiom
   `!x y. word12_mult x (word12_neg y) = word12_neg (word12_mult x y)`;;

(* word12-bits-def *)

new_constant ("word12_shl", `:word12 -> num -> word12`);;

let word12_shl_def = new_axiom
  `!w n. word12_shl w n = num_to_word12 ((2 EXP n) * word12_to_num w)`;;

new_constant ("word12_shr", `:word12 -> num -> word12`);;

let word12_shr_def = new_axiom
  `!w n. word12_shr w n = num_to_word12 (word12_to_num w DIV (2 EXP n))`;;

new_constant ("word12_bit", `:word12 -> num -> bool`);;

let word12_bit_def = new_axiom
  `!w n. word12_bit w n = ODD (word12_to_num (word12_shr w n))`;;

new_constant ("word12_to_list", `:word12 -> bool list`);;

let word12_to_list_def = new_axiom
  `!w. word12_to_list w = MAP (word12_bit w) (interval 0 word12_width)`;;

new_constant ("list_to_word12", `:bool list -> word12`);;

let list_to_word12_nil = new_axiom
  `list_to_word12 [] = num_to_word12 0`
and list_to_word12_cons = new_axiom
  `!h t.
     list_to_word12 (CONS h t) =
     if h then word12_add (word12_shl (list_to_word12 t) 1) (num_to_word12 1)
     else word12_shl (list_to_word12 t) 1`;;

let list_to_word12_def = CONJ list_to_word12_nil list_to_word12_cons;;

new_constant ("is_word12_list", `:bool list -> bool`);;

let is_word12_list_def = new_axiom
  `!l. is_word12_list (l : bool list) <=> LENGTH l = word12_width`;;

new_constant ("word12_and", `:word12 -> word12 -> word12`);;

let word12_and_def = new_axiom
  `!w1 w2.
     word12_and w1 w2 =
     list_to_word12 (zipwith ( /\ ) (word12_to_list w1) (word12_to_list w2))`;;

new_constant ("word12_or", `:word12 -> word12 -> word12`);;

let word12_or_def = new_axiom
  `!w1 w2.
     word12_or w1 w2 =
     list_to_word12 (zipwith ( \/ ) (word12_to_list w1) (word12_to_list w2))`;;

new_constant ("word12_not", `:word12 -> word12`);;

let word12_not_def = new_axiom
  `!w. word12_not w = list_to_word12 (MAP (~) (word12_to_list w))`;;

new_constant ("word12_bits_lte", `:bool -> bool list -> bool list -> bool`);;

let word12_bits_lte_nil = new_axiom
   `!q. word12_bits_lte q [] [] = q`
and word12_bits_lte_cons = new_axiom
   `!q h1 h2 t1 t2.
      word12_bits_lte q (CONS h1 t1) (CONS h2 t2) =
      word12_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`;;

let word12_bits_lte_def = CONJ word12_bits_lte_nil word12_bits_lte_cons;;

(* word12-bits-thm *)

let length_word12_to_list = new_axiom
  `!w. LENGTH (word12_to_list w) = word12_width`;;

let is_word12_to_list = new_axiom
  `!w. is_word12_list (word12_to_list w)`;;

let word12_bit_div = new_axiom
  `!w n. word12_bit w n = ODD (word12_to_num w DIV (2 EXP n))`;;

let nil_to_word12_to_num = new_axiom
  `word12_to_num (list_to_word12 []) = 0`;;

let cons_to_word12_to_num = new_axiom
   `!h t.
      word12_to_num (list_to_word12 (CONS h t)) =
      (2 * word12_to_num (list_to_word12 t) + (if h then 1 else 0)) MOD word12_size`;;

let list_to_word12_to_num_bound = new_axiom
  `!l. word12_to_num (list_to_word12 l) < 2 EXP (LENGTH l)`;;

let list_to_word12_to_num_bound_suc = new_axiom
  `!l. 2 * word12_to_num (list_to_word12 l) + 1 < 2 EXP (SUC (LENGTH l))`;;

let cons_to_word12_to_num_bound = new_axiom
   `!h t.
      2 * word12_to_num (list_to_word12 t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`;;

let word12_to_list_to_word12 = new_axiom
  `!w. list_to_word12 (word12_to_list w) = w`;;

let word12_to_list_inj = new_axiom
  `!w1 w2. word12_to_list w1 = word12_to_list w2 ==> w1 = w2`;;

let word12_to_list_inj_eq = new_axiom
  `!w1 w2. word12_to_list w1 = word12_to_list w2 <=> w1 = w2`;;

let list_to_word12_bit = new_axiom
   `!l n.
      word12_bit (list_to_word12 l) n =
      (n < word12_width /\ n < LENGTH l /\ EL n l)`;;

let short_list_to_word12_to_list = new_axiom
   `!l.
      LENGTH l <= word12_width ==>
      word12_to_list (list_to_word12 l) =
      APPEND l (REPLICATE (word12_width - LENGTH l) F)`;;

let long_list_to_word12_to_list = new_axiom
   `!l.
      word12_width <= LENGTH l ==>
      word12_to_list (list_to_word12 l) = take word12_width l`;;

let list_to_word12_to_list_eq = new_axiom
   `!l.
      word12_to_list (list_to_word12 l) =
      if LENGTH l <= word12_width then
        APPEND l (REPLICATE (word12_width - LENGTH l) F)
      else
        take word12_width l`;;

let list_to_word12_to_list = new_axiom
  `!l. LENGTH l = word12_width <=> word12_to_list (list_to_word12 l) = l`;;

let word12_shl_list = new_axiom
   `!l n.
      word12_shl (list_to_word12 l) n =
      list_to_word12 (APPEND (REPLICATE n F) l)`;;

let short_word12_shr_list = new_axiom
   `!l n.
      LENGTH l <= word12_width ==>
      word12_shr (list_to_word12 l) n =
      (if LENGTH l <= n then list_to_word12 []
       else list_to_word12 (drop n l))`;;

let long_word12_shr_list = new_axiom
   `!l n.
      word12_width <= LENGTH l ==>
      word12_shr (list_to_word12 l) n =
      if word12_width <= n then list_to_word12 []
      else list_to_word12 (drop n (take word12_width l))`;;

let word12_shr_list = new_axiom
   `!l n.
      word12_shr (list_to_word12 l) n =
      (if LENGTH l <= word12_width then
         if LENGTH l <= n then list_to_word12 []
         else list_to_word12 (drop n l)
       else
         if word12_width <= n then list_to_word12 []
         else list_to_word12 (drop n (take word12_width l)))`;;

let word12_eq_bits = new_axiom
  `!w1 w2. (!i. i < word12_width ==> word12_bit w1 i = word12_bit w2 i) ==> w1 = w2`;;

let num_to_word12_cons = new_axiom
  `!n.
     list_to_word12 (CONS (ODD n) (word12_to_list (num_to_word12 (n DIV 2)))) =
     num_to_word12 n`;;

let num_to_word12_list = new_axiom
  `!n.
     num_to_word12 n =
     list_to_word12
       (if n = 0 then []
        else CONS (ODD n) (word12_to_list (num_to_word12 (n DIV 2))))`;;

let word12_lte_list = new_axiom
   `!q w1 w2.
      word12_bits_lte q (word12_to_list w1) (word12_to_list w2) <=>
      (if q then word12_le w1 w2 else word12_lt w1 w2)`;;

let word12_le_list = new_axiom
   `!w1 w2.
      word12_bits_lte T (word12_to_list w1) (word12_to_list w2) <=> word12_le w1 w2`;;

let word12_lt_list = new_axiom
   `!w1 w2.
      word12_bits_lte F (word12_to_list w1) (word12_to_list w2) <=> word12_lt w1 w2`;;

let word12_le_refl = new_axiom
  `!w. word12_le w w`;;

let word12_le_trans = new_axiom
  `!w1 w2 w3. word12_le w1 w2 /\ word12_le w2 w3 ==> word12_le w1 w3`;;

let word12_lt_refl = new_axiom
  `!w. ~word12_lt w w`;;

let word12_lte_trans = new_axiom
  `!w1 w2 w3. word12_lt w1 w2 /\ word12_le w2 w3 ==> word12_lt w1 w3`;;

let word12_let_trans = new_axiom
  `!w1 w2 w3. word12_le w1 w2 /\ word12_lt w2 w3 ==> word12_lt w1 w3`;;

let word12_lt_trans = new_axiom
  `!w1 w2 w3. word12_lt w1 w2 /\ word12_lt w2 w3 ==> word12_lt w1 w3`;;

let word12_reduce_conv =
    REWRITE_CONV
      [word12_to_num_to_word12;
       word12_le_def; word12_lt_def] THENC
    REWRITE_CONV
      [num_to_word12_to_num] THENC
    REWRITE_CONV
      [word12_width_def; word12_size_def; num_to_word12_eq] THENC
    NUM_REDUCE_CONV;;

let word12_width_conv = REWR_CONV word12_width_def;;

let list_to_word12_to_list_conv =
    REWR_CONV list_to_word12_to_list_eq THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word12_width_conv THENC
       NUM_REDUCE_CONV)
      (RAND_CONV
         ((RATOR_CONV o RAND_CONV)
            (RATOR_CONV (RAND_CONV word12_width_conv) THENC
             RAND_CONV length_conv THENC
             NUM_REDUCE_CONV) THENC
          replicate_conv) THENC
       append_conv)
      (RATOR_CONV (RAND_CONV word12_width_conv) THENC
       take_conv);;

let numeral_to_word12_list_conv =
    let zero_conv = REWR_CONV (SYM (CONJUNCT1 list_to_word12_def)) in
    let numeral_conv = REWR_CONV (SYM (SPEC `NUMERAL n` num_to_word12_cons)) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (numeral_conv THENC
          RAND_CONV
            (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV) THENC
             RAND_CONV
               (RAND_CONV
                  (RAND_CONV NUM_REDUCE_CONV THENC
                   rewr_conv) THENC
                list_to_word12_to_list_conv)))) tm in
    rewr_conv;;

let word12_and_list_conv =
    let th = SPECL [`list_to_word12 l1`; `list_to_word12 l2`] word12_and_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word12_to_list_conv) THENC
       RAND_CONV list_to_word12_to_list_conv THENC
       zipwith_conv and_simp_conv);;

let word12_or_list_conv =
    let th = SPECL [`list_to_word12 l1`; `list_to_word12 l2`] word12_or_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word12_to_list_conv) THENC
       RAND_CONV list_to_word12_to_list_conv THENC
       zipwith_conv or_simp_conv);;

let word12_shr_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word12_shr_list in
    REWR_CONV th THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word12_width_conv THENC
       NUM_REDUCE_CONV)
      (cond_conv
        (RATOR_CONV (RAND_CONV length_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV drop_conv))
      (cond_conv
        (RATOR_CONV (RAND_CONV word12_width_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV
           (RAND_CONV
              (RATOR_CONV (RAND_CONV word12_width_conv) THENC
               take_conv) THENC
            drop_conv)));;

let word12_shl_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word12_shl_list in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV replicate_conv) THENC
       append_conv);;

let word12_bit_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_word12_bit in
    REWR_CONV th THENC
    andalso_conv
      (RAND_CONV word12_width_conv THENC
       NUM_REDUCE_CONV)
      (andalso_conv
        (RAND_CONV length_conv THENC
         NUM_REDUCE_CONV)
        el_conv);;

let word12_bits_lte_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 word12_bits_lte_def) in
    let cons_conv = REWR_CONV (CONJUNCT2 word12_bits_lte_def) in
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

let word12_le_list_conv =
    let th = SYM (SPECL [`list_to_word12 l1`; `list_to_word12 l2`] word12_le_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word12_to_list_conv) THENC
    RAND_CONV list_to_word12_to_list_conv THENC
    word12_bits_lte_conv;;

let word12_lt_list_conv =
    let th = SYM (SPECL [`list_to_word12 l1`; `list_to_word12 l2`] word12_lt_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word12_to_list_conv) THENC
    RAND_CONV list_to_word12_to_list_conv THENC
    word12_bits_lte_conv;;

let word12_eq_list_conv =
    let th = SYM (SPECL [`list_to_word12 l1`; `list_to_word12 l2`]
                    word12_to_list_inj_eq) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word12_to_list_conv) THENC
    RAND_CONV list_to_word12_to_list_conv THENC
    list_eq_conv iff_simp_conv;;

let word12_bit_conv =
    word12_width_conv ORELSEC
    list_to_word12_to_list_conv ORELSEC
    numeral_to_word12_list_conv ORELSEC
    word12_and_list_conv ORELSEC
    word12_or_list_conv ORELSEC
    word12_shr_list_conv ORELSEC
    word12_shl_list_conv ORELSEC
    word12_bit_list_conv ORELSEC
    word12_le_list_conv ORELSEC
    word12_lt_list_conv ORELSEC
    word12_eq_list_conv;;

let bit_blast_subterm_conv = word12_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;
let bit_blast_tac = CONV_TAC bit_blast_conv;;

let prove_word12_list_cases n =
    let interval =
        let rec intv i n = if n = 0 then [] else i :: intv (i + 1) (n - 1) in
        intv 0 in
    let lemma1 =
        let nunary = funpow n (fun t -> mk_comb (`SUC`,t)) `0` in
        let goal = mk_eq (`LENGTH (word12_to_list w)`,nunary) in
        let tac =
            REWRITE_TAC [length_word12_to_list; word12_width_def] THEN
            NUM_REDUCE_TAC in
        prove (goal,tac) in
    let witnesses =
        let addtl l = mk_comb (`TL : bool list -> bool list`, hd l) :: l in
        let tls = rev (funpow (n - 1) addtl [`l : bool list`]) in
        map (fun t -> mk_comb (`HD : bool list -> bool`, t)) tls in
    let goal =
        let is = interval n in
        let xs = map (fun i -> mk_var ("x" ^ string_of_int i, bool_ty)) is in
        let w = mk_var ("w", `:word12`) in
        let body = mk_eq (w, mk_comb (`list_to_word12`, mk_list (xs,bool_ty))) in
        mk_forall (w, list_mk_exists (xs,body)) in
    let tac =
        GEN_TAC THEN
        CONV_TAC
          (funpow n (RAND_CONV o ABS_CONV)
             (LAND_CONV (ONCE_REWRITE_CONV [GSYM word12_to_list_to_word12]))) THEN
        MP_TAC lemma1 THEN
        SPEC_TAC (`word12_to_list w`, `l : bool list`) THEN
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

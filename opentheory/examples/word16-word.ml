(* word16 *)

(* word16-def *)

new_constant ("word16_size", `:num`);;

let word16_size_def = new_axiom
  `word16_size = 2 EXP word16_width`;;

let word16_size_nonzero = new_axiom
  `~(word16_size = 0)`;;

(* word16 *)

(* word16-def *)

let mod_refl_word16_size = new_axiom
  `word16_size MOD word16_size = 0`;;

let mod_lt_word16_size = new_axiom
  `!n. n < word16_size ==> n MOD word16_size = n`;;

let zero_mod_word16_size = new_axiom
  `0 MOD word16_size = 0`;;

let lt_mod_word16_size = new_axiom
  `!n. n MOD word16_size < word16_size`;;

let mod_mod_refl_word16_size = new_axiom
  `!n. n MOD word16_size MOD word16_size = n MOD word16_size`;;

let mod_add_mod_word16_size = new_axiom
  `!m n. (m MOD word16_size + n MOD word16_size) MOD word16_size = (m + n) MOD word16_size`;;

let mod_mult_mod_word16_size = new_axiom
  `!m n. (m MOD word16_size * n MOD word16_size) MOD word16_size = (m * n) MOD word16_size`;;

let divides_mod_word16_size = new_axiom
   `!n. divides word16_size n <=> n MOD word16_size = 0`;;

new_type ("word16",0);;

new_constant ("num_to_word16", `:num -> word16`);;

new_constant ("word16_to_num", `:word16 -> num`);;

let word16_to_num_to_word16 = new_axiom
  `!x. num_to_word16 (word16_to_num x) = x`;;

let num_to_word16_inj = new_axiom
   `!x y.
      x < word16_size /\ y < word16_size /\ num_to_word16 x = num_to_word16 y ==>
      x = y`;;

let num_to_word16_to_num = new_axiom
  `!x. word16_to_num (num_to_word16 x) = x MOD word16_size`;;

new_constant ("word16_add", `:word16 -> word16 -> word16`);;

let num_to_word16_add = new_axiom
  `!x1 y1.
     num_to_word16 (x1 + y1) =
     word16_add (num_to_word16 x1) (num_to_word16 y1)`;;

new_constant ("word16_mult", `:word16 -> word16 -> word16`);;

let num_to_word16_mult = new_axiom
  `!x1 y1.
     num_to_word16 (x1 * y1) =
     word16_mult (num_to_word16 x1) (num_to_word16 y1)`;;

new_constant ("word16_neg", `:word16 -> word16`);;

let word16_neg_def = new_axiom
  `!x. word16_neg x = num_to_word16 (word16_size - word16_to_num x)`;;

new_constant ("word16_sub", `:word16 -> word16 -> word16`);;

let word16_sub_def = new_axiom
  `!x y. word16_sub x y = word16_add x (word16_neg y)`;;

new_constant ("word16_le", `:word16 -> word16 -> bool`);;

let word16_le_def = new_axiom
  `!x y. word16_le x y = word16_to_num x <= word16_to_num y`;;

new_constant ("word16_lt", `:word16 -> word16 -> bool`);;

let word16_lt_def = new_axiom
  `!x y. word16_lt x y = ~(word16_le y x)`;;

(* word16-thm *)

let word16_to_num_inj = new_axiom
  `!x y. word16_to_num x = word16_to_num y ==> x = y`;;

let num_to_word16_eq = new_axiom
   `!x y.
      num_to_word16 x = num_to_word16 y <=> x MOD word16_size = y MOD word16_size`;;

let num_to_word16_is_zero = new_axiom
   `!x. num_to_word16 x = num_to_word16 0 <=> divides word16_size x`;;

let word16_to_num_bound = new_axiom
  `!x. word16_to_num x < word16_size`;;

let word16_to_num_div_bound = new_axiom
  `!x. word16_to_num x DIV word16_size = 0`;;

let word16_to_num_mod_bound = new_axiom
  `!x. word16_to_num x MOD word16_size = word16_to_num x`;;

let word16_add_to_num = new_axiom
   `!x y.
      word16_to_num (word16_add x y) =
      (word16_to_num x + word16_to_num y) MOD word16_size`;;

let word16_mult_to_num = new_axiom
   `!x y.
      word16_to_num (word16_mult x y) =
      (word16_to_num x * word16_to_num y) MOD word16_size`;;

let word16_lt_alt = new_axiom
   `!x y. word16_lt x y = word16_to_num x < word16_to_num y`;;

let num_to_word16_word16_size = new_axiom
   `num_to_word16 word16_size = num_to_word16 0`;;

let word16_add_comm = new_axiom
   `!x y. word16_add x y = word16_add y x`;;

let word16_add_assoc = new_axiom
   `!x y z. word16_add (word16_add x y) z = word16_add x (word16_add y z)`;;

let word16_add_left_zero = new_axiom
   `!x. word16_add (num_to_word16 0) x = x`;;

let word16_add_right_zero = new_axiom
   `!x. word16_add x (num_to_word16 0) = x`;;

let word16_add_left_neg = new_axiom
   `!x. word16_add (word16_neg x) x = num_to_word16 0`;;

let word16_add_right_neg = new_axiom
   `!x. word16_add x (word16_neg x) = num_to_word16 0`;;

let word16_add_left_cancel = new_axiom
   `!x y z. word16_add x y = word16_add x z <=> y = z`;;

let word16_add_right_cancel = new_axiom
   `!x y z. word16_add y x = word16_add z x <=> y = z`;;

let word16_add_left_cancel_zero = new_axiom
   `!x y. word16_add x y = x <=> y = num_to_word16 0`;;

let word16_add_right_cancel_zero = new_axiom
   `!x y. word16_add y x = x <=> y = num_to_word16 0`;;

let word16_neg_neg = new_axiom
   `!x. word16_neg (word16_neg x) = x`;;

let word16_neg_inj = new_axiom
   `!x y. word16_neg x = word16_neg y ==> x = y`;;

let word16_neg_zero = new_axiom
   `word16_neg (num_to_word16 0) = num_to_word16 0`;;

let word16_neg_is_zero = new_axiom
   `!x. word16_neg x = num_to_word16 0 <=> x = num_to_word16 0`;;

let word16_neg_add = new_axiom
   `!x y.
      word16_add (word16_neg x) (word16_neg y) =
      word16_neg (word16_add x y)`;;

let word16_mult_comm = new_axiom
   `!x y. word16_mult x y = word16_mult y x`;;

let word16_mult_assoc = new_axiom
   `!x y z.
      word16_mult (word16_mult x y) z = word16_mult x (word16_mult y z)`;;

let word16_add_left_distrib = new_axiom
   `!x y z.
      word16_mult x (word16_add y z) =
      word16_add (word16_mult x y) (word16_mult x z)`;;

let word16_add_right_distrib = new_axiom
   `!x y z.
      word16_mult (word16_add y z) x =
      word16_add (word16_mult y x) (word16_mult z x)`;;

let word16_mult_left_zero = new_axiom
   `!x. word16_mult (num_to_word16 0) x = num_to_word16 0`;;

let word16_mult_right_zero = new_axiom
   `!x. word16_mult x (num_to_word16 0) = num_to_word16 0`;;

let word16_mult_left_one = new_axiom
   `!x. word16_mult (num_to_word16 1) x = x`;;

let word16_mult_right_one = new_axiom
   `!x. word16_mult x (num_to_word16 1) = x`;;

let word16_mult_left_neg = new_axiom
   `!x y. word16_mult (word16_neg x) y = word16_neg (word16_mult x y)`;;

let word16_mult_right_neg = new_axiom
   `!x y. word16_mult x (word16_neg y) = word16_neg (word16_mult x y)`;;

(* word16-bits-def *)

new_constant ("word16_shl", `:word16 -> num -> word16`);;

let word16_shl_def = new_axiom
  `!w n. word16_shl w n = num_to_word16 ((2 EXP n) * word16_to_num w)`;;

new_constant ("word16_shr", `:word16 -> num -> word16`);;

let word16_shr_def = new_axiom
  `!w n. word16_shr w n = num_to_word16 (word16_to_num w DIV (2 EXP n))`;;

new_constant ("word16_bit", `:word16 -> num -> bool`);;

let word16_bit_def = new_axiom
  `!w n. word16_bit w n = ODD (word16_to_num (word16_shr w n))`;;

new_constant ("word16_to_list", `:word16 -> bool list`);;

let word16_to_list_def = new_axiom
  `!w. word16_to_list w = MAP (word16_bit w) (interval 0 word16_width)`;;

new_constant ("list_to_word16", `:bool list -> word16`);;

let list_to_word16_nil = new_axiom
  `list_to_word16 [] = num_to_word16 0`
and list_to_word16_cons = new_axiom
  `!h t.
     list_to_word16 (CONS h t) =
     if h then word16_add (word16_shl (list_to_word16 t) 1) (num_to_word16 1)
     else word16_shl (list_to_word16 t) 1`;;

let list_to_word16_def = CONJ list_to_word16_nil list_to_word16_cons;;

new_constant ("is_word16_list", `:bool list -> bool`);;

let is_word16_list_def = new_axiom
  `!l. is_word16_list (l : bool list) <=> LENGTH l = word16_width`;;

new_constant ("word16_and", `:word16 -> word16 -> word16`);;

let word16_and_def = new_axiom
  `!w1 w2.
     word16_and w1 w2 =
     list_to_word16 (zipwith ( /\ ) (word16_to_list w1) (word16_to_list w2))`;;

new_constant ("word16_or", `:word16 -> word16 -> word16`);;

let word16_or_def = new_axiom
  `!w1 w2.
     word16_or w1 w2 =
     list_to_word16 (zipwith ( \/ ) (word16_to_list w1) (word16_to_list w2))`;;

new_constant ("word16_not", `:word16 -> word16`);;

let word16_not_def = new_axiom
  `!w. word16_not w = list_to_word16 (MAP (~) (word16_to_list w))`;;

new_constant ("word16_bits_lte", `:bool -> bool list -> bool list -> bool`);;

let word16_bits_lte_nil = new_axiom
   `!q. word16_bits_lte q [] [] = q`
and word16_bits_lte_cons = new_axiom
   `!q h1 h2 t1 t2.
      word16_bits_lte q (CONS h1 t1) (CONS h2 t2) =
      word16_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`;;

let word16_bits_lte_def = CONJ word16_bits_lte_nil word16_bits_lte_cons;;

(* word16-bits-thm *)

let length_word16_to_list = new_axiom
  `!w. LENGTH (word16_to_list w) = word16_width`;;

let is_word16_to_list = new_axiom
  `!w. is_word16_list (word16_to_list w)`;;

let word16_bit_div = new_axiom
  `!w n. word16_bit w n = ODD (word16_to_num w DIV (2 EXP n))`;;

let nil_to_word16_to_num = new_axiom
  `word16_to_num (list_to_word16 []) = 0`;;

let cons_to_word16_to_num = new_axiom
   `!h t.
      word16_to_num (list_to_word16 (CONS h t)) =
      (2 * word16_to_num (list_to_word16 t) + (if h then 1 else 0)) MOD word16_size`;;

let list_to_word16_to_num_bound = new_axiom
  `!l. word16_to_num (list_to_word16 l) < 2 EXP (LENGTH l)`;;

let list_to_word16_to_num_bound_suc = new_axiom
  `!l. 2 * word16_to_num (list_to_word16 l) + 1 < 2 EXP (SUC (LENGTH l))`;;

let cons_to_word16_to_num_bound = new_axiom
   `!h t.
      2 * word16_to_num (list_to_word16 t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`;;

let word16_to_list_to_word16 = new_axiom
  `!w. list_to_word16 (word16_to_list w) = w`;;

let word16_to_list_inj = new_axiom
  `!w1 w2. word16_to_list w1 = word16_to_list w2 ==> w1 = w2`;;

let word16_to_list_inj_eq = new_axiom
  `!w1 w2. word16_to_list w1 = word16_to_list w2 <=> w1 = w2`;;

let list_to_word16_bit = new_axiom
   `!l n.
      word16_bit (list_to_word16 l) n =
      (n < word16_width /\ n < LENGTH l /\ EL n l)`;;

let short_list_to_word16_to_list = new_axiom
   `!l.
      LENGTH l <= word16_width ==>
      word16_to_list (list_to_word16 l) =
      APPEND l (REPLICATE (word16_width - LENGTH l) F)`;;

let long_list_to_word16_to_list = new_axiom
   `!l.
      word16_width <= LENGTH l ==>
      word16_to_list (list_to_word16 l) = take word16_width l`;;

let list_to_word16_to_list_eq = new_axiom
   `!l.
      word16_to_list (list_to_word16 l) =
      if LENGTH l <= word16_width then
        APPEND l (REPLICATE (word16_width - LENGTH l) F)
      else
        take word16_width l`;;

let list_to_word16_to_list = new_axiom
  `!l. LENGTH l = word16_width <=> word16_to_list (list_to_word16 l) = l`;;

let word16_shl_list = new_axiom
   `!l n.
      word16_shl (list_to_word16 l) n =
      list_to_word16 (APPEND (REPLICATE n F) l)`;;

let short_word16_shr_list = new_axiom
   `!l n.
      LENGTH l <= word16_width ==>
      word16_shr (list_to_word16 l) n =
      (if LENGTH l <= n then list_to_word16 []
       else list_to_word16 (drop n l))`;;

let long_word16_shr_list = new_axiom
   `!l n.
      word16_width <= LENGTH l ==>
      word16_shr (list_to_word16 l) n =
      if word16_width <= n then list_to_word16 []
      else list_to_word16 (drop n (take word16_width l))`;;

let word16_shr_list = new_axiom
   `!l n.
      word16_shr (list_to_word16 l) n =
      (if LENGTH l <= word16_width then
         if LENGTH l <= n then list_to_word16 []
         else list_to_word16 (drop n l)
       else
         if word16_width <= n then list_to_word16 []
         else list_to_word16 (drop n (take word16_width l)))`;;

let word16_eq_bits = new_axiom
  `!w1 w2. (!i. i < word16_width ==> word16_bit w1 i = word16_bit w2 i) ==> w1 = w2`;;

let num_to_word16_cons = new_axiom
  `!n.
     list_to_word16 (CONS (ODD n) (word16_to_list (num_to_word16 (n DIV 2)))) =
     num_to_word16 n`;;

let num_to_word16_list = new_axiom
  `!n.
     num_to_word16 n =
     list_to_word16
       (if n = 0 then []
        else CONS (ODD n) (word16_to_list (num_to_word16 (n DIV 2))))`;;

let word16_lte_list = new_axiom
   `!q w1 w2.
      word16_bits_lte q (word16_to_list w1) (word16_to_list w2) <=>
      (if q then word16_le w1 w2 else word16_lt w1 w2)`;;

let word16_le_list = new_axiom
   `!w1 w2.
      word16_bits_lte T (word16_to_list w1) (word16_to_list w2) <=> word16_le w1 w2`;;

let word16_lt_list = new_axiom
   `!w1 w2.
      word16_bits_lte F (word16_to_list w1) (word16_to_list w2) <=> word16_lt w1 w2`;;

let word16_le_refl = new_axiom
  `!w. word16_le w w`;;

let word16_le_trans = new_axiom
  `!w1 w2 w3. word16_le w1 w2 /\ word16_le w2 w3 ==> word16_le w1 w3`;;

let word16_lt_refl = new_axiom
  `!w. ~word16_lt w w`;;

let word16_lte_trans = new_axiom
  `!w1 w2 w3. word16_lt w1 w2 /\ word16_le w2 w3 ==> word16_lt w1 w3`;;

let word16_let_trans = new_axiom
  `!w1 w2 w3. word16_le w1 w2 /\ word16_lt w2 w3 ==> word16_lt w1 w3`;;

let word16_lt_trans = new_axiom
  `!w1 w2 w3. word16_lt w1 w2 /\ word16_lt w2 w3 ==> word16_lt w1 w3`;;

let word16_reduce_conv =
    REWRITE_CONV
      [word16_to_num_to_word16;
       word16_le_def; word16_lt_def] THENC
    REWRITE_CONV
      [num_to_word16_to_num] THENC
    REWRITE_CONV
      [word16_width_def; word16_size_def; num_to_word16_eq] THENC
    NUM_REDUCE_CONV;;

let word16_width_conv = REWR_CONV word16_width_def;;

let list_to_word16_to_list_conv =
    REWR_CONV list_to_word16_to_list_eq THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word16_width_conv THENC
       NUM_REDUCE_CONV)
      (RAND_CONV
         ((RATOR_CONV o RAND_CONV)
            (RATOR_CONV (RAND_CONV word16_width_conv) THENC
             RAND_CONV length_conv THENC
             NUM_REDUCE_CONV) THENC
          replicate_conv) THENC
       append_conv)
      (RATOR_CONV (RAND_CONV word16_width_conv) THENC
       take_conv);;

let numeral_to_word16_list_conv =
    let zero_conv = REWR_CONV (SYM (CONJUNCT1 list_to_word16_def)) in
    let numeral_conv = REWR_CONV (SYM (SPEC `NUMERAL n` num_to_word16_cons)) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (numeral_conv THENC
          RAND_CONV
            (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV) THENC
             RAND_CONV
               (RAND_CONV
                  (RAND_CONV NUM_REDUCE_CONV THENC
                   rewr_conv) THENC
                list_to_word16_to_list_conv)))) tm in
    rewr_conv;;

let word16_and_list_conv =
    let th = SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_and_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word16_to_list_conv) THENC
       RAND_CONV list_to_word16_to_list_conv THENC
       zipwith_conv and_simp_conv);;

let word16_or_list_conv =
    let th = SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_or_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_word16_to_list_conv) THENC
       RAND_CONV list_to_word16_to_list_conv THENC
       zipwith_conv or_simp_conv);;

let word16_shr_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word16_shr_list in
    REWR_CONV th THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV word16_width_conv THENC
       NUM_REDUCE_CONV)
      (cond_conv
        (RATOR_CONV (RAND_CONV length_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV drop_conv))
      (cond_conv
        (RATOR_CONV (RAND_CONV word16_width_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV
           (RAND_CONV
              (RATOR_CONV (RAND_CONV word16_width_conv) THENC
               take_conv) THENC
            drop_conv)));;

let word16_shl_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] word16_shl_list in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV replicate_conv) THENC
       append_conv);;

let word16_bit_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_word16_bit in
    REWR_CONV th THENC
    andalso_conv
      (RAND_CONV word16_width_conv THENC
       NUM_REDUCE_CONV)
      (andalso_conv
        (RAND_CONV length_conv THENC
         NUM_REDUCE_CONV)
        el_conv);;

let word16_bits_lte_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 word16_bits_lte_def) in
    let cons_conv = REWR_CONV (CONJUNCT2 word16_bits_lte_def) in
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

let word16_le_list_conv =
    let th = SYM (SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_le_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word16_to_list_conv) THENC
    RAND_CONV list_to_word16_to_list_conv THENC
    word16_bits_lte_conv;;

let word16_lt_list_conv =
    let th = SYM (SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_lt_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word16_to_list_conv) THENC
    RAND_CONV list_to_word16_to_list_conv THENC
    word16_bits_lte_conv;;

let word16_eq_list_conv =
    let th = SYM (SPECL [`list_to_word16 l1`; `list_to_word16 l2`]
                    word16_to_list_inj_eq) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_word16_to_list_conv) THENC
    RAND_CONV list_to_word16_to_list_conv THENC
    list_eq_conv iff_simp_conv;;

let word16_bit_conv =
    word16_width_conv ORELSEC
    list_to_word16_to_list_conv ORELSEC
    numeral_to_word16_list_conv ORELSEC
    word16_and_list_conv ORELSEC
    word16_or_list_conv ORELSEC
    word16_shr_list_conv ORELSEC
    word16_shl_list_conv ORELSEC
    word16_bit_list_conv ORELSEC
    word16_le_list_conv ORELSEC
    word16_lt_list_conv ORELSEC
    word16_eq_list_conv;;

let bit_blast_subterm_conv = word16_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;
let bit_blast_tac = CONV_TAC bit_blast_conv;;

let prove_word16_list_cases n =
    let interval =
        let rec intv i n = if n = 0 then [] else i :: intv (i + 1) (n - 1) in
        intv 0 in
    let lemma1 =
        let nunary = funpow n (fun t -> mk_comb (`SUC`,t)) `0` in
        let goal = mk_eq (`LENGTH (word16_to_list w)`,nunary) in
        let tac =
            REWRITE_TAC [length_word16_to_list; word16_width_def] THEN
            NUM_REDUCE_TAC in
        prove (goal,tac) in
    let witnesses =
        let addtl l = mk_comb (`TL : bool list -> bool list`, hd l) :: l in
        let tls = rev (funpow (n - 1) addtl [`l : bool list`]) in
        map (fun t -> mk_comb (`HD : bool list -> bool`, t)) tls in
    let goal =
        let is = interval n in
        let xs = map (fun i -> mk_var ("x" ^ string_of_int i, bool_ty)) is in
        let w = mk_var ("w", `:word16`) in
        let body = mk_eq (w, mk_comb (`list_to_word16`, mk_list (xs,bool_ty))) in
        mk_forall (w, list_mk_exists (xs,body)) in
    let tac =
        GEN_TAC THEN
        CONV_TAC
          (funpow n (RAND_CONV o ABS_CONV)
             (LAND_CONV (ONCE_REWRITE_CONV [GSYM word16_to_list_to_word16]))) THEN
        MP_TAC lemma1 THEN
        SPEC_TAC (`word16_to_list w`, `l : bool list`) THEN
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

(* byte *)

(* byte-def *)

new_constant ("byte_size", `:num`);;

let byte_size_def = new_axiom
  `byte_size = 2 EXP byte_width`;;

let byte_size_nonzero = new_axiom
  `~(byte_size = 0)`;;

(* byte *)

(* byte-mod *)

let mod_lt_byte_size = new_axiom
  `!n. n < byte_size ==> n MOD byte_size = n`;;

let lt_mod_byte_size = new_axiom
  `!n. n MOD byte_size < byte_size`;;

let mod_mod_refl_byte_size = new_axiom
  `!n. n MOD byte_size MOD byte_size = n MOD byte_size`;;

let mod_add_mod_byte_size = new_axiom
  `!m n. (m MOD byte_size + n MOD byte_size) MOD byte_size = (m + n) MOD byte_size`;;

let mod_mult_mod2_byte_size = new_axiom
  `!m n. (m MOD byte_size * n MOD byte_size) MOD byte_size = (m * n) MOD byte_size`;;

(* byte-def *)

new_type ("byte",0);;

new_constant ("num_to_byte", `:num -> byte`);;

new_constant ("byte_to_num", `:byte -> num`);;

let byte_to_num_to_byte = new_axiom
  `!x. num_to_byte (byte_to_num x) = x`;;

let num_to_byte_inj = new_axiom
   `!x y.
      x < byte_size /\ y < byte_size /\ num_to_byte x = num_to_byte y ==>
      x = y`;;

let num_to_byte_to_num = new_axiom
  `!x. byte_to_num (num_to_byte x) = x MOD byte_size`;;

new_constant ("byte_add", `:byte -> byte -> byte`);;

let num_to_byte_add = new_axiom
  `!x1 y1.
     num_to_byte (x1 + y1) =
     byte_add (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_mult", `:byte -> byte -> byte`);;

let num_to_byte_mult = new_axiom
  `!x1 y1.
     num_to_byte (x1 * y1) =
     byte_mult (num_to_byte x1) (num_to_byte y1)`;;

new_constant ("byte_neg", `:byte -> byte`);;

let byte_neg_def = new_axiom
  `!x. byte_neg x = num_to_byte (byte_size - byte_to_num x)`;;

new_constant ("byte_sub", `:byte -> byte -> byte`);;

let byte_sub_def = new_axiom
  `!x y. byte_sub x y = byte_add x (byte_neg y)`;;

new_constant ("byte_le", `:byte -> byte -> bool`);;

let byte_le_def = new_axiom
  `!x y. byte_le x y = byte_to_num x <= byte_to_num y`;;

new_constant ("byte_lt", `:byte -> byte -> bool`);;

let byte_lt_def = new_axiom
  `!x y. byte_lt x y = ~(byte_le y x)`;;

(* byte-thm *)

let byte_to_num_inj = new_axiom
  `!x y. byte_to_num x = byte_to_num y ==> x = y`;;

let num_to_byte_eq = new_axiom
   `!x y.
      num_to_byte x = num_to_byte y <=> x MOD byte_size = y MOD byte_size`;;

let byte_to_num_bound = new_axiom
  `!x. byte_to_num x < byte_size`;;

let byte_to_num_div_bound = new_axiom
  `!x. byte_to_num x DIV byte_size = 0`;;

let byte_add_to_num = new_axiom
   `!x y.
      byte_to_num (byte_add x y) =
      (byte_to_num x + byte_to_num y) MOD byte_size`;;

let byte_lt_alt = new_axiom
   `!x y. byte_lt x y = byte_to_num x < byte_to_num y`;;

(* byte-bits-def *)

new_constant ("byte_shl", `:byte -> num -> byte`);;

let byte_shl_def = new_axiom
  `!w n. byte_shl w n = num_to_byte ((2 EXP n) * byte_to_num w)`;;

new_constant ("byte_shr", `:byte -> num -> byte`);;

let byte_shr_def = new_axiom
  `!w n. byte_shr w n = num_to_byte (byte_to_num w DIV (2 EXP n))`;;

new_constant ("byte_bit", `:byte -> num -> bool`);;

let byte_bit_def = new_axiom
  `!w n. byte_bit w n = ODD (byte_to_num (byte_shr w n))`;;

new_constant ("byte_to_list", `:byte -> bool list`);;

let byte_to_list_def = new_axiom
  `!w. byte_to_list w = MAP (byte_bit w) (interval 0 byte_width)`;;

new_constant ("list_to_byte", `:bool list -> byte`);;

let list_to_byte_def = new_axiom
  `(list_to_byte [] = num_to_byte 0) /\
   (!h t.
      list_to_byte (CONS h t) =
      if h then byte_add (byte_shl (list_to_byte t) 1) (num_to_byte 1)
      else byte_shl (list_to_byte t) 1)`;;

new_constant ("is_byte_list", `:bool list -> bool`);;

let is_byte_list_def = new_axiom
  `!l. is_byte_list (l : bool list) <=> LENGTH l = byte_width`;;

new_constant ("byte_and", `:byte -> byte -> byte`);;

let byte_and_def = new_axiom
  `!w1 w2.
     byte_and w1 w2 =
     list_to_byte (zipwith ( /\ ) (byte_to_list w1) (byte_to_list w2))`;;

new_constant ("byte_or", `:byte -> byte -> byte`);;

let byte_or_def = new_axiom
  `!w1 w2.
     byte_or w1 w2 =
     list_to_byte (zipwith ( \/ ) (byte_to_list w1) (byte_to_list w2))`;;

new_constant ("byte_not", `:byte -> byte`);;

let byte_not_def = new_axiom
  `!w. byte_not w = list_to_byte (MAP (~) (byte_to_list w))`;;

new_constant ("byte_bits_lte", `:bool -> bool list -> bool list -> bool`);;

let byte_bits_lte_def = new_axiom
   `(!q. byte_bits_lte q [] [] = q) /\
    (!q h1 h2 t1 t2.
       byte_bits_lte q (CONS h1 t1) (CONS h2 t2) =
       byte_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2)`;;

(* byte-bits-thm *)

let length_byte_to_list = new_axiom
  `!w. LENGTH (byte_to_list w) = byte_width`;;

let is_byte_to_list = new_axiom
  `!w. is_byte_list (byte_to_list w)`;;

let byte_bit_div = new_axiom
  `!w n. byte_bit w n = ODD (byte_to_num w DIV (2 EXP n))`;;

let nil_to_byte_to_num = new_axiom
  `byte_to_num (list_to_byte []) = 0`;;

let cons_to_byte_to_num = new_axiom
   `!h t.
      byte_to_num (list_to_byte (CONS h t)) =
      (2 * byte_to_num (list_to_byte t) + (if h then 1 else 0)) MOD byte_size`;;

let list_to_byte_to_num_bound = new_axiom
  `!l. byte_to_num (list_to_byte l) < 2 EXP (LENGTH l)`;;

let list_to_byte_to_num_bound_suc = new_axiom
  `!l. 2 * byte_to_num (list_to_byte l) + 1 < 2 EXP (SUC (LENGTH l))`;;

let cons_to_byte_to_num_bound = new_axiom
   `!h t.
      2 * byte_to_num (list_to_byte t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`;;

let byte_to_list_to_byte = new_axiom
  `!w. list_to_byte (byte_to_list w) = w`;;

let byte_to_list_inj = new_axiom
  `!w1 w2. byte_to_list w1 = byte_to_list w2 ==> w1 = w2`;;

let byte_to_list_inj_eq = new_axiom
  `!w1 w2. byte_to_list w1 = byte_to_list w2 <=> w1 = w2`;;

let list_to_byte_bit = new_axiom
   `!l n.
      byte_bit (list_to_byte l) n =
      (n < byte_width /\ n < LENGTH l /\ EL n l)`;;

let short_list_to_byte_to_list = new_axiom
   `!l.
      LENGTH l <= byte_width ==>
      byte_to_list (list_to_byte l) =
      APPEND l (REPLICATE (byte_width - LENGTH l) F)`;;

let long_list_to_byte_to_list = new_axiom
   `!l.
      byte_width <= LENGTH l ==>
      byte_to_list (list_to_byte l) = take byte_width l`;;

let list_to_byte_to_list_eq = new_axiom
   `!l.
      byte_to_list (list_to_byte l) =
      if LENGTH l <= byte_width then
        APPEND l (REPLICATE (byte_width - LENGTH l) F)
      else
        take byte_width l`;;

let list_to_byte_to_list = new_axiom
  `!l. LENGTH l = byte_width <=> byte_to_list (list_to_byte l) = l`;;

let byte_shl_list = new_axiom
   `!l n.
      byte_shl (list_to_byte l) n =
      list_to_byte (APPEND (REPLICATE n F) l)`;;

let short_byte_shr_list = new_axiom
   `!l n.
      LENGTH l <= byte_width ==>
      byte_shr (list_to_byte l) n =
      (if LENGTH l <= n then list_to_byte []
       else list_to_byte (drop n l))`;;

let long_byte_shr_list = new_axiom
   `!l n.
      byte_width <= LENGTH l ==>
      byte_shr (list_to_byte l) n =
      if byte_width <= n then list_to_byte []
      else list_to_byte (drop n (take byte_width l))`;;

let byte_shr_list = new_axiom
   `!l n.
      byte_shr (list_to_byte l) n =
      (if LENGTH l <= byte_width then
         if LENGTH l <= n then list_to_byte []
         else list_to_byte (drop n l)
       else
         if byte_width <= n then list_to_byte []
         else list_to_byte (drop n (take byte_width l)))`;;

let byte_eq_bits = new_axiom
  `!w1 w2. (!i. i < byte_width ==> byte_bit w1 i = byte_bit w2 i) ==> w1 = w2`;;

let num_to_byte_cons = new_axiom
  `!n.
     list_to_byte (CONS (ODD n) (byte_to_list (num_to_byte (n DIV 2)))) =
     num_to_byte n`;;

let num_to_byte_list = new_axiom
  `!n.
     num_to_byte n =
     list_to_byte
       (if n = 0 then []
        else CONS (ODD n) (byte_to_list (num_to_byte (n DIV 2))))`;;

let byte_lte_list = new_axiom
   `!q w1 w2.
      byte_bits_lte q (byte_to_list w1) (byte_to_list w2) <=>
      (if q then byte_le w1 w2 else byte_lt w1 w2)`;;

let byte_le_list = new_axiom
   `!w1 w2.
      byte_bits_lte T (byte_to_list w1) (byte_to_list w2) <=> byte_le w1 w2`;;

let byte_lt_list = new_axiom
   `!w1 w2.
      byte_bits_lte F (byte_to_list w1) (byte_to_list w2) <=> byte_lt w1 w2`;;

let byte_reduce_conv =
    REWRITE_CONV
      [byte_to_num_to_byte;
       byte_le_def; byte_lt_def] THENC
    REWRITE_CONV
      [num_to_byte_to_num] THENC
    REWRITE_CONV
      [byte_width_def; byte_size_def; num_to_byte_eq] THENC
    NUM_REDUCE_CONV;;

let byte_width_conv = REWR_CONV byte_width_def;;

let list_to_byte_to_list_conv =
    REWR_CONV list_to_byte_to_list_eq THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV byte_width_conv THENC
       NUM_REDUCE_CONV)
      (RAND_CONV
         ((RATOR_CONV o RAND_CONV)
            (RATOR_CONV (RAND_CONV byte_width_conv) THENC
             RAND_CONV length_conv THENC
             NUM_REDUCE_CONV) THENC
          replicate_conv) THENC
       append_conv)
      (RATOR_CONV (RAND_CONV byte_width_conv) THENC
       take_conv);;

let numeral_to_byte_list_conv =
    let zero_conv = REWR_CONV (SYM (CONJUNCT1 list_to_byte_def)) in
    let numeral_conv = REWR_CONV (SYM (SPEC `NUMERAL n` num_to_byte_cons)) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (numeral_conv THENC
          RAND_CONV
            (RATOR_CONV (RAND_CONV NUM_REDUCE_CONV) THENC
             RAND_CONV
               (RAND_CONV
                  (RAND_CONV NUM_REDUCE_CONV THENC
                   rewr_conv) THENC
                list_to_byte_to_list_conv)))) tm in
    rewr_conv;;

let byte_and_list_conv =
    let th = SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_and_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
       RAND_CONV list_to_byte_to_list_conv THENC
       zipwith_conv and_simp_conv);;

let byte_or_list_conv =
    let th = SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_or_def in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
       RAND_CONV list_to_byte_to_list_conv THENC
       zipwith_conv or_simp_conv);;

let byte_shr_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] byte_shr_list in
    REWR_CONV th THENC
    cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       RAND_CONV byte_width_conv THENC
       NUM_REDUCE_CONV)
      (cond_conv
        (RATOR_CONV (RAND_CONV length_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV drop_conv))
      (cond_conv
        (RATOR_CONV (RAND_CONV byte_width_conv) THENC
         NUM_REDUCE_CONV)
        ALL_CONV
        (RAND_CONV
           (RAND_CONV
              (RATOR_CONV (RAND_CONV byte_width_conv) THENC
               take_conv) THENC
            drop_conv)));;

let byte_shl_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] byte_shl_list in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV replicate_conv) THENC
       append_conv);;

let byte_bit_list_conv =
    let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_byte_bit in
    REWR_CONV th THENC
    andalso_conv
      (RAND_CONV byte_width_conv THENC
       NUM_REDUCE_CONV)
      (andalso_conv
        (RAND_CONV length_conv THENC
         NUM_REDUCE_CONV)
        el_conv);;

let byte_bits_lte_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 byte_bits_lte_def) in
    let cons_conv = REWR_CONV (CONJUNCT2 byte_bits_lte_def) in
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

let byte_le_list_conv =
    let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_le_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
    RAND_CONV list_to_byte_to_list_conv THENC
    byte_bits_lte_conv;;

let byte_lt_list_conv =
    let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`] byte_lt_list) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
    RAND_CONV list_to_byte_to_list_conv THENC
    byte_bits_lte_conv;;

let byte_eq_list_conv =
    let th = SYM (SPECL [`list_to_byte l1`; `list_to_byte l2`]
                    byte_to_list_inj_eq) in
    REWR_CONV th THENC
    RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
    RAND_CONV list_to_byte_to_list_conv THENC
    list_eq_conv iff_simp_conv;;

let byte_bit_conv =
    byte_width_conv ORELSEC
    list_to_byte_to_list_conv ORELSEC
    numeral_to_byte_list_conv ORELSEC
    byte_and_list_conv ORELSEC
    byte_or_list_conv ORELSEC
    byte_shr_list_conv ORELSEC
    byte_shl_list_conv ORELSEC
    byte_bit_list_conv ORELSEC
    byte_le_list_conv ORELSEC
    byte_lt_list_conv ORELSEC
    byte_eq_list_conv;;

(* ========================================================================= *)
(* PROOF TOOLS FOR NATURAL NUMBER TO BIT-LIST CONVERSIONS                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Bit-list functions operating on ML numerals.                              *)
(* ------------------------------------------------------------------------- *)

let bit_hd_num n = eq_num (mod_num n num_2) num_1;;

let bit_tl_num n = quo_num n num_2;;

let rec bit_width_num n =
    if eq_num n num_0 then num_0 else
    succ_num (bit_width_num (bit_tl_num n));;

let bit_to_num b = if b then num_1 else num_0;;

let bit_cons_num h t = bit_to_num h +/ (num_2 */ t);;

let rec bit_shl_num n k =
    if eq_num k num_0 then n else
    bit_shl_num (bit_cons_num false n) (k -/ num_1);;

let rec bit_shr_num n k =
    if eq_num k num_0 then n else
    bit_shr_num (bit_tl_num n) (k -/ num_1);;

let bit_nth_num n i = bit_hd_num (bit_shr_num n i);;

let bit_bound_num n k = n -/ bit_shl_num (bit_shr_num n k) k;;

let bit_append_num = itlist bit_cons_num;;

let bits_to_num l = bit_append_num l num_0;;

let rec num_to_bitvec n k =
    if eq_num k num_0 then [] else
    bit_hd_num n :: num_to_bitvec (bit_tl_num n) (k -/ num_1);;

let num_to_bits n = num_to_bitvec n (bit_width_num n);;

(* ------------------------------------------------------------------------- *)
(* Bit-list conversions.                                                     *)
(* ------------------------------------------------------------------------- *)

let bit_tl_conv = REWR_CONV bit_tl_def THENC NUM_REDUCE_CONV;;

let rec bit_width_conv tm =
  (REWR_CONV bit_width_src THENC
   RATOR_CONV (LAND_CONV NUM_REDUCE_CONV) THENC
   (REWR_CONV COND_TRUE ORELSEC
    (REWR_CONV COND_FALSE THENC
     LAND_CONV (RAND_CONV bit_tl_conv THENC bit_width_conv) THENC
     NUM_REDUCE_CONV))) tm;;

let numeral_to_bits_conv =
  let zero_th = prove
    (`_0 = bits_to_num []`,
     REWRITE_TAC [bits_to_num_nil; NUMERAL]) in
  let bit0_th = prove
    (`!l. BIT0 (bits_to_num l) = bits_to_num (CONS F l)`,
     REWRITE_TAC [bits_to_num_cons; bit_cons_false; MULT_2] THEN
     REWRITE_TAC [BIT0]) in
  let bit1_th = prove
    (`!l. BIT1 (bits_to_num l) = bits_to_num (CONS T l)`,
     REWRITE_TAC
       [bits_to_num_cons; bit_cons_true; MULT_2; ONE; SUC_ADD; ZERO_ADD] THEN
     REWRITE_TAC [BIT1]) in
  let numeral_conv = REWR_CONV NUMERAL
  and zero_conv = REWR_CONV zero_th
  and bit0_conv = REWR_CONV bit0_th
  and bit1_conv = REWR_CONV bit1_th in
  let rec bits_conv tm =
      (zero_conv ORELSEC
       (RAND_CONV bits_conv THENC
        (bit0_conv ORELSEC bit1_conv))) tm in
  numeral_conv THENC
  bits_conv;;

let bit_nth_numeral_conv =
  let init_th = prove
    (`!l i.
        i < LENGTH l /\ nth l i <=>
        0 <= i /\ i - 0 < LENGTH l /\ nth l (i - 0)`,
     REWRITE_TAC [LE_0; SUB_0]) in
  let nil_th = prove
    (`!i j. j <= i /\ i - j < LENGTH ([] : bool list) /\ nth [] (i - j) <=> F`,
     REWRITE_TAC [LENGTH; LT_ZERO]) in
  let cons_th = prove
    (`!h t i j.
        j <= i /\ i - j < LENGTH (CONS h t) /\ nth (CONS h t) (i - j) <=>
        (h /\ i = j) \/
        (\n. n <= i /\ i - n < LENGTH t /\ nth t (i - n)) (SUC j)`,
     REPEAT GEN_TAC THEN
     (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV) LE_LT THEN
     ASM_CASES_TAC `(i : num) = j` THENL
     [POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
      REWRITE_TAC [LT_REFL; SUB_REFL; LENGTH; LT_0; nth_zero] THEN
      REWRITE_TAC [LE_SUC_LT; LT_REFL];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [LE_SUC_LT] THEN
     REVERSE_TAC (ASM_CASES_TAC `j < (i : num)`) THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     POP_ASSUM
      (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
       REWRITE_RULE [LT_EXISTS]) THEN
     REWRITE_TAC [LT_0; ADD_SUB2; LENGTH; LT_SUC] THEN
     REWRITE_TAC [ADD_SUC; GSYM SUC_ADD; ADD_SUB2] THEN
     REVERSE_TAC (ASM_CASES_TAC `d < LENGTH (t : bool list)`) THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC nth_suc THEN
     ASM_REWRITE_TAC []) in
  let cons_false_th = prove
    (`!t i j.
        j <= i /\ i - j < LENGTH (CONS F t) /\ nth (CONS F t) (i - j) <=>
        (\n. n <= i /\ i - n < LENGTH t /\ nth t (i - n)) (SUC j)`,
     REWRITE_TAC [cons_th]) in
  let cons_true_th = prove
    (`!t i j.
        j <= i /\ i - j < LENGTH (CONS T t) /\ nth (CONS T t) (i - j) <=>
        i = j \/ (\n. n <= i /\ i - n < LENGTH t /\ nth t (i - n)) (SUC j)`,
     REWRITE_TAC [cons_th]) in
  let init_conv = REWR_CONV init_th in
  let nil_conv = REWR_CONV nil_th in
  let cons_true_conv = REWR_CONV cons_true_th in
  let cons_false_conv = REWR_CONV cons_false_th in
  let or_false_conv = REWR_CONV (TAUT `x \/ F <=> x`) in
  let rec reduce_conv tm =
      (nil_conv ORELSEC
       (cons_true_conv THENC
        RAND_CONV reduce_cons_conv THENC
        TRY_CONV or_false_conv) ORELSEC
       (cons_false_conv THENC
        reduce_cons_conv)) tm
  and reduce_cons_conv tm =
      (RAND_CONV NUM_REDUCE_CONV THENC
       BETA_CONV THENC
       reduce_conv) tm in
  LAND_CONV numeral_to_bits_conv THENC
  REWR_CONV bit_nth_bits_to_num THENC
  init_conv THENC
  reduce_conv;;

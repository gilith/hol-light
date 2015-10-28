(*BEGIN-PARAMETRIC*)
needs "opentheory/theories/tools.ml";;
needs "opentheory/theories/natural-bits/natural-bits-tools.ml";;

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
    (LAND_CONV length_conv THENC
     RAND_CONV word16_width_conv THENC
     NUM_REDUCE_CONV)
    (RAND_CONV
       (RAND_CONV
          (LAND_CONV word16_width_conv THENC
           RAND_CONV length_conv THENC
           NUM_REDUCE_CONV) THENC
        replicate_conv) THENC
     append_conv)
    (LAND_CONV word16_width_conv THENC
     take_conv);;

let numeral_to_word16_list_conv =
  let list_to_word16_conv = REWR_CONV (GSYM list_to_word16_def) in
  RAND_CONV numeral_to_bits_conv THENC
  list_to_word16_conv;;

let word16_and_list_conv =
  let th = SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_and_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_word16_to_list_conv THENC
     RAND_CONV list_to_word16_to_list_conv THENC
     zipwith_conv and_simp_conv);;

let word16_or_list_conv =
  let th = SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_or_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_word16_to_list_conv THENC
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
    (LAND_CONV replicate_conv THENC
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
      nth_conv);;

let word16_bits_lte_conv =
  let nil_conv = REWR_CONV word16_bits_lte_nil in
  let cons_conv = REWR_CONV word16_bits_lte_cons in
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
  LAND_CONV list_to_word16_to_list_conv THENC
  RAND_CONV list_to_word16_to_list_conv THENC
  word16_bits_lte_conv;;

let word16_lt_list_conv =
  let th = SYM (SPECL [`list_to_word16 l1`; `list_to_word16 l2`] word16_lt_list) in
  REWR_CONV th THENC
  LAND_CONV list_to_word16_to_list_conv THENC
  RAND_CONV list_to_word16_to_list_conv THENC
  word16_bits_lte_conv;;

let word16_eq_list_conv =
  let th = SYM (SPECL [`list_to_word16 l1`; `list_to_word16 l2`]
                  word16_to_list_inj_eq) in
  REWR_CONV th THENC
  LAND_CONV list_to_word16_to_list_conv THENC
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
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* word16 *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* word16 *)

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
        (MP_TAC (ISPEC `l : bool list` list_cases) THEN
         STRIP_TAC THENL
         [ASM_REWRITE_TAC [LENGTH; NOT_SUC];
          ALL_TAC] THEN
         POP_ASSUM SUBST_VAR_TAC THEN
         REWRITE_TAC [LENGTH; SUC_INJ; HD; TL; CONS_11] THEN
         SPEC_TAC (`t : bool list`, `l : bool list`) THEN
         GEN_TAC) THEN
      REWRITE_TAC [LENGTH_EQ_NIL] in
  prove (goal,tac);;

(*END-PARAMETRIC*)

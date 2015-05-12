(* ========================================================================= *)
(* NATURAL NUMBER TO BIT-LIST CONVERSIONS                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for natural number to bit-list conversions.               *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/natural-bits/natural-bits.int";;

(* ------------------------------------------------------------------------- *)
(* Helper theorems (not exported).                                           *)
(* ------------------------------------------------------------------------- *)

let two_nonzero = prove
 (`~(2 = 0)`,
  REWRITE_TAC [TWO; NOT_SUC]);;

let exp_two_nz = prove
 (`!n. ~(2 EXP n = 0)`,
  REWRITE_TAC [EXP_EQ_0] THEN
  NUM_REDUCE_TAC);;

let le_exp_two = prove
 (`!m n. 2 EXP m <= 2 EXP n <=> m <= n`,
  REWRITE_TAC [LE_EXP] THEN
  NUM_REDUCE_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definition of natural number to bit-list conversions.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-def";;

let bit_width_def = new_definition
  `!n. bit_width n = if n = 0 then 0 else log 2 n + 1`;;

export_thm bit_width_def;;

let bit_to_num_def = new_definition
  `!b. bit_to_num b = if b then 1 else 0`;;

export_thm bit_to_num_def;;

let bit_cons_def = new_definition
  `!h t. bit_cons h t = bit_to_num h + 2 * t`;;

export_thm bit_cons_def;;

let bit_hd_def = new_definition
  `!n. bit_hd n = ODD n`;;

export_thm bit_hd_def;;

let bit_tl_def = new_definition
  `!n. bit_tl n = n DIV 2`;;

export_thm bit_tl_def;;

let bit_shl_def = new_definition
  `!n k. bit_shl n k = (2 EXP k) * n`;;

export_thm bit_shl_def;;

let bit_shr_def = new_definition
  `!n k. bit_shr n k = n DIV (2 EXP k)`;;

export_thm bit_shr_def;;

let bit_nth_def = new_definition
  `!n i. bit_nth n i = bit_hd (bit_shr n i)`;;

export_thm bit_nth_def;;

let bit_bound_def = new_definition
  `!n k. bit_bound n k = n MOD (2 EXP k)`;;

export_thm bit_bound_def;;

let bit_cmp_def = new_definition
  `!q (m : num) n. bit_cmp q m n = if q then m <= n else m < n`;;

export_thm bit_cmp_def;;

let bit_append_def = new_definition
  `!l n. bit_append l n = foldr bit_cons n l`;;

export_thm bit_append_def;;

let bits_to_num_def = new_definition
  `!l. bits_to_num l = bit_append l 0`;;

export_thm bits_to_num_def;;

let (num_to_bitvec_zero,num_to_bitvec_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!n. num_to_bitvec n 0 = []) /\
     (!n k.
        num_to_bitvec n (SUC k) =
        CONS (bit_hd n) (num_to_bitvec (bit_tl n) k))` in
  CONJ_PAIR def;;

export_thm num_to_bitvec_zero;;
export_thm num_to_bitvec_suc;;

let num_to_bitvec_def = CONJ num_to_bitvec_zero num_to_bitvec_suc;;

let num_to_bits_def = new_definition
  `!n. num_to_bits n = num_to_bitvec n (bit_width n)`;;

export_thm num_to_bits_def;;

let is_bits_def = new_definition
  `!l. is_bits l <=> NULL l \/ LAST l`;;

export_thm is_bits_def;;

let bit_and_def = new_definition
  `!m n.
     bit_and m n =
     bits_to_num
       (MAP (\i. bit_nth m i /\ bit_nth n i)
          (interval 0 (MIN (bit_width m) (bit_width n))))`;;

export_thm bit_and_def;;

let bit_or_def = new_definition
  `!m n.
     bit_or m n =
     bits_to_num
       (MAP (\i. bit_nth m i \/ bit_nth n i)
          (interval 0 (MAX (bit_width m) (bit_width n))))`;;

export_thm bit_or_def;;

let random_uniform_loop_exists = prove
 (`!n w. ?loop. !r.
     loop r =
     let (r1,r2) = split_random r in
     let l = random_bits w r1 in
     let m = bits_to_num l in
     if m < n then m else
     loop r2`,
  REPEAT GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ (r : random).
          let (r1,r2) = split_random r in
          let l = random_bits w r1 in
          let m = bits_to_num l in
          ~(m < n)`;
       `\ (r : random).
          let (r1,r2) = split_random r in
          let l = random_bits w r1 in
          let m = bits_to_num l in
          r2`;
       `\ (r : random).
          let (r1,r2) = split_random r in
          let l = random_bits w r1 in
          let m = bits_to_num l in
          m`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `loop : random -> num`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `loop : random -> num` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `split_random r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `r1 : random`
       (X_CHOOSE_THEN `r2 : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `bits_to_num (random_bits w r1) < n` THEN
  REWRITE_TAC []);;

let random_uniform_loop_def =
  new_specification ["random_uniform_loop"]
    (ONCE_REWRITE_RULE [SKOLEM_THM]
      (ONCE_REWRITE_RULE [SKOLEM_THM]
        random_uniform_loop_exists));;

export_thm random_uniform_loop_def;;

let random_uniform_def = new_definition
  `!n r.
     random_uniform n r =
     let w = bit_width (n - 1) in
     random_uniform_loop n w r`;;

export_thm random_uniform_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of natural number to bit-list conversions.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-thm";;

let bit_width_zero = prove
 (`bit_width 0 = 0`,
  REWRITE_TAC [bit_width_def]);;

export_thm bit_width_zero;;

let bit_width_eq_zero = prove
 (`!n. bit_width n = 0 <=> n = 0`,
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_width_zero];
   REWRITE_TAC [bit_width_def; NOT_SUC; GSYM ADD1]]);;

export_thm bit_width_eq_zero;;

let bit_width_one = prove
 (`bit_width 1 = 1`,
  REWRITE_TAC [bit_width_def] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [EQ_ADD_RCANCEL_0] THEN
   MATCH_MP_TAC log_one THEN
   REWRITE_TAC [TWO; SUC_LT]]);;

export_thm bit_width_one;;

let bit_width_src = prove
 (`!n. bit_width n = if n = 0 then 0 else bit_width (bit_tl n) + 1`,
  GEN_TAC THEN
  REWRITE_TAC [bit_width_def; bit_tl_def] THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   MP_TAC (SPECL [`2`; `n : num`] log_recursion) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [TWO; SUC_LT];
    DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC DIV_EQ_0 THEN
    REWRITE_TAC [TWO; NOT_SUC]]]);;

export_thm bit_width_src;;

let bit_width_mono = prove
 (`!n1 n2. n1 <= n2 ==> bit_width n1 <= bit_width n2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n1 = 0` THENL
  [ASM_REWRITE_TAC [bit_width_zero; LE_0];
   ASM_CASES_TAC `n2 = 0` THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [GSYM LE_ZERO];
    ASM_REWRITE_TAC [bit_width_def; LE_ADD_RCANCEL] THEN
    MATCH_MP_TAC log_mono THEN
    ASM_REWRITE_TAC [TWO; SUC_LT]]]);;

export_thm bit_width_mono;;

let lt_exp_bit_width = prove
 (`!n. n < 2 EXP (bit_width n)`,
  GEN_TAC THEN
  REWRITE_TAC [bit_width_def] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [EXP; ONE; SUC_LT];
   MATCH_MP_TAC lt_exp_log THEN
   ASM_REWRITE_TAC [TWO; SUC_LT]]);;

export_thm lt_exp_bit_width;;

let bit_to_num_true = prove
 (`bit_to_num T = 1`,
  REWRITE_TAC [bit_to_num_def]);;

export_thm bit_to_num_true;;

let bit_to_num_false = prove
 (`bit_to_num F = 0`,
  REWRITE_TAC [bit_to_num_def]);;

export_thm bit_to_num_false;;

let bit_to_num_one = prove
 (`!b. bit_to_num b = 1 <=> b`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC [bit_to_num_def; ONE; NOT_SUC]);;

export_thm bit_to_num_one;;

let bit_to_num_zero = prove
 (`!b. bit_to_num b = 0 <=> ~b`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC [bit_to_num_def; ONE; NOT_SUC]);;

export_thm bit_to_num_zero;;

let bit_to_num_bound = prove
 (`!b. bit_to_num b < 2`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC
    [bit_to_num_true; bit_to_num_false;
     TWO; ONE; LT_SUC_LE; LE_REFL; SUC_LE]);;

export_thm bit_to_num_bound;;

let bit_width_bit_to_num = prove
 (`!b. bit_width (bit_to_num b) = (bit_to_num b)`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THENL
  [REWRITE_TAC [bit_to_num_true; bit_width_one];
   REWRITE_TAC [bit_to_num_false; bit_width_zero]]);;

export_thm bit_width_bit_to_num;;

let bit_hd_zero = prove
 (`~bit_hd 0`,
  REWRITE_TAC [bit_hd_def; ODD_ZERO]);;

export_thm bit_hd_zero;;

let bit_hd_suc = prove
 (`!n. bit_hd (SUC n) = ~bit_hd n`,
  REWRITE_TAC [bit_hd_def; ODD_SUC]);;

export_thm bit_hd_suc;;

let bit_hd_one = prove
 (`bit_hd 1`,
  REWRITE_TAC [ONE; bit_hd_suc; bit_hd_zero]);;

export_thm bit_hd_one;;

let bit_hd_two = prove
 (`~bit_hd 2`,
  REWRITE_TAC [TWO; bit_hd_suc; bit_hd_one]);;

export_thm bit_hd_two;;

let bit_to_num_hd = prove
 (`!b. bit_hd (bit_to_num b) = b`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC [bit_to_num_def; bit_hd_zero; bit_hd_one]);;

export_thm bit_to_num_hd;;

let bit_hd_to_num = prove
 (`!n. bit_to_num (bit_hd n) = n MOD 2`,
  GEN_TAC THEN
  REWRITE_TAC [bit_to_num_def; bit_hd_def] THEN
  MATCH_MP_TAC EQ_SYM THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [GSYM EVEN_MOD; GSYM ODD_MOD] THEN
  ASM_REWRITE_TAC [GSYM NOT_ODD]);;

export_thm bit_hd_to_num;;

let bit_to_num_mod_two = prove
 (`!b. bit_to_num b MOD 2 = bit_to_num b`,
  REWRITE_TAC [GSYM bit_hd_to_num; bit_to_num_hd]);;

export_thm bit_to_num_mod_two;;

let bit_tl_zero = prove
 (`bit_tl 0 = 0`,
  REWRITE_TAC [bit_tl_def] THEN
  MATCH_MP_TAC DIV_LT THEN
  REWRITE_TAC [LT_NZ; two_nonzero]);;

export_thm bit_tl_zero;;

let bit_tl_one = prove
 (`bit_tl 1 = 0`,
  REWRITE_TAC [bit_tl_def] THEN
  MATCH_MP_TAC DIV_LT THEN
  REWRITE_TAC [TWO; SUC_LT]);;

export_thm bit_tl_one;;

let bit_to_num_tl = prove
 (`!b. bit_tl (bit_to_num b) = 0`,
  GEN_TAC THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC [bit_to_num_def; bit_tl_zero; bit_tl_one]);;

export_thm bit_to_num_tl;;

let bit_hd_add = prove
 (`!n1 n2. bit_hd (n1 + n2) = ~(bit_hd n1 <=> bit_hd n2)`,
  REWRITE_TAC [bit_hd_def; ODD_ADD]);;

export_thm bit_hd_add;;

let bit_hd_mult = prove
 (`!n1 n2. bit_hd (n1 * n2) = (bit_hd n1 /\ bit_hd n2)`,
  REWRITE_TAC [bit_hd_def; ODD_MULT]);;

export_thm bit_hd_mult;;

let bit_hd_double = prove
 (`!n. ~bit_hd (2 * n)`,
  REWRITE_TAC [bit_hd_mult; bit_hd_two]);;

export_thm bit_hd_double;;

let bit_hd_cons = prove
 (`!h t. bit_hd (bit_cons h t) = h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_cons_def; bit_hd_add; bit_hd_double; bit_to_num_hd]);;

export_thm bit_hd_cons;;

let bit_tl_induction = prove
 (`!p. p 0 /\ (!n. ~(n = 0) /\ p (bit_tl n) ==> p n) ==> !n. p n`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MATCH_MP_TAC div_induction THEN
  EXISTS_TAC `2` THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC [TWO; SUC_LT];
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [bit_tl_def]]);;

export_thm bit_tl_induction;;

let bit_cons_false = prove
 (`!n. bit_cons F n = 2 * n`,
  REWRITE_TAC [bit_cons_def; bit_to_num_false; ZERO_ADD]);;

export_thm bit_cons_false;;

let bit_cons_true = prove
 (`!n. bit_cons T n = 1 + 2 * n`,
  REWRITE_TAC [bit_cons_def; bit_to_num_true]);;

export_thm bit_cons_true;;

let bit_cons_zero = prove
 (`!b. bit_cons b 0 = bit_to_num b`,
  REWRITE_TAC [bit_cons_def; ADD_0; MULT_0]);;

export_thm bit_cons_zero;;

let suc_bit_cons_false = prove
 (`!n. SUC (bit_cons F n) = bit_cons T n`,
  REWRITE_TAC [bit_cons_def; bit_to_num_def; ONE; SUC_ADD]);;

export_thm suc_bit_cons_false;;

let suc_bit_cons_true = prove
 (`!n. SUC (bit_cons T n) = bit_cons F (SUC n)`,
  REWRITE_TAC
    [bit_cons_def; bit_to_num_def; MULT_SUC; TWO; ONE; ONE; ADD]);;

export_thm suc_bit_cons_true;;

let bit_tl_cons = prove
 (`!h t. bit_tl (bit_cons h t) = t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_tl_def; bit_cons_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `bit_to_num h DIV 2 + (2 * t) DIV 2` THEN
  CONJ_TAC THENL
  [MP_TAC (SPECL [`bit_to_num h`; `2 * t`; `2`] DIV_ADD_MOD) THEN
   REWRITE_TAC [two_nonzero] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`2`; `t : num`] MOD_MULT) THEN
   MP_TAC (SPECL [`bit_to_num h`; `2 * t`; `2`] MOD_ADD_MOD) THEN
   REWRITE_TAC [two_nonzero] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_0] THEN
   MATCH_MP_TAC MOD_MOD_REFL THEN
   ACCEPT_TAC two_nonzero;
   MP_TAC (SPECL [`2`; `t : num`] DIV_MULT) THEN
   REWRITE_TAC [two_nonzero] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [EQ_ADD_RCANCEL_0; GSYM bit_tl_def; bit_to_num_tl]]);;

export_thm bit_tl_cons;;

let bit_cons_inj = prove
 (`!h1 h2 t1 t2. bit_cons h1 t1 = bit_cons h2 t2 <=> h1 = h2 /\ t1 = t2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `bit_hd (bit_cons h1 t1) = bit_hd (bit_cons h2 t2)`
      (ACCEPT_TAC o REWRITE_RULE [bit_hd_cons]) THEN
    ASM_REWRITE_TAC [];
    SUBGOAL_THEN `bit_tl (bit_cons h1 t1) = bit_tl (bit_cons h2 t2)`
      (ACCEPT_TAC o REWRITE_RULE [bit_tl_cons]) THEN
    ASM_REWRITE_TAC []];
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bit_cons_inj;;

let bit_cons_eq_zero = prove
 (`!h t. bit_cons h t = 0 <=> ~h /\ t = 0`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `bit_cons h t = bit_cons F 0` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_cons_zero; bit_to_num_false];
   REWRITE_TAC [bit_cons_inj]]);;

export_thm bit_cons_eq_zero;;

let bit_cons_eq_one = prove
 (`!h t. bit_cons h t = 1 <=> h /\ t = 0`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `bit_cons h t = bit_cons T 0` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_cons_zero; bit_to_num_true];
   REWRITE_TAC [bit_cons_inj]]);;

export_thm bit_cons_eq_one;;

let bit_cons_hd_tl = prove
 (`!n. bit_cons (bit_hd n) (bit_tl n) = n`,
  GEN_TAC THEN
  REWRITE_TAC [bit_cons_def; bit_hd_to_num; bit_tl_def] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  MATCH_MP_TAC DIVISION_DEF_DIV THEN
  ACCEPT_TAC two_nonzero);;

export_thm bit_cons_hd_tl;;

let bit_cons_cases = prove
 (`!n. ?h t. n = bit_cons h t`,
  GEN_TAC THEN
  EXISTS_TAC `bit_hd n` THEN
  EXISTS_TAC `bit_tl n` THEN
  REWRITE_TAC [bit_cons_hd_tl]);;

export_thm bit_cons_cases;;

let bit_cons_induction = prove
 (`!p. p 0 /\ (!h t. p t ==> p (bit_cons h t)) ==> !n. p n`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bit_tl_induction THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC [];
   GEN_TAC THEN
   MP_TAC (SPEC `n : num` bit_cons_cases) THEN
   DISCH_THEN (CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
   REWRITE_TAC [bit_tl_cons] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm bit_cons_induction;;

let bit_tl_add = prove
 (`!n1 n2. bit_tl (n1 + bit_cons F n2) = bit_tl n1 + n2`,
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [ZERO_ADD; bit_tl_cons; bit_tl_zero] THEN
  REWRITE_TAC [bit_cons_false] THEN
  REWRITE_TAC [bit_cons_def; GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC [GSYM bit_cons_def; bit_tl_cons]);;

export_thm bit_tl_add;;

let bit_shl_zero = prove
 (`!n. bit_shl n 0 = n`,
  REWRITE_TAC [bit_shl_def; EXP_0; ONE_MULT]);;

export_thm bit_shl_zero;;

let bit_shl_one = prove
 (`!n. bit_shl n 1 = 2 * n`,
  REWRITE_TAC [bit_shl_def; EXP_1]);;

export_thm bit_shl_one;;

let bit_shl_suc = prove
 (`!n k. bit_shl n (SUC k) = bit_cons F (bit_shl n k)`,
  REWRITE_TAC
    [bit_shl_def; EXP_SUC; bit_cons_def; bit_to_num_false; ZERO_ADD;
     MULT_ASSOC]);;

export_thm bit_shl_suc;;

let bit_shl_funpow = prove
 (`!n k. bit_shl n k = funpow (bit_cons F) k n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_shl_zero; funpow_zero; I_THM];
   ASM_REWRITE_TAC [bit_shl_suc; funpow_suc; o_THM]]);;

export_thm bit_shl_funpow;;

let bit_shl_suc' = prove
 (`!n k. bit_shl n (SUC k) = bit_shl (bit_cons F n) k`,
  REWRITE_TAC [bit_shl_funpow; funpow_suc'; o_THM]);;

export_thm bit_shl_suc';;

let bit_shl_add = prove
 (`!n k1 k2. bit_shl n (k1 + k2) = bit_shl (bit_shl n k1) k2`,
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [bit_shl_funpow; funpow_add; o_THM]);;

export_thm bit_shl_add;;

let zero_bit_shl = prove
 (`!k. bit_shl 0 k = 0`,
  REWRITE_TAC [bit_shl_def; MULT_0]);;

export_thm zero_bit_shl;;

let one_bit_shl = prove
 (`!k. bit_shl 1 k = 2 EXP k`,
  REWRITE_TAC [bit_shl_def; MULT_1]);;

export_thm one_bit_shl;;

let add_bit_shl = prove
 (`!k n1 n2. bit_shl (n1 + n2) k = bit_shl n1 k + bit_shl n2 k`,
  REWRITE_TAC [bit_shl_def; LEFT_ADD_DISTRIB]);;

export_thm add_bit_shl;;

let mult_bit_shl = prove
 (`!k n1 n2. bit_shl (n1 * n2) k = n1 * bit_shl n2 k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_shl_def; MULT_ASSOC] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

export_thm mult_bit_shl;;

let bit_shl_eq_zero = prove
 (`!k n. bit_shl n k = 0 <=> n = 0`,
  REWRITE_TAC [bit_shl_def; MULT_EQ_0; exp_two_nz]);;

export_thm bit_shl_eq_zero;;

let bit_shl_mono_le = prove
 (`!k n1 n2. bit_shl n1 k <= bit_shl n2 k <=> n1 <= n2`,
  REWRITE_TAC [bit_shl_def; LE_MULT_LCANCEL; exp_two_nz]);;

export_thm bit_shl_mono_le;;

let bit_shl_inj = prove
 (`!k n1 n2. bit_shl n1 k = bit_shl n2 k <=> n1 = n2`,
  REWRITE_TAC [GSYM LE_ANTISYM; bit_shl_mono_le]);;

export_thm bit_shl_inj;;

let bit_shr_zero = prove
 (`!n. bit_shr n 0 = n`,
  REWRITE_TAC [bit_shr_def; EXP_0; DIV_1]);;

export_thm bit_shr_zero;;

let bit_shr_one = prove
 (`!n. bit_shr n 1 = bit_tl n`,
  REWRITE_TAC [bit_shr_def; bit_tl_def; EXP_1]);;

export_thm bit_shr_one;;

let bit_shr_suc = prove
 (`!n k. bit_shr n (SUC k) = bit_tl (bit_shr n k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_shr_def; EXP_SUC; bit_tl_def] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC (ONCE_REWRITE_RULE [MULT_SYM] DIV_DIV) THEN
  REWRITE_TAC [MULT_EQ_0; DE_MORGAN_THM; two_nonzero; EXP_EQ_0]);;

export_thm bit_shr_suc;;

let bit_shr_funpow = prove
 (`!n k. bit_shr n k = funpow bit_tl k n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_shr_zero; funpow_zero; I_THM];
   ASM_REWRITE_TAC [bit_shr_suc; funpow_suc; o_THM]]);;

export_thm bit_shr_funpow;;

let bit_shr_suc' = prove
 (`!n k. bit_shr n (SUC k) = bit_shr (bit_tl n) k`,
  REWRITE_TAC [bit_shr_funpow; funpow_suc'; o_THM]);;

export_thm bit_shr_suc';;

let bit_shr_add = prove
 (`!n k1 k2. bit_shr n (k1 + k2) = bit_shr (bit_shr n k1) k2`,
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [bit_shr_funpow; funpow_add; o_THM]);;

export_thm bit_shr_add;;

let zero_bit_shr = prove
 (`!k. bit_shr 0 k = 0`,
  GEN_TAC THEN
  REWRITE_TAC [bit_shr_def] THEN
  MATCH_MP_TAC DIV_0 THEN
  REWRITE_TAC [EXP_EQ_0; two_nonzero]);;

export_thm zero_bit_shr;;

let add_bit_shr = prove
 (`!n1 n2 k. bit_shr (n1 + bit_shl n2 k) k = bit_shr n1 k + n2`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`n2 : num`, `n2 : num`) THEN
  SPEC_TAC (`n1 : num`, `n1 : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_shr_zero; bit_shl_zero];
   ASM_REWRITE_TAC [bit_shr_suc'; bit_shl_suc; bit_tl_add]]);;

export_thm add_bit_shr;;

let bit_nth_zero = prove
 (`!n. bit_nth n 0 = bit_hd n`,
  REWRITE_TAC [bit_nth_def; bit_shr_zero]);;

export_thm bit_nth_zero;;

let bit_nth_suc = prove
 (`!n i. bit_nth n (SUC i) = bit_nth (bit_tl n) i`,
  REWRITE_TAC [bit_nth_def; bit_shr_suc']);;

export_thm bit_nth_suc;;

let bit_tl_nth = prove
 (`!n. bit_nth (bit_tl n) = bit_nth n o SUC`,
  REWRITE_TAC [FUN_EQ_THM; bit_nth_suc; o_THM]);;

export_thm bit_tl_nth;;

let bit_nth_add = prove
 (`!n k i. bit_nth n (k + i) = bit_nth (bit_shr n k) i`,
  REWRITE_TAC [bit_nth_def; GSYM bit_shr_add]);;

export_thm bit_nth_add;;

let zero_bit_nth = prove
 (`!i. ~bit_nth 0 i`,
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_nth_zero; bit_hd_zero];
   ASM_REWRITE_TAC [bit_nth_suc; bit_tl_zero]]);;

export_thm zero_bit_nth;;

let bit_bound = prove
 (`!n k. bit_bound n k + bit_shl (bit_shr n k) k = n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [bit_shl_def; bit_shr_def; bit_bound_def] THEN
  MATCH_MP_TAC (ONCE_REWRITE_RULE [MULT_SYM] DIVISION_DEF_DIV) THEN
  REWRITE_TAC [EXP_EQ_0; two_nonzero]);;

export_thm bit_bound;;

let bit_bound_zero = prove
 (`!n. bit_bound n 0 = 0`,
  GEN_TAC THEN
  MP_TAC (SPECL [`n : num`; `0`] bit_bound) THEN
  REWRITE_TAC [bit_shr_zero; bit_shl_zero; EQ_ADD_RCANCEL_0]);;

export_thm bit_bound_zero;;

let bit_bound_suc = prove
 (`!n k. bit_bound n (SUC k) = bit_cons (bit_hd n) (bit_bound (bit_tl n) k)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC
    [GSYM (SPEC `bit_shl (bit_shr n (SUC k)) (SUC k)` EQ_ADD_RCANCEL)] THEN
  REWRITE_TAC [bit_bound] THEN
  REWRITE_TAC [bit_shr_suc'; bit_shl_suc] THEN
  REWRITE_TAC
    [bit_cons_def; bit_to_num_false; ZERO_ADD; GSYM ADD_ASSOC;
     GSYM LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC [GSYM bit_cons_def] THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM bit_cons_hd_tl))) THEN
  REWRITE_TAC [bit_cons_inj] THEN
  REWRITE_TAC [bit_bound]);;

export_thm bit_bound_suc;;

let bit_bound_suc' = prove
 (`!n k.
     bit_bound n (SUC k) =
     bit_bound n k + bit_shl (bit_to_num (bit_nth n k)) k`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC
    [GSYM (SPEC `bit_shl (bit_shr n (SUC k)) (SUC k)` EQ_ADD_RCANCEL)] THEN
  REWRITE_TAC [bit_bound] THEN
  REWRITE_TAC [bit_shl_suc'; GSYM ADD_ASSOC; GSYM add_bit_shl] THEN
  REWRITE_TAC [bit_cons_false; GSYM bit_cons_def] THEN
  REWRITE_TAC [bit_shr_suc; bit_nth_def; bit_cons_hd_tl; bit_bound]);;

export_thm bit_bound_suc';;

let bit_bound_one = prove
 (`!n. bit_bound n 1 = bit_to_num (bit_hd n)`,
  REWRITE_TAC [ONE; bit_bound_suc; bit_bound_zero; bit_cons_zero]);;

export_thm bit_bound_one;;

let bit_bound_width = prove
 (`!n. bit_bound n (bit_width n) = n`,
  MATCH_MP_TAC bit_tl_induction THEN
  REWRITE_TAC [bit_width_zero; bit_bound_zero] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [bit_width_src] THEN
  ASM_REWRITE_TAC [GSYM ADD1; bit_bound_suc; bit_cons_hd_tl]);;

export_thm bit_bound_width;;

let bit_append_nil = prove
 (`!n. bit_append [] n = n`,
  REWRITE_TAC [bit_append_def; foldr_nil]);;

export_thm bit_append_nil;;

let bit_append_cons = prove
 (`!h t n. bit_append (CONS h t) n = bit_cons h (bit_append t n)`,
  REWRITE_TAC [bit_append_def; foldr_cons]);;

export_thm bit_append_cons;;

let bits_to_num_nil = prove
 (`bits_to_num [] = 0`,
  REWRITE_TAC [bits_to_num_def; bit_append_nil]);;

export_thm bits_to_num_nil;;

let bits_to_num_cons = prove
 (`!h t. bits_to_num (CONS h t) = bit_cons h (bits_to_num t)`,
  REWRITE_TAC [bits_to_num_def; bit_append_cons]);;

export_thm bits_to_num_cons;;

let bits_to_num_cons_eq_zero = prove
 (`!h t. bits_to_num (CONS h t) = 0 <=> ~h /\ bits_to_num t = 0`,
  REWRITE_TAC [bits_to_num_cons; bit_cons_eq_zero]);;

export_thm bits_to_num_cons_eq_zero;;

let bits_to_num_sing = prove
 (`!b. bits_to_num [b] = bit_to_num b`,
  REWRITE_TAC [bits_to_num_cons; bits_to_num_nil; bit_cons_zero]);;

export_thm bits_to_num_sing;;

let bits_to_num_append = prove
 (`!l1 l2.
     bits_to_num (APPEND l1 l2) =
     bits_to_num l1 + bit_shl (bits_to_num l2) (LENGTH l1)`,
  GEN_TAC THEN
  X_GEN_TAC `l : bool list` THEN
  SPEC_TAC (`l1 : bool list`, `l1 : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NIL_APPEND; bits_to_num_nil; LENGTH; ZERO_ADD; bit_shl_zero];
   ASM_REWRITE_TAC [CONS_APPEND; bits_to_num_cons; LENGTH; bit_shl_suc] THEN
   REWRITE_TAC [bit_cons_def; bit_to_num_false; ZERO_ADD] THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB; ADD_ASSOC]]);;

export_thm bits_to_num_append;;

let num_to_bitvec = prove
 (`!n k. num_to_bitvec n k = MAP (bit_nth n) (interval 0 k)`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [interval_zero; MAP; num_to_bitvec_zero];
   ASM_REWRITE_TAC [interval_suc; MAP; num_to_bitvec_suc] THEN
   REWRITE_TAC
     [GSYM map_suc_interval; GSYM MAP_o; bit_nth_zero; bit_tl_nth]]);;

export_thm num_to_bitvec;;

let length_num_to_bitvec = prove
 (`!n k. LENGTH (num_to_bitvec n k) = k`,
  REWRITE_TAC [num_to_bitvec; LENGTH_MAP; length_interval]);;

export_thm length_num_to_bitvec;;

let length_num_to_bits = prove
 (`!n. LENGTH (num_to_bits n) = bit_width n`,
  REWRITE_TAC [num_to_bits_def; length_num_to_bitvec]);;

export_thm length_num_to_bits;;

let num_to_bitvec_src = prove
 (`!n k.
     num_to_bitvec n k =
     if k = 0 then [] else
     CONS (bit_hd n) (num_to_bitvec (bit_tl n) (k - 1))`,
  GEN_TAC THEN
  INDUCT_TAC THEN
  REWRITE_TAC [num_to_bitvec_def; NOT_SUC; SUC_SUB1]);;

export_thm num_to_bitvec_src;;

let num_to_bits_src = prove
 (`!n.
     num_to_bits n =
     if n = 0 then [] else CONS (bit_hd n) (num_to_bits (bit_tl n))`,
  GEN_TAC THEN
  REWRITE_TAC [num_to_bits_def] THEN
  CONV_TAC (LAND_CONV (REWR_CONV num_to_bitvec_src)) THEN
  REWRITE_TAC [bit_width_eq_zero] THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV bit_width_src))) THEN
   ASM_REWRITE_TAC [GSYM ADD1; SUC_SUB1]]);;

export_thm num_to_bits_src;;

let num_to_bits_eq_nil = prove
 (`!n. num_to_bits n = [] <=> n = 0`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [num_to_bits_src] THEN
  BOOL_CASES_TAC `n = 0` THEN
  REWRITE_TAC [NOT_CONS_NIL]);;

export_thm num_to_bits_eq_nil;;

let num_to_bits_zero = prove
 (`num_to_bits 0 = []`,
  REWRITE_TAC [num_to_bits_eq_nil]);;

export_thm num_to_bits_zero;;

let num_to_bits_one = prove
 (`num_to_bits 1 = [T]`,
  ONCE_REWRITE_TAC [num_to_bits_src] THEN
  REWRITE_TAC [num_to_bits_zero; bit_hd_one; bit_tl_one] THEN
  REWRITE_TAC [ONE; NOT_SUC]);;

export_thm num_to_bits_one;;

let num_to_bitvec_to_num = prove
 (`!n k. bits_to_num (num_to_bitvec n k) = bit_bound n k`,
  REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [num_to_bitvec_zero; bit_bound_zero; bits_to_num_nil];
   GEN_TAC THEN
   ASM_REWRITE_TAC [num_to_bitvec_suc; bit_bound_suc; bits_to_num_cons]]);;

export_thm num_to_bitvec_to_num;;

let num_to_bits_to_num = prove
 (`!n. bits_to_num (num_to_bits n) = n`,
  REWRITE_TAC [num_to_bits_def; num_to_bitvec_to_num; bit_bound_width]);;

export_thm num_to_bits_to_num;;

let bit_nth_bits_to_num = prove
 (`!l i. bit_nth (bits_to_num l) i <=> i < LENGTH l /\ nth l i`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [bits_to_num_nil; zero_bit_nth; LENGTH; LT];
   INDUCT_TAC THENL
   [REWRITE_TAC
      [LENGTH; LT_0; nth_zero; bit_nth_zero; bits_to_num_cons; bit_hd_cons];
    POP_ASSUM (K ALL_TAC) THEN
    ASM_REWRITE_TAC
      [bit_nth_suc; LENGTH; LT_SUC; bits_to_num_cons; bit_tl_cons] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    ASM_CASES_TAC `i < LENGTH (t : bool list)` THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC nth_suc THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC []]]]);;

export_thm bit_nth_bits_to_num;;

let bit_width_bits_to_num = prove
 (`!l. bit_width (bits_to_num l) <= LENGTH l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [bits_to_num_nil; bit_width_zero; LE_0];
   ONCE_REWRITE_TAC [bit_width_src] THEN
   BOOL_CASES_TAC `bits_to_num (CONS h t) = 0` THENL
   [REWRITE_TAC [LE_0];
    ASM_REWRITE_TAC
      [LENGTH; bits_to_num_cons; bit_tl_cons; GSYM ADD1; LE_SUC]]]);;

export_thm bit_width_bits_to_num;;

let bits_to_num_bound = prove
 (`!l. bits_to_num l < 2 EXP (LENGTH l)`,
  GEN_TAC THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 EXP (bit_width (bits_to_num l))` THEN
  REWRITE_TAC [lt_exp_bit_width; le_exp_two; bit_width_bits_to_num]);;

export_thm bits_to_num_bound;;

let bits_to_num_replicate_false = prove
 (`!k. bits_to_num (REPLICATE F k) = 0`,
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE_0; bits_to_num_nil];
   ASM_REWRITE_TAC [REPLICATE_SUC; bits_to_num_cons_eq_zero]]);;

export_thm bits_to_num_replicate_false;;

let bits_to_num_replicate_true = prove
 (`!k. bits_to_num (REPLICATE T k) = 2 EXP k - 1`,
  GEN_TAC THEN
  SUBGOAL_THEN
    `SUC (bits_to_num (REPLICATE T k)) = 2 EXP k`
    (fun th -> REWRITE_TAC [SUC_SUB1; SYM th]) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE_0; bits_to_num_nil; ONE; EXP_0];
   ASM_REWRITE_TAC
     [REPLICATE_SUC; bits_to_num_cons; suc_bit_cons_true; EXP_SUC] THEN
   REWRITE_TAC [bit_cons_def; bit_to_num_false; ZERO_ADD]]);;

export_thm bits_to_num_replicate_true;;

let is_bits_nil = prove
 (`is_bits []`,
  REWRITE_TAC [is_bits_def; NULL]);;

export_thm is_bits_nil;;

let is_bits_cons = prove
 (`!h t. is_bits (CONS h t) <=> if NULL t then h else is_bits t`,
  GEN_TAC THEN
  REWRITE_TAC [is_bits_def] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NULL_NIL; NULL_CONS; LAST_SING];
   REWRITE_TAC [NULL_CONS; LAST_MULTIPLE]]);;

export_thm is_bits_cons;;

let is_bits_replicate = prove
 (`!b k. is_bits (REPLICATE b k) <=> k = 0 \/ b`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE_0; is_bits_nil];
   ASM_REWRITE_TAC [REPLICATE_SUC; is_bits_cons; NOT_SUC; NULL_REPLICATE] THEN
   POP_ASSUM (K ALL_TAC) THEN
   COND_CASES_TAC THEN
   REWRITE_TAC []]);;

export_thm is_bits_replicate;;

let is_bits_width = prove
 (`!l. is_bits l <=> bit_width (bits_to_num l) = LENGTH l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [is_bits_nil; bits_to_num_nil; bit_width_zero; LENGTH];
   ONCE_REWRITE_TAC [bit_width_src] THEN
   ASM_REWRITE_TAC [is_bits_cons; LENGTH; bits_to_num_cons_eq_zero] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [bits_to_num_cons; bit_tl_cons; GSYM ADD1] THEN
   BOOL_CASES_TAC `h : bool` THENL
   [REWRITE_TAC [SUC_INJ; NULL_EQ_NIL] THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [bits_to_num_nil; bit_width_zero; LENGTH];
     REFL_TAC];
    SPEC_TAC (`t : bool list`, `l : bool list`) THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [bits_to_num_nil; NULL_NIL; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [NULL_CONS] THEN
     COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [NOT_SUC; bit_width_zero; LENGTH];
      REWRITE_TAC [SUC_INJ]]]]]);;

export_thm is_bits_width;;

let bits_to_num_to_bits = prove
 (`!l. is_bits l <=> num_to_bits (bits_to_num l) = l`,
  GEN_TAC THEN
  EQ_TAC THENL
  [REWRITE_TAC [is_bits_width] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC nth_eq THEN
   ASM_REWRITE_TAC [length_num_to_bits] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [num_to_bits_def; num_to_bitvec] THEN
   MP_TAC (ISPECL [`bit_nth (bits_to_num l)`;
                   `interval 0 (LENGTH (l : bool list))`;
                   `i : num`] nth_map) THEN
   ASM_REWRITE_TAC [length_interval] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`0`; `LENGTH (l : bool list)`; `i : num`] nth_interval) THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [bit_nth_bits_to_num];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [is_bits_width] THEN
   POP_ASSUM (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [length_num_to_bits]]);;

export_thm bits_to_num_to_bits;;

let is_bits_num_to_bits = prove
 (`!n. is_bits (num_to_bits n)`,
  REWRITE_TAC [bits_to_num_to_bits; num_to_bits_to_num]);;

export_thm is_bits_num_to_bits;;

let bit_width_ones = prove
 (`!k. bit_width (2 EXP k - 1) = k`,
  GEN_TAC THEN
  REWRITE_TAC [GSYM bits_to_num_replicate_true] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `LENGTH (REPLICATE T k)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [GSYM is_bits_width; is_bits_replicate];
   MATCH_ACCEPT_TAC LENGTH_REPLICATE]);;

export_thm bit_width_ones;;

let bit_cons_le_lcancel = prove
 (`!h t1 t2.
     bit_cons h t1 <= bit_cons h t2 <=>
     t1 <= t2`,
  REWRITE_TAC [bit_cons_def; LE_ADD_LCANCEL; LE_MULT_LCANCEL; two_nonzero]);;

export_thm bit_cons_le_lcancel;;

let bit_cons_le_rcancel = prove
 (`!h1 h2 t.
     bit_cons h1 t <= bit_cons h2 t <=>
     bit_to_num h1 <= bit_to_num h2`,
  REWRITE_TAC [bit_cons_def; LE_ADD_RCANCEL]);;

export_thm bit_cons_le_rcancel;;

let bit_cons_lt_lcancel = prove
 (`!h t1 t2.
     bit_cons h t1 < bit_cons h t2 <=>
     t1 < t2`,
  REWRITE_TAC [GSYM NOT_LE; bit_cons_le_lcancel]);;

export_thm bit_cons_lt_lcancel;;

let bit_cons_lt_rcancel = prove
 (`!h1 h2 t.
     bit_cons h1 t < bit_cons h2 t <=>
     bit_to_num h1 < bit_to_num h2`,
  REWRITE_TAC [GSYM NOT_LE; bit_cons_le_rcancel]);;

export_thm bit_cons_lt_rcancel;;

let bit_nth_width = prove
 (`!n i. bit_nth n i ==> i < bit_width n`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM num_to_bits_to_num)))) THEN
  REWRITE_TAC [bit_nth_bits_to_num; length_num_to_bits] THEN
  STRIP_TAC);;

export_thm bit_nth_width;;

let bit_width_cons = prove
 (`!h t. ~(t = 0) ==> bit_width (bit_cons h t) = SUC (bit_width t)`,
  REPEAT STRIP_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV bit_width_src)) THEN
  ASM_REWRITE_TAC [bit_cons_eq_zero; bit_tl_cons; ADD1]);;

export_thm bit_width_cons;;

let bit_width_cons_le = prove
 (`!h t. bit_width (bit_cons h t) <= SUC (bit_width t)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t = 0` THENL
  [ASM_REWRITE_TAC [bit_cons_zero; bit_width_zero; bit_width_bit_to_num] THEN
   REWRITE_TAC [GSYM ONE; GSYM TWO; GSYM LT_SUC_LE; bit_to_num_bound];
   MP_TAC (SPECL [`h : bool`; `t : num`] bit_width_cons) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_ACCEPT_TAC LE_REFL]);;

export_thm bit_width_cons_le;;

let bit_width_shl = prove
 (`!n k. ~(n = 0) ==> bit_width (bit_shl n k) = bit_width n + k`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_shl_zero; ADD_0];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [bit_shl_suc] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `SUC (bit_width (bit_shl n k))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC bit_width_cons THEN
    ASM_REWRITE_TAC [bit_shl_eq_zero];
    REWRITE_TAC [ADD_SUC; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]]);;

export_thm bit_width_shl;;

let bit_width_one_shl = prove
 (`!k. bit_width (bit_shl 1 k) = k + 1`,
  GEN_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `bit_width 1 + k` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bit_width_shl THEN
   REWRITE_TAC [ONE; NOT_SUC];
   REWRITE_TAC [bit_width_one] THEN
   MATCH_ACCEPT_TAC ADD_SYM]);;

export_thm bit_width_one_shl;;

let bit_width_shl_le = prove
 (`!n k. bit_width (bit_shl n k) <= bit_width n + k`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC [zero_bit_shl; bit_width_zero; LE_0];
   MP_TAC (SPECL [`n : num`; `k : num`] bit_width_shl) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_ACCEPT_TAC LE_REFL]);;

export_thm bit_width_shl_le;;

let bit_width_shr_le = prove
 (`!n j k. bit_width n <= j + k ==> bit_width (bit_shr n k) <= j`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `bit_shr n k = 0` THENL
  [ASM_REWRITE_TAC [bit_width_zero; LE_0];
   ALL_TAC] THEN
  CONV_TAC (REWR_CONV (GSYM (SPEC `k : num` LE_ADD_RCANCEL))) THEN
  MP_TAC (SPECL [`bit_shr n k`; `k : num`] bit_width_shl) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `bit_width n` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC bit_width_mono THEN
  CONV_TAC (REWR_CONV (GSYM (SPEC `bit_bound n k` LE_ADD_LCANCEL))) THEN
  REWRITE_TAC [bit_bound; LE_ADDR]);;

export_thm bit_width_shr_le;;

let bit_width_max = prove
 (`!m n. bit_width (MAX m n) = MAX (bit_width m) (bit_width n)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MAX] THEN
  COND_CASES_TAC THENL
  [MP_TAC (SPECL [`m : num`; `n : num`] bit_width_mono) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   MP_TAC (SPECL [`n : num`; `m : num`] bit_width_mono) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [GSYM NOT_LE];
    ALL_TAC] THEN
   STRIP_TAC THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [GSYM LE_ANTISYM];
    REFL_TAC]]);;

export_thm bit_width_max;;

let bit_width_add = prove
 (`!m n. bit_width (m + n) <= MAX (bit_width m) (bit_width n) + 1`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `bit_width (bit_shl (MAX m n) 1)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bit_width_mono THEN
   REWRITE_TAC [bit_shl_one; MULT_2] THEN
   MATCH_MP_TAC LE_ADD2 THEN
   REWRITE_TAC [LE_MAX1; LE_MAX2];
   REWRITE_TAC [GSYM bit_width_max] THEN
   ASM_CASES_TAC `MAX m n = 0` THENL
   [ASM_REWRITE_TAC [zero_bit_shl; bit_width_zero; LE_0];
    MP_TAC (SPECL [`MAX m n`; `1`] bit_width_shl) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LE_REFL]]]);;

export_thm bit_width_add;;

let bit_shr_bound_add = prove
 (`!n j k. bit_shr (bit_bound n (j + k)) k = bit_bound (bit_shr n k) j`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_0; bit_shr_zero];
   ASM_REWRITE_TAC [ADD_SUC; bit_bound_suc; bit_shr_suc'; bit_tl_cons]]);;

export_thm bit_shr_bound_add;;

let bit_shr_bound = prove
 (`!n k. bit_shr (bit_bound n k) k = 0`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`n : num`; `0`; `k : num`] bit_shr_bound_add) THEN
  REWRITE_TAC [ZERO_ADD; bit_bound_zero]);;

export_thm bit_shr_bound;;

let bit_nth_bound = prove
 (`!n i k. bit_nth (bit_bound n k) i <=> i < k /\ bit_nth n i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_nth_def] THEN
  ASM_CASES_TAC `i < (k : num)` THENL
  [ASM_REWRITE_TAC [] THEN
   POP_ASSUM
     (X_CHOOSE_THEN `j : num` SUBST_VAR_TAC o
      REWRITE_RULE [LT_EXISTS]) THEN
   REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] bit_shr_bound_add] THEN
   REWRITE_TAC [bit_bound_suc; bit_hd_cons];
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM
     (X_CHOOSE_THEN `j : num` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS; NOT_LT]) THEN
   REWRITE_TAC [bit_shr_add; bit_shr_bound; zero_bit_shr; bit_hd_zero]]);;

export_thm bit_nth_bound;;

let bit_bound_shl_add = prove
 (`!n j k. bit_bound (bit_shl n k) (j + k) = bit_shl (bit_bound n j) k`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [ADD_0; bit_shl_zero];
   ASM_REWRITE_TAC
     [ADD_SUC; bit_bound_suc; bit_shl_suc; bit_hd_cons; bit_tl_cons]]);;

export_thm bit_bound_shl_add;;

let bit_bound_shl = prove
 (`!n k. bit_bound (bit_shl n k) k = 0`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`n : num`; `0`; `k : num`] bit_bound_shl_add) THEN
  REWRITE_TAC [ZERO_ADD; bit_bound_zero; zero_bit_shl]);;

export_thm bit_bound_shl;;

let bit_bound_bound_min = prove
 (`!n j k. bit_bound (bit_bound n j) k = bit_bound n (MIN j k)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MIN] THEN
  COND_CASES_TAC THENL
  [POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   (CONV_TAC o REWR_CONV)
     (GSYM
       (SPEC `bit_shl (bit_shr (bit_bound n j) (j + d)) (j + d)`
         EQ_ADD_RCANCEL)) THEN
   SUBST1_TAC (SPECL [`bit_bound n j`; `j + d : num`] bit_bound) THEN
   REWRITE_TAC
     [bit_shr_add; bit_shr_bound; zero_bit_shr; zero_bit_shl; ADD_0];
   POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [LT_EXISTS; NOT_LE]) THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   SPEC_TAC (`k : num`, `k : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [bit_bound_zero];
    ASM_REWRITE_TAC [SUC_ADD; bit_bound_suc; bit_hd_cons; bit_tl_cons]]]);;

export_thm bit_bound_bound_min;;

let bit_bound_bound = prove
 (`!n k. bit_bound (bit_bound n k) k = bit_bound n k`,
  REWRITE_TAC [bit_bound_bound_min; MIN_REFL]);;

export_thm bit_bound_bound;;

let zero_bit_bound = prove
 (`!k. bit_bound 0 k = 0`,
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_bound_zero];
   ASM_REWRITE_TAC
     [bit_bound_suc; bit_tl_zero; bit_cons_zero; bit_hd_zero;
      bit_to_num_false]]);;

export_thm zero_bit_bound;;

let bit_bound_eq = prove
 (`!m n p k. m = n + bit_shl p k ==> bit_bound m k = bit_bound n k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST_VAR_TAC THEN
  (CONV_TAC o REWR_CONV)
    (GSYM
      (SPEC `bit_shl (bit_shr (n + bit_shl p k) k) k`
        EQ_ADD_RCANCEL)) THEN
  SUBST1_TAC (SPECL [`n + bit_shl p k`; `k : num`] bit_bound) THEN
  REWRITE_TAC [add_bit_shr; add_bit_shl; ADD_ASSOC; bit_bound]);;

export_thm bit_bound_eq;;

let add_bit_bound = prove
 (`!n1 n2 k. bit_bound (n1 + bit_shl n2 k) k = bit_bound n1 k`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_bound_eq THEN
  EXISTS_TAC `n2 : num` THEN
  REWRITE_TAC []);;

export_thm add_bit_bound;;

let bit_bound_add = prove
 (`!m n k. bit_bound (bit_bound m k + bit_bound n k) k = bit_bound (m + n) k`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC bit_bound_eq THEN
  EXISTS_TAC `bit_shr m k + bit_shr n k` THEN
  REWRITE_TAC [add_bit_shl] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_bound m k + bit_shl (bit_shr m k) k) +
     (bit_bound n k + bit_shl (bit_shr n k) k)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_bound];
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM]);;

export_thm bit_bound_add;;

let bit_bound_mult = prove
 (`!m n k. bit_bound (bit_bound m k * bit_bound n k) k = bit_bound (m * n) k`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC bit_bound_eq THEN
  EXISTS_TAC
    `bit_bound m k * bit_shr n k +
     n * bit_shr m k` THEN
  REWRITE_TAC
    [add_bit_shl; mult_bit_shl; ADD_ASSOC; GSYM LEFT_ADD_DISTRIB;
     bit_bound] THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV MULT_SYM))) THEN
  REWRITE_TAC [GSYM RIGHT_ADD_DISTRIB; bit_bound]);;

export_thm bit_bound_mult;;

let zero_bit_nth_imp = prove
 (`!n. (!i. ~bit_nth n i) ==> n = 0`,
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [bit_cons_eq_zero] THEN
  REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   ASM_REWRITE_TAC [bit_nth_zero; bit_hd_cons];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   ASM_REWRITE_TAC [bit_nth_suc; bit_tl_cons]]);;

export_thm zero_bit_nth_imp;;

let zero_bit_nth_eq = prove
 (`!n. (!i. ~bit_nth n i) <=> n = 0`,
  GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC zero_bit_nth_imp;
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [zero_bit_nth]]);;

export_thm zero_bit_nth_eq;;

let bit_nth_eq = prove
 (`!m n. (!i. bit_nth m i = bit_nth n i) ==> m = n`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [zero_bit_nth; zero_bit_nth_eq] THEN
  X_GEN_TAC `h2 : bool` THEN
  X_GEN_TAC `t2 : num` THEN
  STRIP_TAC THEN
  X_GEN_TAC `n : num` THEN
  MP_TAC (SPEC `n : num` bit_cons_cases) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `h1 : bool`
      (X_CHOOSE_THEN `t1 : num`
        SUBST_VAR_TAC)) THEN
  STRIP_TAC THEN
  REWRITE_TAC [bit_cons_inj] THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   REWRITE_TAC [bit_nth_zero; bit_hd_cons];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   GEN_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   REWRITE_TAC [bit_nth_suc; bit_tl_cons]]);;

export_thm bit_nth_eq;;

let bit_shr_width = prove
 (`!n. bit_shr n (bit_width n) = 0`,
  GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  GEN_TAC THEN
  REWRITE_TAC [GSYM bit_nth_add; zero_bit_nth] THEN
  MATCH_MP_TAC (ONCE_REWRITE_RULE [GSYM CONTRAPOS_THM] bit_nth_width) THEN
  REWRITE_TAC [NOT_LT; LE_ADD]);;

export_thm bit_shr_width;;

let bit_width_bound = prove
 (`!n k. bit_width (bit_bound n k) <= k`,
  CONV_TAC (REWR_CONV SWAP_FORALL_THM) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_bound_zero; bit_width_zero; LE_REFL];
   ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC [bit_bound_suc] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `SUC (bit_width (bit_bound (bit_tl n) k))` THEN
  ASM_REWRITE_TAC [bit_width_cons_le; LE_SUC]);;

export_thm bit_width_bound;;

let bit_shr_eq_zero = prove
 (`!n k. bit_shr n k = 0 <=> bit_width n <= k`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `k : num`] bit_bound) THEN
   ASM_REWRITE_TAC [zero_bit_shl; ADD_0] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [bit_width_bound];
   DISCH_THEN
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   REWRITE_TAC [bit_shr_add; bit_shr_width; zero_bit_shr]]);;

export_thm bit_shr_eq_zero;;

let bit_bound_id = prove
 (`!n k. bit_bound n k = n <=> bit_width n <= k`,
  REPEAT GEN_TAC THEN
  CONV_TAC
    (LAND_CONV
      (RAND_CONV
         (REWR_CONV (GSYM (SPECL [`n : num`; `k : num`] bit_bound))) THENC
       REWR_CONV EQ_SYM_EQ)) THEN
  REWRITE_TAC [EQ_ADD_LCANCEL_0; bit_shl_eq_zero; bit_shr_eq_zero]);;

export_thm bit_bound_id;;

let bit_width_mult = prove
 (`!m n. bit_width (m * n) <= bit_width m + bit_width n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_width_def; MULT_EQ_0] THEN
  ASM_CASES_TAC `m = 0` THENL
  [ASM_REWRITE_TAC [LE_0];
   ALL_TAC] THEN
  ASM_CASES_TAC `n = 0` THENL
  [ASM_REWRITE_TAC [LE_0];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
  MATCH_MP_TAC log_mult_upper_bound THEN
  ASM_REWRITE_TAC [TWO; SUC_LT]);;

export_thm bit_width_mult;;

let bit_width_upper_bound = prove
 (`!n k. bit_width n <= k <=> n < 2 EXP k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_width_def] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [LE_0; LT_NZ; EXP_EQ_0; TWO; NOT_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD1; LE_SUC_LT] THEN
  ASSUME_TAC (EQT_ELIM (NUM_REDUCE_CONV `1 < 2`)) THEN
  ASM_CASES_TAC `n < 2 EXP k` THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC log_upper_bound THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC log_lower_bound THEN
   ASM_REWRITE_TAC [GSYM NOT_LT]]);;

export_thm bit_width_upper_bound;;

let bit_bound_le = prove
 (`!n k. bit_bound n k <= n`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `bit_bound n k + bit_shl (bit_shr n k) k` THEN
  REWRITE_TAC [LE_ADD] THEN
  REWRITE_TAC [bit_bound; LE_REFL]);;

export_thm bit_bound_le;;

let num_to_bitvec_bound = prove
 (`!n k. num_to_bitvec (bit_bound n k) k = num_to_bitvec n k`,
  CONV_TAC (REWR_CONV SWAP_FORALL_THM) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [num_to_bitvec_zero];
   ASM_REWRITE_TAC
     [num_to_bitvec_suc; bit_bound_suc; bit_hd_cons; bit_tl_cons]]);;

export_thm num_to_bitvec_bound;;

let zero_to_bitvec = prove
 (`!k. num_to_bitvec 0 k = REPLICATE F k`,
  INDUCT_TAC THENL
  [REWRITE_TAC [num_to_bitvec_def; REPLICATE];
   ASM_REWRITE_TAC [num_to_bitvec_def; REPLICATE; bit_hd_zero; bit_tl_zero]]);;

export_thm zero_to_bitvec;;

let bits_to_num_to_long_bitvec = prove
 (`!l k.
     num_to_bitvec (bits_to_num l) (LENGTH l + k) =
     APPEND l (REPLICATE F k)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [bits_to_num_nil; zero_to_bitvec; APPEND; LENGTH; ZERO_ADD];
   ASM_REWRITE_TAC
     [bits_to_num_cons; LENGTH; SUC_ADD; num_to_bitvec_suc; bit_hd_cons;
      bit_tl_cons; APPEND]]);;

export_thm bits_to_num_to_long_bitvec;;

let bits_to_num_to_short_bitvec = prove
 (`!l k. k <= LENGTH l ==> num_to_bitvec (bits_to_num l) k = take k l`,
  LIST_INDUCT_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [bits_to_num_nil; zero_to_bitvec; LENGTH; LE] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [REPLICATE; take_zero];
   ALL_TAC] THEN
  GEN_TAC THEN
  REWRITE_TAC [bits_to_num_cons; LENGTH] THEN
  MP_TAC (SPEC `k : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `n : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [num_to_bitvec_zero; take_zero];
   ALL_TAC] THEN
  REWRITE_TAC [LE_SUC; num_to_bitvec_suc; bit_hd_cons; bit_tl_cons] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `n : num`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC take_suc THEN
  ASM_REWRITE_TAC []);;

export_thm bits_to_num_to_short_bitvec;;

let bits_to_num_to_bitvec = prove
 (`!l k.
     num_to_bitvec (bits_to_num l) k =
     if LENGTH l <= k then APPEND l (REPLICATE F (k - LENGTH l))
     else take k l`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o REWRITE_RULE [LE_EXISTS]) THEN
   REWRITE_TAC [bits_to_num_to_long_bitvec; ADD_SUB2];
   MATCH_MP_TAC bits_to_num_to_short_bitvec THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM NOT_LE]]);;

export_thm bits_to_num_to_bitvec;;

let bit_shr_bits_to_num = prove
 (`!l k.
     bit_shr (bits_to_num l) k =
     if LENGTH l <= k then 0 else bits_to_num (drop k l)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [bit_shr_eq_zero] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (l : bool list)` THEN
   ASM_REWRITE_TAC [bit_width_bits_to_num];
   ALL_TAC] THEN
  SUBGOAL_THEN `k <= LENGTH (l : bool list)` MP_TAC THENL
  [MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM NOT_LE];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`l : bool list`, `l : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [LE; LENGTH] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [bit_shr_zero; drop_zero];
   ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC (SPEC `k : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `n : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [bit_shr_zero; drop_zero];
   ALL_TAC] THEN
  REWRITE_TAC [LENGTH; LE_SUC; bits_to_num_cons; bit_shr_suc'; bit_tl_cons] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `n : num`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC drop_suc THEN
  ASM_REWRITE_TAC []);;

export_thm bit_shr_bits_to_num;;

let bit_bound_bits_to_num = prove
 (`!l k.
     bit_bound (bits_to_num l) k =
     bits_to_num (if LENGTH l <= k then l else take k l)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [bit_bound_id] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (l : bool list)` THEN
   ASM_REWRITE_TAC [bit_width_bits_to_num];
   ALL_TAC] THEN
  SUBGOAL_THEN `k <= LENGTH (l : bool list)` MP_TAC THENL
  [MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM NOT_LE];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  SPEC_TAC (`l : bool list`, `l : bool list`) THEN
  LIST_INDUCT_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [LE; LENGTH] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [bit_bound_zero; take_zero; bits_to_num_nil];
   ALL_TAC] THEN
  GEN_TAC THEN
  MP_TAC (SPEC `k : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `n : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [bit_bound_zero; take_zero; bits_to_num_nil];
   ALL_TAC] THEN
  REWRITE_TAC
    [LENGTH; LE_SUC; bits_to_num_cons; bit_bound_suc; bit_hd_cons;
     bit_tl_cons] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `n : num`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [GSYM bits_to_num_cons] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC take_suc THEN
  ASM_REWRITE_TAC []);;

export_thm bit_bound_bits_to_num;;

let bits_to_num_eq_zero = prove
 (`!l. bits_to_num l = 0 <=> ALL (~) l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [bits_to_num_nil; ALL];
   ASM_REWRITE_TAC [ALL; bits_to_num_cons; bit_cons_eq_zero]]);;

export_thm bits_to_num_eq_zero;;

let bit_to_num_inj = prove
 (`!b1 b2. bit_to_num b1 = bit_to_num b2 <=> b1 = b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_to_num_def; ONE] THEN
  BOOL_CASES_TAC `b1 : bool` THEN
  BOOL_CASES_TAC `b2 : bool` THEN
  REWRITE_TAC [NOT_SUC]);;

export_thm bit_to_num_inj;;

let bit_to_num_le = prove
 (`!b1 b2. bit_to_num b1 <= bit_to_num b2 <=> ~b1 \/ b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_to_num_def; ONE] THEN
  BOOL_CASES_TAC `b1 : bool` THEN
  BOOL_CASES_TAC `b2 : bool` THEN
  REWRITE_TAC [LE; NOT_SUC]);;

export_thm bit_to_num_le;;

let bit_to_num_lt = prove
 (`!b1 b2. bit_to_num b1 < bit_to_num b2 <=> ~b1 /\ b2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM NOT_LE; bit_to_num_le; DE_MORGAN_THM] THEN
  BOOL_CASES_TAC `b1 : bool` THEN
  ASM_REWRITE_TAC []);;

export_thm bit_to_num_lt;;

let bit_cons_lt_mono = prove
 (`!h1 h2 t1 t2. t1 < t2 ==> bit_cons h1 t1 < bit_cons h2 t2`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bit_cons_def] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `2 + 2 * t1` THEN
  REWRITE_TAC [LT_ADD_RCANCEL; bit_to_num_bound] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `2 * t2` THEN
  REWRITE_TAC [LE_ADDR] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     ONCE_REWRITE_RULE [ADD_SYM] o
     REWRITE_RULE [LT_EXISTS]) THEN
  REWRITE_TAC [LE_ADD_RCANCEL; LEFT_ADD_DISTRIB; ADD1; MULT_1; LE_ADDR]);;

export_thm bit_cons_lt_mono;;

let bit_cons_lt = prove
 (`!h1 h2 t1 t2.
     bit_cons h1 t1 < bit_cons h2 t2 <=>
     t1 < t2 \/ (t1 = t2 /\ bit_to_num h1 < bit_to_num h2)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `t1 < (t2 : num)` THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC bit_cons_lt_mono THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_CASES_TAC `t1 = (t2 : num)` THENL
  [ASM_REWRITE_TAC [bit_cons_lt_rcancel];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [NOT_LT] THEN
  MATCH_MP_TAC LT_IMP_LE THEN
  MATCH_MP_TAC bit_cons_lt_mono THEN
  ASM_REWRITE_TAC [GSYM NOT_LE; LE_LT]);;

export_thm bit_cons_lt;;

let bit_cons_le = prove
 (`!h1 h2 t1 t2.
     bit_cons h1 t1 <= bit_cons h2 t2 <=>
     t1 < t2 \/ (t1 = t2 /\ bit_to_num h1 <= bit_to_num h2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM NOT_LT; bit_cons_lt] THEN
  REWRITE_TAC [DE_MORGAN_THM; NOT_LT; LT_LE] THEN
  ASM_CASES_TAC `t1 = (t2 : num)` THENL
  [ASM_REWRITE_TAC [LE_REFL];
   ASM_REWRITE_TAC []]);;

export_thm bit_cons_le;;

let bit_shr_shl = prove
 (`!n k. bit_shr (bit_shl n k) k = n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_shl_zero; bit_shr_zero];
   ASM_REWRITE_TAC [bit_shr_suc'; bit_shl_suc; bit_tl_cons]]);;

export_thm bit_shr_shl;;

let bit_nth_shl = prove
 (`!n k i. bit_nth (bit_shl n k) i <=> k <= i /\ bit_nth n (i - k)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k <= (i : num)` THENL
  [POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   REWRITE_TAC [ADD_SUB2; LE_ADD; bit_nth_add; bit_shr_shl];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     REWRITE_RULE [LT_EXISTS; NOT_LE]) THEN
  REWRITE_TAC [ADD_SUC] THEN
  SPEC_TAC (`i : num`, `i : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [bit_nth_zero; bit_shl_suc; bit_hd_cons];
   ALL_TAC] THEN
  REWRITE_TAC [bit_nth_suc; bit_tl_cons; bit_shl_suc] THEN
  ASM_REWRITE_TAC [SUC_ADD]);;

export_thm bit_nth_shl;;

let add_bit_width = prove
 (`!m n j k.
     bit_width (bit_bound m k + bit_shl n k) <= j + k <=>
     bit_width n <= j`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   (CONV_TAC o LAND_CONV o RAND_CONV o REWR_CONV)
     (SYM (SPECL [`n : num`; `k : num`] bit_shr_shl)) THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `bit_width (bit_bound m k + bit_shl n k)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC bit_width_mono THEN
   REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  STRIP_TAC THEN
  (CONV_TAC o RAND_CONV o REWR_CONV) ADD_SYM THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH (APPEND (num_to_bitvec m k) (num_to_bits n))` THEN
  REVERSE_TAC CONJ_TAC THENL
  [ASM_REWRITE_TAC
     [LENGTH_APPEND; length_num_to_bitvec; LE_ADD_LCANCEL; length_num_to_bits];
   ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `bit_width (bits_to_num (APPEND (num_to_bitvec m k) (num_to_bits n)))` THEN
  REVERSE_TAC CONJ_TAC THENL
  [MATCH_ACCEPT_TAC bit_width_bits_to_num;
   ALL_TAC] THEN
  MATCH_MP_TAC bit_width_mono THEN
  REWRITE_TAC
    [bits_to_num_append; num_to_bitvec_to_num; num_to_bits_to_num;
     length_num_to_bitvec; LE_REFL]);;

export_thm add_bit_width;;

let zero_bit_cmp = prove
 (`!q n. bit_cmp q 0 n <=> q \/ ~(n = 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_cmp_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [LE_0; LT_NZ]);;

export_thm zero_bit_cmp;;

let bit_cmp_zero = prove
 (`!q n. bit_cmp q n 0 <=> q /\ n = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bit_cmp_def] THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [LE; LT]);;

export_thm bit_cmp_zero;;

let bit_cmp_cons = prove
 (`!q h1 h2 t1 t2.
     bit_cmp q (bit_cons h1 t1) (bit_cons h2 t2) =
     bit_cmp ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [bit_cmp_def; bit_cons_le; bit_cons_lt; bit_to_num_lt; bit_to_num_le] THEN
  REWRITE_TAC [LE_LT] THEN
  ASM_CASES_TAC `t1 < (t2 : num)` THENL
  [ASM_REWRITE_TAC [COND_ID];
   ALL_TAC] THEN
  REVERSE_TAC (ASM_CASES_TAC `t1 = (t2 : num)`) THENL
  [ASM_REWRITE_TAC [COND_ID];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  BOOL_CASES_TAC `h1 : bool` THEN
  BOOL_CASES_TAC `h2 : bool` THEN
  ASM_REWRITE_TAC [COND_ID]);;

export_thm bit_cmp_cons;;

let bit_nth_and = prove
 (`!m n i. bit_nth (bit_and m n) i <=> bit_nth m i /\ bit_nth n i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [bit_and_def; bit_nth_bits_to_num; LENGTH_MAP; length_interval;
     length_num_to_bits] THEN
  REVERSE_TAC (ASM_CASES_TAC `i < MIN (bit_width m) (bit_width n)`) THENL
  [ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LT_MIN; DE_MORGAN_THM]) THENL
   [DISJ1_TAC THEN
    MP_TAC (SPECL [`m : num`; `i : num`] bit_nth_width) THEN
    ASM_REWRITE_TAC [];
    DISJ2_TAC THEN
    MP_TAC (SPECL [`n : num`; `i : num`] bit_nth_width) THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MP_TAC
    (ISPECL
       [`\i. bit_nth m i /\ bit_nth n i`;
        `interval 0 (MIN (bit_width m) (bit_width n))`;
        `i : num`]
       nth_map) THEN
  ASM_REWRITE_TAC [length_interval] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`0`; `MIN (bit_width m) (bit_width n)`; `i : num`]
       nth_interval) THEN
  ASM_REWRITE_TAC [ZERO_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

export_thm bit_nth_and;;

let bit_and_refl = prove
 (`!n. bit_and n n = n`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  GEN_TAC THEN
  REWRITE_TAC [bit_nth_and]);;

export_thm bit_and_refl;;

let bit_and_comm = prove
 (`!m n. bit_and m n = bit_and n m`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  GEN_TAC THEN
  REWRITE_TAC [bit_nth_and] THEN
  MATCH_ACCEPT_TAC CONJ_SYM);;

export_thm bit_and_comm;;

let zero_bit_and = prove
 (`!n. bit_and 0 n = 0`,
  GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  REWRITE_TAC [zero_bit_nth; bit_nth_and]);;

export_thm zero_bit_and;;

let bit_and_zero = prove
 (`!n. bit_and n 0 = 0`,
  ONCE_REWRITE_TAC [bit_and_comm] THEN
  ACCEPT_TAC zero_bit_and);;

export_thm bit_and_zero;;

let bit_and_cons = prove
 (`!h1 h2 t1 t2.
     bit_and (bit_cons h1 t1) (bit_cons h2 t2) =
     bit_cons (h1 /\ h2) (bit_and t1 t2)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  X_GEN_TAC `i : num` THEN
  REWRITE_TAC [bit_nth_and] THEN
  MP_TAC (SPEC `i : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `n : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [bit_nth_zero; bit_hd_cons];
   REWRITE_TAC [bit_nth_suc; bit_tl_cons; bit_nth_and]]);;

export_thm bit_and_cons;;

let bit_and_le1 = prove
 (`!m n. bit_and m n <= m`,
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [zero_bit_and; LE_0] THEN
  X_GEN_TAC `h1 : bool` THEN
  X_GEN_TAC `t1 : num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [bit_and_zero; LE_0] THEN
  X_GEN_TAC `h2 : bool` THEN
  X_GEN_TAC `t2 : num` THEN
  DISCH_THEN (K ALL_TAC) THEN
  REWRITE_TAC [bit_and_cons; bit_cons_le] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LE_LT] o SPEC `t2 : num`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISJ2_TAC THEN
  ASM_REWRITE_TAC [bit_to_num_def] THEN
  BOOL_CASES_TAC `h2 : bool` THEN
  REWRITE_TAC [LE_REFL; LE_0]);;

export_thm bit_and_le1;;

let bit_and_le2 = prove
 (`!m n. bit_and m n <= n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [bit_and_comm] THEN
  MATCH_ACCEPT_TAC bit_and_le1);;

export_thm bit_and_le2;;

let bit_and_min = prove
 (`!m n. bit_and m n <= MIN m n`,
  REWRITE_TAC [LE_MIN; bit_and_le1; bit_and_le2]);;

export_thm bit_and_min;;

let bit_hd_and = prove
 (`!m n. bit_hd (bit_and m n) <=> bit_hd m /\ bit_hd n`,
  REWRITE_TAC [GSYM bit_nth_zero; bit_nth_and]);;

export_thm bit_hd_and;;

let bit_tl_and = prove
 (`!m n. bit_tl (bit_and m n) = bit_and (bit_tl m) (bit_tl n)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  REWRITE_TAC [GSYM bit_nth_suc; bit_nth_and]);;

export_thm bit_tl_and;;

let bit_bound_and = prove
 (`!m n k. bit_bound (bit_and m n) k = bit_and (bit_bound m k) (bit_bound n k)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  X_GEN_TAC `i : num` THEN
  REWRITE_TAC [bit_nth_and; bit_nth_bound] THEN
  ASM_CASES_TAC `i < (k : num)` THEN
  ASM_REWRITE_TAC []);;

export_thm bit_bound_and;;

let num_to_bitvec_bit_and = prove
 (`!m n k.
     num_to_bitvec (bit_and m n) k =
     zipwith ( /\ ) (num_to_bitvec m k) (num_to_bitvec n k)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`m : num`, `m : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [num_to_bitvec_zero; zipwith_nil];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [num_to_bitvec_suc] THEN
  MP_TAC
    (ISPECL
       [`( /\ )`;
        `bit_hd m`;
        `bit_hd n`;
        `num_to_bitvec (bit_tl m) k`;
        `num_to_bitvec (bit_tl n) k`]
       zipwith_cons) THEN
  REWRITE_TAC [length_num_to_bitvec] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [CONS_11; bit_hd_and; bit_tl_and]);;

export_thm num_to_bitvec_bit_and;;

let bit_and_ones = prove
 (`!n k. bit_and n (2 EXP k - 1) = bit_bound n k`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  X_GEN_TAC `i : num` THEN
  REWRITE_TAC
    [GSYM bits_to_num_replicate_true; bit_nth_and; bit_nth_bound;
     bit_nth_bits_to_num; LENGTH_REPLICATE] THEN
  BOOL_CASES_TAC `bit_nth n i` THEN
  REWRITE_TAC [] THEN
  ASM_CASES_TAC `i < (k : num)` THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC (ISPECL [`T`; `k : num`; `i : num`] nth_replicate) THEN
  ASM_REWRITE_TAC []);;

export_thm bit_and_ones;;

let bit_nth_or = prove
 (`!m n i. bit_nth (bit_or m n) i <=> bit_nth m i \/ bit_nth n i`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [bit_or_def; bit_nth_bits_to_num; LENGTH_MAP; length_interval;
     length_num_to_bits] THEN
  REVERSE_TAC (ASM_CASES_TAC `i < MAX (bit_width m) (bit_width n)`) THENL
  [ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [NOT_LT; MAX_LE] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`m : num`; `i : num`] bit_nth_width) THEN
   MP_TAC (SPECL [`n : num`; `i : num`] bit_nth_width) THEN
   ASM_REWRITE_TAC [GSYM NOT_LE] THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (ISPECL
       [`\i. bit_nth m i \/ bit_nth n i`;
        `interval 0 (MAX (bit_width m) (bit_width n))`;
        `i : num`]
       nth_map) THEN
  ASM_REWRITE_TAC [length_interval] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`0`; `MAX (bit_width m) (bit_width n)`; `i : num`]
       nth_interval) THEN
  ASM_REWRITE_TAC [ZERO_ADD] THEN
  DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

export_thm bit_nth_or;;

let bit_or_refl = prove
 (`!n. bit_or n n = n`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  GEN_TAC THEN
  REWRITE_TAC [bit_nth_or]);;

export_thm bit_or_refl;;

let bit_or_comm = prove
 (`!m n. bit_or m n = bit_or n m`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  GEN_TAC THEN
  REWRITE_TAC [bit_nth_or] THEN
  MATCH_ACCEPT_TAC DISJ_SYM);;

export_thm bit_or_comm;;

let zero_bit_or = prove
 (`!n. bit_or 0 n = n`,
  GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  REWRITE_TAC [zero_bit_nth; bit_nth_or]);;

export_thm zero_bit_or;;

let bit_or_zero = prove
 (`!n. bit_or n 0 = n`,
  ONCE_REWRITE_TAC [bit_or_comm] THEN
  ACCEPT_TAC zero_bit_or);;

export_thm bit_or_zero;;

let bit_or_cons = prove
 (`!h1 h2 t1 t2.
     bit_or (bit_cons h1 t1) (bit_cons h2 t2) =
     bit_cons (h1 \/ h2) (bit_or t1 t2)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  X_GEN_TAC `i : num` THEN
  REWRITE_TAC [bit_nth_or] THEN
  MP_TAC (SPEC `i : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `n : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [bit_nth_zero; bit_hd_cons];
   REWRITE_TAC [bit_nth_suc; bit_tl_cons; bit_nth_or]]);;

export_thm bit_or_cons;;

let bit_or_le1 = prove
 (`!m n. m <= bit_or m n`,
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [zero_bit_or; MAX_L0; LE_0] THEN
  X_GEN_TAC `h1 : bool` THEN
  X_GEN_TAC `t1 : num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [bit_or_zero; LE_REFL] THEN
  X_GEN_TAC `h2 : bool` THEN
  X_GEN_TAC `t2 : num` THEN
  DISCH_THEN (K ALL_TAC) THEN
  REWRITE_TAC [bit_or_cons; bit_cons_le] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LE_LT] o SPEC `t2 : num`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISJ2_TAC THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [bit_to_num_def] THEN
  BOOL_CASES_TAC `h2 : bool` THEN
  REWRITE_TAC [LE_REFL] THEN
  BOOL_CASES_TAC `h1 : bool` THEN
  REWRITE_TAC [LE_0; LE_REFL]);;

export_thm bit_or_le1;;

let bit_or_le2 = prove
 (`!m n. n <= bit_or m n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [bit_or_comm] THEN
  MATCH_ACCEPT_TAC bit_or_le1);;

export_thm bit_or_le2;;

let bit_or_max = prove
 (`!m n. MAX m n <= bit_or m n`,
  REWRITE_TAC [MAX_LE; bit_or_le1; bit_or_le2]);;

export_thm bit_or_max;;

let bit_hd_or = prove
 (`!m n. bit_hd (bit_or m n) <=> bit_hd m \/ bit_hd n`,
  REWRITE_TAC [GSYM bit_nth_zero; bit_nth_or]);;

export_thm bit_hd_or;;

let bit_tl_or = prove
 (`!m n. bit_tl (bit_or m n) = bit_or (bit_tl m) (bit_tl n)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  REWRITE_TAC [GSYM bit_nth_suc; bit_nth_or]);;

export_thm bit_tl_or;;

let bit_bound_or = prove
 (`!m n k. bit_bound (bit_or m n) k = bit_or (bit_bound m k) (bit_bound n k)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC bit_nth_eq THEN
  X_GEN_TAC `i : num` THEN
  REWRITE_TAC [bit_nth_or; bit_nth_bound] THEN
  ASM_CASES_TAC `i < (k : num)` THEN
  ASM_REWRITE_TAC []);;

export_thm bit_bound_or;;

let num_to_bitvec_bit_or = prove
 (`!m n k.
     num_to_bitvec (bit_or m n) k =
     zipwith ( \/ ) (num_to_bitvec m k) (num_to_bitvec n k)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`m : num`, `m : num`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [num_to_bitvec_zero; zipwith_nil];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [num_to_bitvec_suc] THEN
  MP_TAC
    (ISPECL
       [`( \/ )`;
        `bit_hd m`;
        `bit_hd n`;
        `num_to_bitvec (bit_tl m) k`;
        `num_to_bitvec (bit_tl n) k`]
       zipwith_cons) THEN
  REWRITE_TAC [length_num_to_bitvec] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [CONS_11; bit_hd_or; bit_tl_or]);;

export_thm num_to_bitvec_bit_or;;

let bit_or_eq_zero = prove
 (`!m n. bit_or m n = 0 <=> m = 0 /\ n = 0`,
  REPEAT GEN_TAC THEN
  REVERSE_TAC EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [zero_bit_or];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM LE; GSYM MAX_LE] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `bit_or m n` THEN
  ASM_REWRITE_TAC [bit_or_max]);;

export_thm bit_or_eq_zero;;

let bit_or_and = prove
 (`!m n. bit_or m n + bit_and m n = m + n`,
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [zero_bit_or; zero_bit_and; ZERO_ADD; ADD_0] THEN
  X_GEN_TAC `h1 : bool` THEN
  X_GEN_TAC `t1 : num` THEN
  STRIP_TAC THEN
  MATCH_MP_TAC bit_cons_induction THEN
  REWRITE_TAC [bit_or_zero; bit_and_zero; ADD_0] THEN
  X_GEN_TAC `h2 : bool` THEN
  X_GEN_TAC `t2 : num` THEN
  DISCH_THEN (K ALL_TAC) THEN
  REWRITE_TAC [bit_or_cons; bit_and_cons] THEN
  REWRITE_TAC [bit_cons_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (h1 \/ h2) + bit_to_num (h1 /\ h2)) +
     2 * (bit_or t1 t2 + bit_and t1 t2)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LEFT_ADD_DISTRIB; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  POP_ASSUM (SUBST1_TAC o SPEC `t2 : num`) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(bit_to_num h1 + bit_to_num h2) + 2 * (t1 + t2)` THEN
  REVERSE_TAC CONJ_TAC THENL
  [REWRITE_TAC [LEFT_ADD_DISTRIB; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  REWRITE_TAC [EQ_ADD_RCANCEL] THEN
  BOOL_CASES_TAC `h1 : bool` THEN
  REWRITE_TAC [bit_to_num_true; bit_to_num_false; ADD_0; ZERO_ADD]);;

export_thm bit_or_and;;

let random_uniform_loop_surj = prove
 (`!n i. i < n ==> ?r. random_uniform_loop n (bit_width (n - 1)) r = i`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `n : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `m : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  ONCE_REWRITE_TAC [random_uniform_loop_def] THEN
  REWRITE_TAC [SUC_SUB1; LT_SUC_LE; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL [`bit_width m`; `num_to_bitvec i (bit_width m)`]
       random_bits_surj) THEN
  REWRITE_TAC [length_num_to_bitvec] THEN
  DISCH_THEN (X_CHOOSE_THEN `r1 : random` STRIP_ASSUME_TAC) THEN
  MP_TAC (SPECL [`r1 : random`; `r2 : random`] split_random_surj) THEN
  DISCH_THEN (X_CHOOSE_THEN `r : random` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r : random` THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; num_to_bitvec_to_num] THEN
  SUBGOAL_THEN
    `bit_bound i (bit_width m) = i`
    (fun th -> ASM_REWRITE_TAC [th]) THEN
  REWRITE_TAC [bit_bound_id] THEN
  MATCH_MP_TAC bit_width_mono THEN
  ASM_REWRITE_TAC []);;

export_thm random_uniform_loop_surj;;

let random_uniform_surj = prove
 (`!n i. i < n ==> ?r. random_uniform n r = i`,
  REWRITE_TAC
    [random_uniform_def; LET_DEF; LET_END_DEF; random_uniform_loop_surj]);;

export_thm random_uniform_surj;;

let bit_tl_src = GSYM bit_shr_one;;

export_thm bit_tl_src;;

let bit_bound_src = prove
 (`!n k. bit_bound n k = n - bit_shl (bit_shr n k) k`,
  REPEAT GEN_TAC THEN
  (CONV_TAC o RAND_CONV o LAND_CONV o REWR_CONV)
    (SYM (SPECL [`n : num`; `k : num`] bit_bound)) THEN
  REWRITE_TAC [ADD_SUB]);;

export_thm bit_bound_src;;

let random_uniform_src = prove
 (`!n.
     random_uniform n =
     \r.
       let w = bit_width (n - 1) in
       random_uniform_loop n w r`,
  REWRITE_TAC [FUN_EQ_THM; random_uniform_def]);;

export_thm random_uniform_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for natural number to bit-list conversions.                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-haskell-src";;

export_thm bit_hd_def;;  (* Haskell *)
export_thm bit_tl_src;;  (* Haskell *)
export_thm bit_width_src;;  (* Haskell *)
export_thm bit_to_num_def;;  (* Haskell *)
export_thm bit_cons_def;;  (* Haskell *)
export_thm bit_nth_def;;  (* Haskell *)
export_thm bit_bound_src;;  (* Haskell *)
export_thm bit_append_def;;  (* Haskell *)
export_thm bits_to_num_def;;  (* Haskell *)
export_thm num_to_bitvec_src;;  (* Haskell *)
export_thm num_to_bits_src;;  (* Haskell *)
export_thm random_uniform_loop_def;;  (* Haskell *)
export_thm random_uniform_src;;  (* Haskell *)

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

logfile_end ();;

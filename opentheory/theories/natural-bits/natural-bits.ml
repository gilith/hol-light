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

let div2_induction = prove
 (`!p. p 0 /\ (!n. ~(n = 0) /\ p (n DIV 2) ==> p n) ==> !n. p n`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MATCH_MP_TAC div_induction THEN
  EXISTS_TAC `2` THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [TWO; LT_SUC_LE; LE_REFL]);;

let two_nonzero = prove
  (`~(2 = 0)`,
   REWRITE_TAC [TWO; NOT_SUC]);;

let zero_div_two = prove
  (`0 DIV 2 = 0`,
   MATCH_MP_TAC DIV_0 THEN
   ACCEPT_TAC two_nonzero);;

let even_zero = prove
  (`!n. n = 0 ==> EVEN n`,
   GEN_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [EVEN]);;

let cond_mod_two = prove
  (`!n. (if ODD n then 1 else 0) = n MOD 2`,
   GEN_TAC THEN
   MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
   STRIP_TAC THENL
   [MP_TAC (SPEC `n:num` EVEN_MOD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC (SPEC `n:num` NOT_ODD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]);
    MP_TAC (SPEC `n:num` ODD_MOD) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

let cons_div_two = prove
  (`!n h. ((if h then 1 else 0) + 2 * n) DIV 2 = n`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(2 * n) DIV 2 + (if h then 1 else 0) DIV 2` THEN
   CONJ_TAC THENL
   [MP_TAC (SPECL [`2 * n`; `if h then 1 else 0`; `2`] DIV_ADD_MOD) THEN
    COND_TAC THENL
    [NUM_REDUCE_TAC;
     ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
    MP_TAC (SPECL [`2`; `n : num`] MOD_MULT) THEN
    COND_TAC THENL
    [NUM_REDUCE_TAC;
     ALL_TAC] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th; ADD]) THEN
    BOOL_CASES_TAC `h:bool` THENL
    [REWRITE_TAC [] THEN
     NUM_REDUCE_TAC THEN
     REWRITE_TAC [GSYM ODD_MOD; GSYM ADD1; ODD_DOUBLE];
     REWRITE_TAC [] THEN
     NUM_REDUCE_TAC THEN
     REWRITE_TAC [GSYM EVEN_MOD; ADD_0; EVEN_DOUBLE]];
    ALL_TAC] THEN
   MP_TAC (SPECL [`2`; `n : num`] DIV_MULT) THEN
   COND_TAC THENL
   [NUM_REDUCE_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th; EQ_ADD_LCANCEL_0]) THEN
   MATCH_MP_TAC DIV_LT THEN
   BOOL_CASES_TAC `h : bool` THEN
   REWRITE_TAC [] THEN
   NUM_REDUCE_TAC);;

let exp_two_nz = prove
  (`!n. ~(2 EXP n = 0)`,
   REWRITE_TAC [EXP_EQ_0] THEN
   NUM_REDUCE_TAC);;

let le_exp_two = prove
  (`!m n. 2 EXP m <= 2 EXP n <=> m <= n`,
   REWRITE_TAC [LE_EXP] THEN
   NUM_REDUCE_TAC);;

let lt_exp_two = prove
  (`!m n. 2 EXP m < 2 EXP n <=> m < n`,
   REWRITE_TAC [LT_EXP] THEN
   NUM_REDUCE_TAC);;

let lt_exp_two_suc = prove
  (`!m n. m < 2 EXP n ==> 1 + 2 * m < 2 EXP SUC n`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 * (m + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LEFT_ADD_DISTRIB; LT_ADD_LCANCEL] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [EXP; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   ASM_REWRITE_TAC [GSYM ADD1; LE_SUC_LT]);;

let mod_exp_two_lt = prove
  (`!m n. m MOD (2 EXP n) < 2 EXP n`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m : num`; `2 EXP n`] DIVISION) THEN
   COND_TAC THENL
   [REWRITE_TAC [exp_two_nz];
    DISCH_THEN (fun th -> ACCEPT_TAC (CONJUNCT2 th))]);;

let div_exp_two_lt = prove
  (`!m n. m DIV (2 EXP n) = 0 <=> m < 2 EXP n`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC DIV_EQ_0 THEN
   MATCH_ACCEPT_TAC exp_two_nz);;

let odd_mod_exp_two = prove
  (`!m n. ODD (m MOD (2 EXP n)) <=> ODD m /\ ~(n = 0)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `n:num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [EXP; MULT_CLAUSES; MOD_1; ODD];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [NOT_SUC; EXP; ODD_MOD] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC MOD_MOD THEN
   REWRITE_TAC [GSYM EXP; exp_two_nz]);;

let mod_div_exp_two = prove
  (`!x m n.
      (x MOD (2 EXP m)) DIV (2 EXP n) =
      (if m <= n then 0 else (x DIV (2 EXP n)) MOD (2 EXP (m - n)))`,
   REPEAT GEN_TAC THEN
   bool_cases_tac `m <= (n : num)` THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIV_LT THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP m` THEN
    ASM_REWRITE_TAC [le_exp_two; mod_exp_two_lt];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`x : num`; `2 EXP n`; `2 EXP (m - n)`] DIV_MOD) THEN
   COND_TAC THENL
   [REWRITE_TAC [MULT_EQ_0; exp_two_nz];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [GSYM EXP_ADD] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC SUB_ADD2 THEN
   MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
   ASM_REWRITE_TAC []);;

(* ------------------------------------------------------------------------- *)
(* Definition of natural number to bit-list conversions.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-def";;

let bitwidth_def = new_definition
  `!n. bitwidth n = if n = 0 then 0 else log 2 n + 1`;;

export_thm bitwidth_def;;

let bit_to_num_def = new_definition
  `!b. bit_to_num b = if b then 1 else 0`;;

export_thm bit_to_num_def;;

let bit_cons_def = new_definition
  `!b n. bit_cons b n = bit_to_num b + 2 * n`;;

export_thm bit_cons_def;;

let bit_hd_def = new_definition
  `!n. bit_hd n = ODD n`;;

export_thm bit_hd_def;;

let bit_tl_def = new_definition
  `!n. bit_tl n = n DIV 2`;;

export_thm bit_tl_def;;

let bit_shl_def = new_definition
  `!n k. bit_shl n k = funpow (bit_cons F) k n`;;

export_thm bit_shl_def;;

let bit_shr_def = new_definition
  `!n k. bit_shr n k = funpow bit_tl k n`;;

export_thm bit_shr_def;;

let bit_nth_def = new_definition
  `!n i. bit_nth n i = bit_hd (bit_shr n i)`;;

export_thm bit_nth_def;;

let bit_bound_def = new_definition
  `!n k. bit_bound n k = n - bit_shl (bit_shr n k) k`;;

export_thm bit_bound_def;;

let bit_append_def = new_definition
  `!l n. bit_append l n = foldr bit_cons n l`;;

export_thm bit_append_def;;

let bits_to_num_def = new_definition
  `!l. bits_to_num l = bit_append l 0`;;

export_thm bits_to_num_def;;

let num_to_bits_def = new_definition
  `!n. num_to_bits n = MAP (bit_nth n) (interval 0 (bitwidth n))`;;

export_thm num_to_bits_def;;

let is_bits_def = new_definition
  `!l. is_bits l <=> NULL l \/ LAST l`;;

export_thm is_bits_def;;

let rdecode_uniform_loop_exists = prove
 (`!n w. ?loop. !r.
     loop r =
     let (l,r') = rbits w r in
     let m = bits_to_num l in
     if m < n then m else
     loop r'`,
  REPEAT GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ (r : random).
          let (l,r') = rbits w r in
          let m = bits_to_num l in
          ~(m < n)`;
       `\ (r : random).
          let (l,r') = rbits w r in
          let m = bits_to_num l in
          r'`;
       `\ (r : random).
          let (l,r') = rbits w r in
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
  PAIR_CASES_TAC `rbits w r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : bool list`
       (X_CHOOSE_THEN `r' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `bits_to_num l < n` THEN
  REWRITE_TAC []);;

let rdecode_uniform_loop_def =
  new_specification ["rdecode_uniform_loop"]
    (ONCE_REWRITE_RULE [SKOLEM_THM]
      (ONCE_REWRITE_RULE [SKOLEM_THM]
        rdecode_uniform_loop_exists));;

export_thm rdecode_uniform_loop_def;;

let rdecode_uniform_def = new_definition
  `!n r.
     rdecode_uniform n r =
     let w = bitwidth (n - 1) in
     let (r1,r2) = rsplit r in
     (rdecode_uniform_loop n w r1 MOD n, r2)`;;

export_thm rdecode_uniform_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of natural number to bit-list conversions.                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-thm";;

let length_num_to_bits = prove
  (`!n. LENGTH (num_to_bits n) = bitwidth n`,
   REWRITE_TAC [num_to_bits_def; LENGTH_MAP; length_interval]);;

export_thm length_num_to_bits;;

let bitwidth_zero = prove
  (`bitwidth 0 = 0`,
   REWRITE_TAC [bitwidth_def]);;

export_thm bitwidth_zero;;

let bitwidth_recursion = prove
  (`!n. bitwidth n = if n = 0 then 0 else bitwidth (n DIV 2) + 1`,
   GEN_TAC THEN
   REWRITE_TAC [bitwidth_def] THEN
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

export_thm bitwidth_recursion;;

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

let bit_hd_add = prove
  (`!m n. bit_hd (m + n) = ~(bit_hd m <=> bit_hd n)`,
   REWRITE_TAC [bit_hd_def; ODD_ADD]);;

export_thm bit_hd_add;;

let bit_hd_mult = prove
  (`!m n. bit_hd (m * n) = (bit_hd m /\ bit_hd n)`,
   REWRITE_TAC [bit_hd_def; ODD_MULT]);;

export_thm bit_hd_mult;;

let bit_hd_double = prove
  (`!n. ~bit_hd (2 * n)`,
   REWRITE_TAC [bit_hd_mult; bit_hd_two]);;

export_thm bit_hd_double;;

let bit_hd_cons = prove
  (`!b n. bit_hd (bit_cons b n) = b`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bit_cons_def; bit_hd_add; bit_hd_double; bit_to_num_hd]);;

export_thm bit_hd_cons;;

(***
let bit_tl_cons = prove
  (`!b n. bit_tl (bit_cons b n) = n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bit_tl_def; bit_cons_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `bit_to_num b DIV 2 + (2 * n) DIV 2` THEN
   CONJ_TAC THENL
   [MP_TAC (SPECL [`bit_to_num b`; `2 * n`; `2`] DIV_ADD_MOD) THEN
    REWRITE_TAC [two_nonzero] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (SPECL [`2`; `n : num`] MOD_MULT) THEN
    MP_TAC (SPECL [`bit_to_num b`; `2 * n`; `2`] MOD_ADD_MOD) THEN
    REWRITE_TAC [two_nonzero] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ADD_0] THEN
    MATCH_MP_TAC MOD_MOD_REFL THEN
    ACCEPT_TAC two_nonzero;
   MP_TAC (SPECL [`2`; `n : num`] DIV_MULT) THEN
   REWRITE_TAC [two_nonzero] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [EQ_ADD_RCANCEL_0] THEN
***
   MATCH_MP_TAC DIV_LT THEN
   BOOL_CASES_TAC `h : bool` THEN
   REWRITE_TAC [] THEN
   NUM_REDUCE_TAC);;


   MATCH_MP_TAC (TAUT `!x y z. ~y /\ (x <=> z) ==> (~(x <=> y) <=> z)`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [NOT_ODD; EVEN_DOUBLE];
    REWRITE_TAC [GSYM bit_hd_def; bit_to_num_hd]]);;

export_thm bit_hd_cons;;

let bit_to_num_tl = prove
  (`!b. bit_tl (bit_to_num b) = 0`,
   GEN_TAC THEN
   BOOL_CASES_TAC `b : bool` THEN
   REWRITE_TAC [bit_to_num_def; bit_hd_def; ODD_ZERO; ODD_SUC; ONE]);;

export_thm bit_to_num_hd;;



let num_shr_zero = prove
  (`!n. num_shr n 0 = n`,
   REWRITE_TAC [num_shr_def; funpow_zero; I_THM]);;

export_thm num_shr_zero;;

let num_shr_suc = prove
  (`!n k. num_shr n (SUC k) = num_shr n k DIV 2`,
   REWRITE_TAC [num_shr_def; funpow_suc; o_THM]);;

export_thm num_shr_suc;;

let num_shr_suc' = prove
  (`!n k. num_shr n (SUC k) = num_shr (n DIV 2) k`,
   REWRITE_TAC [num_shr_def; funpow_suc'; o_THM]);;

export_thm num_shr_suc';;

let num_shr_add = prove
  (`!n k1 k2. num_shr n (k1 + k2) = num_shr (num_shr n k1) k2`,
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   REWRITE_TAC [num_shr_def; funpow_add; o_THM]);;

export_thm num_shr_add;;

let num_bit_zero = prove
  (`!n. num_bit n 0 = ODD n`,
   REWRITE_TAC [num_bit_def; num_shr_zero]);;

export_thm num_bit_zero;;

let num_bit_suc = prove
  (`!n i. num_bit n (SUC i) = num_bit (n DIV 2) i`,
   REWRITE_TAC [num_bit_def; num_shr_suc']);;

export_thm num_bit_suc;;

let num_bit_div2 = prove
  (`!n. num_bit (n DIV 2) = num_bit n o SUC`,
   REWRITE_TAC [FUN_EQ_THM; num_bit_suc; o_THM]);;

export_thm num_bit_div2;;

let num_bit_add = prove
  (`!n k i. num_bit n (k + i) = num_bit (num_shr n k) i`,
   REWRITE_TAC [num_bit_def; GSYM num_shr_add]);;

export_thm num_bit_add;;

let zero_num_bit = prove
  (`!i. ~num_bit 0 i`,
   INDUCT_TAC THENL
   [REWRITE_TAC [num_bit_zero; ODD_ZERO];
    ASM_REWRITE_TAC [num_bit_suc; zero_div_two]]);;

export_thm zero_num_bit;;

let (bits_to_num_nil,bits_to_num_cons) =
  let def = new_recursive_definition list_RECURSION
    `(bits_to_num [] = 0) /\
     (!h t. bits_to_num (CONS h t) = bit_to_num h + 2 * bits_to_num t)` in
  CONJ_PAIR def;;

export_thm bits_to_num_nil;;
export_thm bits_to_num_cons;;

let num_to_bits_recursion = prove
  (`!n.
      num_to_bits n =
      if n = 0 then [] else CONS (ODD n) (num_to_bits (n DIV 2))`,
   GEN_TAC THEN
   REWRITE_TAC [num_to_bits_def] THEN
   ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC [bitwidth_def; interval_zero; MAP];
    ASM_REWRITE_TAC [] THEN
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [bitwidth_recursion])) THEN
    ASM_REWRITE_TAC [interval_suc; GSYM ADD1; MAP] THEN
    REWRITE_TAC [num_bit_zero; num_bit_div2; MAP_o; map_suc_interval]]);;

export_thm num_to_bits_recursion;;

let num_to_bits_eq_nil = prove
  (`!n. num_to_bits n = [] <=> n = 0`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [num_to_bits_recursion] THEN
   BOOL_CASES_TAC `n = 0` THEN
   REWRITE_TAC [NOT_CONS_NIL]);;

export_thm num_to_bits_eq_nil;;

let num_to_bits_zero = prove
  (`num_to_bits 0 = []`,
   REWRITE_TAC [num_to_bits_eq_nil]);;

export_thm num_to_bits_zero;;

let num_to_bits_one = prove
  (`num_to_bits 1 = [T]`,
   ONCE_REWRITE_TAC [num_to_bits_recursion] THEN
   NUM_REDUCE_TAC THEN
   REWRITE_TAC [num_to_bits_zero]);;

export_thm num_to_bits_one;;

let is_bits_nil = prove
  (`is_bits []`,
   REWRITE_TAC [is_bits_def; NULL]);;

export_thm is_bits_nil;;

***
let num_to_bits_to_num = prove
  (`!n. bits_to_num (num_to_bits n) = n`,
   MATCH_MP_TAC div2_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [num_to_bits_zero; bits_to_num_def];
    ONCE_REWRITE_TAC [num_to_bits_recursion] THEN
    ASM_REWRITE_TAC [bits_to_num_cons; cond_mod_two] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC DIVISION_DEF_DIV THEN
    REWRITE_TAC [TWO; NOT_SUC]]);;

export_thm num_to_bits_to_num;;

let bit_to_num_div2 = prove
  (`!b n. (bit_to_num b + 2 * n) DIV 2 = n`,
   REWRITE_TAC [bit_to_num_def; cons_div_two]);;

export_thm bit_to_num_div2;;

let bits_to_num_cons_div2 = prove
  (`!h t. bits_to_num (CONS h t) DIV 2 = bits_to_num t`,
   REWRITE_TAC [bits_to_num_cons; bit_to_num_div2]);;

export_thm bits_to_num_cons_div2;;

let num_bit_bits_to_num = prove
  (`!l i. num_bit (bits_to_num l) i <=> i < LENGTH l /\ nth l i`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [bits_to_num_def; zero_num_bit; LENGTH; LT];
    GEN_TAC THEN
    NUM_CASES_TAC `i : num` THENL
    [DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [LENGTH; LT_0; nth_zero; num_bit_zero] THEN
     REWRITE_TAC [bits_to_num_def; ODD_ADD] THEN
     SUBGOAL_THEN `ODD (2 * bits_to_num t) <=> F` SUBST1_TAC THENL
     [REWRITE_TAC [NOT_ODD; EVEN_DOUBLE];
      REWRITE_TAC [] THEN
      BOOL_CASES_TAC `h : bool` THEN
      REWRITE_TAC [ONE; ODD]];
     STRIP_TAC THEN
     ASM_REWRITE_TAC [num_bit_suc; LENGTH; LT_SUC; bits_to_num_cons_div2] THEN
     POP_ASSUM_LIST (K ALL_TAC) THEN
     ASM_CASES_TAC `n < LENGTH (t : bool list)` THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC EQ_SYM THEN
      MATCH_MP_TAC nth_suc THEN
      FIRST_ASSUM ACCEPT_TAC;
      ASM_REWRITE_TAC []]]]);;

export_thm num_bit_bits_to_num;;

let bitwidth_bits_to_num = prove
  (`!l. bitwidth (bits_to_num l) <= LENGTH l`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [bits_to_num_nil; bitwidth_zero; LE_0];
    ONCE_REWRITE_TAC [bitwidth_recursion] THEN
    BOOL_CASES_TAC `bits_to_num (CONS h t) = 0` THENL
    [REWRITE_TAC [LE_0];
     ASM_REWRITE_TAC [LENGTH; bits_to_num_cons_div2; GSYM ADD1; LE_SUC]]]);;

export_thm bitwidth_bits_to_num;;

let is_bits_bitwidth = prove
  (`!l. is_bits l <=> bitwidth (bits_to_num l) = LENGTH l`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [is_bits_nil; bits_to_num_nil; bitwidth_zero; LENGTH];
    ONCE_REWRITE_TAC [bitwidth_recursion] THEN
    REWRITE_TAC [LENGTH; bits_to_num_cons_div2; GSYM ADD1] THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [NOT_SUC; is_bits_def; NULL] THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN
     SPEC_TAC (`h : bool`, `b : bool`) THEN
     SPEC_TAC (`t : bool list`, `l : bool list`) THEN
     LIST_INDUCT_TAC THENL
     [GEN_TAC THEN
      REWRITE_TAC [LAST; NULL; bits_to_num_def; ADD_EQ_0; MULT_0] THEN
      BOOL_CASES_TAC `b : bool` THEN
      REWRITE_TAC [ONE; NOT_SUC];
      GEN_TAC THEN
      ONCE_REWRITE_TAC [bits_to_num_def] THEN
      REWRITE_TAC [LAST_MULTIPLE; NULL; ADD_EQ_0; MULT_EQ_0] THEN
      NUM_REDUCE_TAC THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC];
     ASM_REWRITE_TAC [SUC_INJ] THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [is_bits_def; NULL; LAST] THEN
     LIST_CASES_TAC `t : bool list` THENL
     [DISCH_THEN SUBST_VAR_TAC THEN
      REWRITE_TAC
        [NULL; LENGTH; bits_to_num_def; bitwidth_zero; MULT_0; ADD_0] THEN
      BOOL_CASES_TAC `h : bool` THEN
      REWRITE_TAC [ONE; NOT_SUC];
      DISCH_THEN
        (X_CHOOSE_THEN `b : bool`
          (X_CHOOSE_THEN `l : bool list` SUBST_VAR_TAC)) THEN
      REWRITE_TAC [NULL] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC []]]]);;

export_thm is_bits_bitwidth;;

let bits_to_num_to_bits = prove
  (`!l. is_bits l <=> num_to_bits (bits_to_num l) = l`,
   GEN_TAC THEN
   EQ_TAC THENL
   [REWRITE_TAC [is_bits_bitwidth] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC nth_eq THEN
    ASM_REWRITE_TAC [length_num_to_bits] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [num_to_bits_def] THEN
    MP_TAC (ISPECL [`num_bit (bits_to_num l)`;
                    `interval 0 (LENGTH (l : bool list))`;
                    `i : num`] nth_map) THEN
    ASM_REWRITE_TAC [length_interval] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPECL [`0`; `LENGTH (l : bool list)`; `i : num`] nth_interval) THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [num_bit_bits_to_num];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [is_bits_bitwidth] THEN
    POP_ASSUM (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
    REWRITE_TAC [length_num_to_bits]]);;

export_thm bits_to_num_to_bits;;

let is_bits_num_to_bits = prove
  (`!n. is_bits (num_to_bits n)`,
   REWRITE_TAC [bits_to_num_to_bits; num_to_bits_to_num]);;

export_thm is_bits_num_to_bits;;

let bitwidth_max = prove
  (`!m. bitwidth (2 EXP m - 1) = m`,
   GEN_TAC THEN
   REWRITE_TAC [bitwidth_def] THEN
   ASM_CASES_TAC `m = 0` THENL
   [ASM_REWRITE_TAC [EXP; SUB_REFL];
    ASM_CASES_TAC `2 EXP m - 1 = 0` THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN
     POP_ASSUM MP_TAC THEN
     NUM_CASES_TAC `2 EXP m` THENL
     [ASM_REWRITE_TAC [EXP_EQ_0; TWO; NOT_SUC];
      STRIP_TAC THEN
      ASM_REWRITE_TAC [SUC_SUB1] THEN
      ONCE_REWRITE_TAC [GSYM SUC_INJ] THEN
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [GSYM ONE; EXP_EQ_1] THEN
      NUM_REDUCE_TAC];
     ASM_REWRITE_TAC [] THEN
     POP_ASSUM (K ALL_TAC) THEN
     NUM_CASES_TAC `m : num` THENL
     [ASM_REWRITE_TAC [];
      STRIP_TAC THEN
      ASM_REWRITE_TAC [ADD1; EQ_ADD_RCANCEL] THEN
      MATCH_MP_TAC log_max THEN
      NUM_REDUCE_TAC]]]);;

export_thm bitwidth_max;;

let lt_exp_bitwidth = prove
  (`!n. n < 2 EXP (bitwidth n)`,
   GEN_TAC THEN
   REWRITE_TAC [bitwidth_def] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [EXP; ONE; SUC_LT];
    MATCH_MP_TAC lt_exp_log THEN
    ASM_REWRITE_TAC [TWO; SUC_LT]]);;

export_thm lt_exp_bitwidth;;

let bits_to_num_bound = prove
  (`!l. bits_to_num l < 2 EXP (LENGTH l)`,
   GEN_TAC THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (bitwidth (bits_to_num l))` THEN
   REWRITE_TAC [lt_exp_bitwidth; le_exp_two; bitwidth_bits_to_num]);;

export_thm bits_to_num_bound;;

let bits_to_num_append = prove
  (`!l1 l2.
      bits_to_num (APPEND l1 l2) =
      bits_to_num l1 + 2 EXP (LENGTH l1) * bits_to_num l2`,
   GEN_TAC THEN
   X_GEN_TAC `l : bool list` THEN
   SPEC_TAC (`l1 : bool list`, `l1 : bool list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [NIL_APPEND; bits_to_num_nil; LENGTH; EXP_0; ZERO_ADD; ONE_MULT];
    ASM_REWRITE_TAC
      [CONS_APPEND; bits_to_num_cons; LENGTH; EXP_SUC; GSYM ADD_ASSOC;
       EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB; GSYM MULT_ASSOC]]);;

export_thm bits_to_num_append;;

let bits_to_num_replicate_false = prove
  (`!m. bits_to_num (REPLICATE F m) = 0`,
   INDUCT_TAC THENL
   [REWRITE_TAC [REPLICATE_0; bits_to_num_nil];
    ASM_REWRITE_TAC [REPLICATE_SUC; bits_to_num_cons; MULT_0; ZERO_ADD]]);;

export_thm bits_to_num_replicate_false;;

let bits_to_num_replicate_true = prove
  (`!m. bits_to_num (REPLICATE T m) = 2 EXP m - 1`,
   GEN_TAC THEN
   SUBGOAL_THEN
     `1 + bits_to_num (REPLICATE T m) = 2 EXP m`
     (fun th -> REWRITE_TAC [ADD_SUB2; SYM th]) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN   
   INDUCT_TAC THENL
   [REWRITE_TAC [REPLICATE_0; bits_to_num_nil; ADD_0; EXP_0];
    REWRITE_TAC [REPLICATE_SUC; bits_to_num_cons; ADD_ASSOC; EXP_SUC] THEN
    SUBGOAL_THEN `1 + 1 = 2 * 1` SUBST1_TAC THENL
    [NUM_REDUCE_TAC;
     ASM_REWRITE_TAC [GSYM LEFT_ADD_DISTRIB]]]);;

export_thm bits_to_num_replicate_true;;

logfile_end ();;
***)

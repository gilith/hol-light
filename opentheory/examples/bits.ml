(* ------------------------------------------------------------------------- *)
(* A theory of natural numbers represented as bits.                          *)
(* ------------------------------------------------------------------------- *)

logfile "natural-bits-def";;

let bitwidth_def = new_definition
  `!n. bitwidth n = if n = 0 then 0 else log 2 n + 1`;;

export_thm bitwidth_def;;

let num_bit_def = new_definition
  `!n i. num_bit n i = ODD (n DIV (2 EXP i))`;;

export_thm num_bit_def;;

let num_to_bits_def = new_definition
  `!n. num_to_bits n = MAP (num_bit n) (interval 0 (bitwidth n))`;;

export_thm num_to_bits_def;;

let is_bits_def = new_definition
  `!l. is_bits l <=> NULL l \/ LAST l`;;

export_thm is_bits_def;;

let (bits_to_num_nil,bits_to_num_cons) =
  let def = new_recursive_definition list_RECURSION
    `(bits_to_num [] = 0) /\
     (!h t.
        bits_to_num (CONS h t) =
        2 * bits_to_num t + (if h then 1 else 0))` in
  CONJ_PAIR def;;

export_thm bits_to_num_nil;;
export_thm bits_to_num_cons;;

let bits_to_num_def = CONJ bits_to_num_nil bits_to_num_cons;;

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

logfile "natural-bits-thm";;

(* Helper theorems (not exported) *)

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

(* Exported theorems *)

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
     MP_TAC (SPECL [`n : num`; `2`] DIV_EQ_0) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [TWO; NOT_SUC];
      DISCH_THEN SUBST1_TAC THEN
      REFL_TAC]]]);;

export_thm bitwidth_recursion;;

let num_bit_zero = prove
  (`!n. num_bit n 0 = ODD n`,
   GEN_TAC THEN
   REWRITE_TAC [num_bit_def; EXP_0; DIV_1]);;

export_thm num_bit_zero;;

let num_bit_suc = prove
  (`!n i. num_bit n (SUC i) = num_bit (n DIV 2) i`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [num_bit_def; EXP] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC DIV_DIV THEN
   REWRITE_TAC [GSYM EXP_SUC; EXP_EQ_0; NOT_SUC; TWO]);;

export_thm num_bit_suc;;

let num_bit_div2 = prove
  (`!n. num_bit (n DIV 2) = num_bit n o SUC`,
   REWRITE_TAC [FUN_EQ_THM; num_bit_suc; o_THM]);;

export_thm num_bit_div2;;

let zero_num_bit = prove
  (`!i. ~num_bit 0 i`,
   GEN_TAC THEN
   REWRITE_TAC [num_bit_def] THEN
   MP_TAC (SPEC `2 EXP i` DIV_0) THEN
   REWRITE_TAC [EXP_EQ_0] THEN
   ANTS_TAC THENL
   [REWRITE_TAC [TWO; NOT_SUC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ODD]]);;

export_thm zero_num_bit;;

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

let is_bits_num_to_bits = prove
  (`!n. is_bits (num_to_bits n)`,
   MATCH_MP_TAC div2_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [num_to_bits_zero; is_bits_nil];
    ONCE_REWRITE_TAC [num_to_bits_recursion] THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [is_bits_def] THEN
    (LIST_CASES_TAC `num_to_bits (n DIV 2)` THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [NULL]) THENL
    [POP_ASSUM MP_TAC THEN
     REWRITE_TAC [num_to_bits_eq_nil] THEN
     MP_TAC (SPECL [`n : num`; `2`] DIV_EQ_0) THEN
     REWRITE_TAC [TWO; NOT_SUC] THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC [LT; ONE] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [ODD; LAST; NULL];
     CONV_TAC (RAND_CONV (REWR_CONV LAST)) THEN
     REWRITE_TAC [NULL]]]);;

export_thm is_bits_num_to_bits;;

let num_to_bits_to_num = prove
  (`!n. bits_to_num (num_to_bits n) = n`,
   MATCH_MP_TAC div2_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [num_to_bits_zero; bits_to_num_def];
    ONCE_REWRITE_TAC [num_to_bits_recursion] THEN
    ASM_REWRITE_TAC [bits_to_num_def; cond_mod_two] THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    MATCH_MP_TAC DIVISION_DEF_DIV THEN
    REWRITE_TAC [TWO; NOT_SUC]]);;

export_thm num_to_bits_to_num;;

let bits_to_num_cons_div2 = prove
  (`!h t. bits_to_num (CONS h t) DIV 2 = bits_to_num t`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bits_to_num_def] THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   MP_TAC
     (SPECL [`bits_to_num t`; `if h then 1 else 0`; `2`]
        DIV_MULT_ADD) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [TWO; NOT_SUC];
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [EQ_ADD_LCANCEL_0] THEN
    BOOL_CASES_TAC `h : bool` THEN
    NUM_REDUCE_TAC]);;

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

let is_bits_bitwidth = prove
  (`!l. is_bits l <=> bitwidth (bits_to_num l) = LENGTH l`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [is_bits_nil; bits_to_num_nil; bitwidth_zero; LENGTH];
    ONCE_REWRITE_TAC [bitwidth_recursion] THEN
    REWRITE_TAC [LENGTH; bits_to_num_cons_div2; GSYM ADD1] THEN
    ASM_CASES_TAC `bits_to_num (CONS h t) = 0` THENL
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
        [NULL; LENGTH; bits_to_num_def; bitwidth_zero; MULT_0; ZERO_ADD] THEN
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

logfile_end ();;

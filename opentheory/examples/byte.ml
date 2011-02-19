(* ------------------------------------------------------------------------- *)
(* A type of bytes.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "byte-def";;

let byte_width_def = new_definition
  `byte_width = 8`;;

export_thm byte_width_def;;

logfile_end ();;

(* Start of parametric theory instantiation: word *)

#use "word-byte.ml";;

(* word-def *)

logfile "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

export_thm word_size_def;;

let word_size_nonzero = prove
  (`~(word_size = 0)`,
   REWRITE_TAC [word_size_def; EXP_EQ_0] THEN
   NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

(* Start of parametric theory instantiation: modular *)

(* modular-mod *)

let lt_word_size = new_axiom
  `!n. n < word_size ==> n MOD word_size = n`;;

let word_size_lt = new_axiom
  `!n. n MOD word_size < word_size`;;

let mod_mod_word_size = new_axiom
  `!n. n MOD word_size MOD word_size = n MOD word_size`;;

let add_mod_word_size = new_axiom
  `!m n.
     (m MOD word_size + n MOD word_size) MOD word_size =
     (m + n) MOD word_size`;;

let mult_mod_word_size = new_axiom
  `!m n.
     (m MOD word_size * n MOD word_size) MOD word_size =
     (m * n) MOD word_size`;;

(* modular-def *)

new_type ("word",0);;

new_constant ("word_add", `:word -> word -> word`);;
new_constant ("word_mult", `:word -> word -> word`);;
new_constant ("word_neg", `:word -> word`);;
new_constant ("word_sub", `:word -> word -> word`);;
new_constant ("word_le", `:word -> word -> bool`);;
new_constant ("word_lt", `:word -> word -> bool`);;
new_constant ("num_to_word", `:num -> word`);;
new_constant ("word_to_num", `:word -> num`);;

let word_to_num_to_word = new_axiom
  `!x. num_to_word (word_to_num x) = x`;;

let num_to_word_inj = new_axiom
  `!x y.
     x < word_size /\ y < word_size /\ num_to_word x = num_to_word y ==>
     x = y`;;

let num_to_word_to_num = new_axiom
  `!x. word_to_num (num_to_word x) = x MOD word_size`;;

let num_to_word_add = new_axiom
  `!x1 y1.
     num_to_word (x1 + y1) = word_add (num_to_word x1) (num_to_word y1)`;;

let num_to_word_mult = new_axiom
  `!x1 y1.
     num_to_word (x1 * y1) = word_mult (num_to_word x1) (num_to_word y1)`;;

let word_neg_def = new_axiom
  `!x. word_neg x = num_to_word (word_size - word_to_num x)`;;

let word_sub_def = new_axiom
  `!x y. word_sub x y = word_add x (word_neg y)`;;

let word_le_def = new_axiom
  `!x y. word_le x y = word_to_num x <= word_to_num y`;;

let word_lt_def = new_axiom
  `!x y. word_lt x y = ~(word_le y x)`;;

(* modular-thm *)

let word_to_num_inj = new_axiom
  `!x y. word_to_num x = word_to_num y ==> x = y`;;

let num_to_word_eq = new_axiom
  `!x y. num_to_word x = num_to_word y <=> x MOD word_size = y MOD word_size`;;

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

let word_to_num_div_bound = new_axiom
  `!x. word_to_num x DIV word_size = 0`;;

let word_add_to_num = new_axiom
  `!x y.
     word_to_num (word_add x y) =
     (word_to_num x + word_to_num y) MOD word_size`;;

(* End of parametric theory instantiation: modular *)

logfile "word-bits-def";;

let word_shl_def = new_definition
 `!w n. word_shl w n = num_to_word ((2 EXP n) * word_to_num w)`;;

export_thm word_shl_def;;

let word_shr_def = new_definition
 `!w n. word_shr w n = num_to_word (word_to_num w DIV (2 EXP n))`;;

export_thm word_shr_def;;

let word_bit_def = new_definition
 `!w n. word_bit w n = ODD (word_to_num (word_shr w n))`;;

export_thm word_bit_def;;

let word_to_list_def = new_definition
 `!w. word_to_list w = MAP (word_bit w) (interval 0 word_width)`;;

export_thm word_to_list_def;;

let list_to_word_def = new_recursive_definition list_RECURSION
  `(list_to_word [] = num_to_word 0) /\
   (!h t.
      list_to_word (CONS h t) =
      if h then word_add (word_shl (list_to_word t) 1) (num_to_word 1)
      else word_shl (list_to_word t) 1)`;;

export_thm list_to_word_def;;

let is_word_list_def = new_definition
 `!l. is_word_list (l : bool list) <=> LENGTH l = word_width`;;

export_thm is_word_list_def;;

let word_and_def = new_definition
  `!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_and_def;;

let word_or_def = new_definition
  `!w1 w2.
     word_or w1 w2 =
     list_to_word (zipwith ( \/ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_or_def;;

let word_not_def = new_definition
  `!w. word_not w = list_to_word (MAP (~) (word_to_list w))`;;

export_thm word_not_def;;

logfile "word-bits-thm";;

(* Helper theorems (not exported) *)

let even_0 = prove
  (`!n. n = 0 ==> EVEN n`,
   GEN_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [EVEN]);;

let cons_div_2 = prove
  (`!n h. (2 * n + (if h then 1 else 0)) DIV 2 = n`,
   REPEAT GEN_TAC THEN
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

let exp_2_nz = prove
  (`!n. ~(2 EXP n = 0)`,
   REWRITE_TAC [EXP_EQ_0] THEN
   NUM_REDUCE_TAC);;

let le_exp_2 = prove
  (`!m n. 2 EXP m <= 2 EXP n <=> m <= n`,
   REWRITE_TAC [LE_EXP] THEN
   NUM_REDUCE_TAC);;

let lt_exp_2 = prove
  (`!m n. 2 EXP m < 2 EXP n <=> m < n`,
   REWRITE_TAC [LT_EXP] THEN
   NUM_REDUCE_TAC);;

let lt_exp_2_suc = prove
  (`!m n. m < 2 EXP n ==> 2 * m + 1 < 2 EXP SUC n`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 * (m + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LEFT_ADD_DISTRIB; LT_ADD_LCANCEL] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [EXP; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   ASM_REWRITE_TAC [GSYM ADD1; LE_SUC_LT]);;

let mod_exp_2_lt = prove
  (`!m n. m MOD (2 EXP n) < 2 EXP n`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m : num`; `2 EXP n`] DIVISION) THEN
   COND_TAC THENL
   [REWRITE_TAC [exp_2_nz];
    DISCH_THEN (fun th -> ACCEPT_TAC (CONJUNCT2 th))]);;

let div_exp_2_lt = prove
  (`!m n. m DIV (2 EXP n) = 0 <=> m < 2 EXP n`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC DIV_EQ_0 THEN
   MATCH_ACCEPT_TAC exp_2_nz);;

let cond_mod_2 = prove
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

let odd_mod_exp_2 = prove
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
   REWRITE_TAC [GSYM EXP; exp_2_nz]);;

let mod_div_exp_2 = prove
  (`!x m n.
      (x MOD (2 EXP m)) DIV (2 EXP n) =
      (if m <= n then 0 else (x DIV (2 EXP n)) MOD (2 EXP (m - n)))`,
   REPEAT GEN_TAC THEN
   bool_cases_tac `m <= n` THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC DIV_LT THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP m` THEN
    ASM_REWRITE_TAC [le_exp_2; mod_exp_2_lt];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`x : num`; `2 EXP n`; `2 EXP (m - n)`] DIV_MOD) THEN
   COND_TAC THENL
   [REWRITE_TAC [MULT_EQ_0; exp_2_nz];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [GSYM EXP_ADD] THEN
   AP_TERM_TAC THEN
   ASM_ARITH_TAC);;

(* Exported theorems *)

let length_word_to_list = prove
  (`!w. LENGTH (word_to_list w) = word_width`,
   REWRITE_TAC [word_to_list_def; LENGTH_MAP; length_interval]);;

export_thm length_word_to_list;;

let is_word_to_list = prove
  (`!w. is_word_list (word_to_list w)`,
   REWRITE_TAC [is_word_list_def; length_word_to_list]);;

export_thm is_word_to_list;;

let word_bit_div = prove
  (`!w n. word_bit w n = ODD (word_to_num w DIV (2 EXP n))`,
   REWRITE_TAC [word_bit_def; word_shr_def; num_to_word_to_num] THEN
   REPEAT GEN_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC lt_word_size THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `word_to_num w` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC DIV_LE THEN
    REWRITE_TAC [EXP_EQ_0] THEN
    NUM_REDUCE_TAC;
    REWRITE_TAC [word_to_num_bound]]);;

export_thm word_bit_div;;

let nil_to_word_to_num = prove
  (`word_to_num (list_to_word []) = 0`,
   REWRITE_TAC [list_to_word_def; num_to_word_to_num] THEN
   MATCH_MP_TAC lt_word_size THEN
   REWRITE_TAC [LT_NZ; word_size_nonzero]);;

export_thm nil_to_word_to_num;;

let cons_to_word_to_num = prove
  (`!h t.
      word_to_num (list_to_word (CONS h t)) =
      (2 * word_to_num (list_to_word t) + (if h then 1 else 0)) MOD word_size`,
   REWRITE_TAC [list_to_word_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `h : bool` BOOL_CASES_AX) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC
      [word_add_to_num; word_shl_def; EXP_1; word_to_num_to_word] THEN
    REWRITE_TAC [num_to_word_to_num; add_mod_word_size];
    ASM_REWRITE_TAC [word_shl_def; EXP_1; word_to_num_to_word; ADD_0] THEN
    REWRITE_TAC [num_to_word_to_num; add_mod_word_size]]);;

export_thm cons_to_word_to_num;;

let list_to_word_to_num_bound = prove
  (`!l. word_to_num (list_to_word l) < 2 EXP (LENGTH l)`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [nil_to_word_to_num; LENGTH; EXP] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [cons_to_word_to_num; LENGTH] THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `2 * word_to_num (list_to_word t) + (if h then 1 else 0)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC MOD_LE THEN
    ACCEPT_TAC word_size_nonzero;
    ALL_TAC] THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `2 * word_to_num (list_to_word t) + 1` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_ADD_LCANCEL] THEN
    BOOL_CASES_TAC `h : bool`THEN
    REWRITE_TAC [LE_REFL] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC lt_exp_2_suc THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm list_to_word_to_num_bound;;

let list_to_word_to_num_bound_suc = prove
  (`!l. 2 * word_to_num (list_to_word l) + 1 < 2 EXP (SUC (LENGTH l))`,
   GEN_TAC THEN
   MATCH_MP_TAC lt_exp_2_suc THEN
   MATCH_ACCEPT_TAC list_to_word_to_num_bound);;

export_thm list_to_word_to_num_bound_suc;;

let cons_to_word_to_num_bound = prove
  (`!h t.
      2 * word_to_num (list_to_word t) + (if h then 1 else 0) <
      2 EXP SUC (LENGTH t)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `2 * word_to_num (list_to_word t) + 1` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_ADD_LCANCEL] THEN
    BOOL_CASES_TAC `h : bool` THEN
    REWRITE_TAC [LE_REFL; LE_0];
    MATCH_ACCEPT_TAC list_to_word_to_num_bound_suc]);;

export_thm cons_to_word_to_num_bound;;

let word_to_list_to_word = prove
  (`!w. list_to_word (word_to_list w) = w`,
   GEN_TAC THEN
   REWRITE_TAC [word_to_list_def] THEN
   MATCH_MP_TAC word_to_num_inj THEN
   MATCH_MP_TAC (ITAUT`!p q. (p ==> q) /\ p ==> q`) THEN
   EXISTS_TAC
     `!k.
        k <= word_width ==>
        word_to_num
          (list_to_word (MAP (word_bit w) (interval (word_width - k) k))) =
          word_to_num w DIV (2 EXP (word_width - k))` THEN
   CONJ_TAC THENL
   [DISCH_THEN (MP_TAC o SPEC `word_width`) THEN
    REWRITE_TAC [SUB_REFL; LE_REFL; EXP; DIV_1];
    ALL_TAC] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC
      [SUB; interval_def; MAP; nil_to_word_to_num; GSYM word_size_def;
       word_to_num_div_bound];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   PAT_ASSUM `X ==> Y` THEN
   MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC k` THEN
    ASM_REWRITE_TAC [LE; LE_REFL];
    ALL_TAC] THEN
   REWRITE_TAC [interval_def; MAP; cons_to_word_to_num] THEN
   KNOW_TAC `word_width - k = SUC (word_width - SUC k)` THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [word_bit_div; cond_mod_2] THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [EXP] THEN
   MP_TAC (SPECL [`word_to_num w`; `2 EXP (word_width - SUC k)`;
                   `2`] (ONCE_REWRITE_RULE [MULT_SYM] DIV_DIV)) THEN
   MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM EXP; EXP_EQ_0] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   MP_TAC (SPECL [`word_to_num w DIV (2 EXP (word_width - SUC k))`;
                   `2`] DIVISION) THEN
   MATCH_MP_TAC (ITAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
   CONJ_TAC THENL
   [NUM_REDUCE_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM (CONJUNCT1 th)]) THEN
   MATCH_MP_TAC lt_word_size THEN
   MATCH_MP_TAC LET_TRANS THEN
   EXISTS_TAC `word_to_num w` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC DIV_LE THEN
    REWRITE_TAC [EXP_EQ_0] THEN
    NUM_REDUCE_TAC;
    REWRITE_TAC [word_to_num_bound]]);;

export_thm word_to_list_to_word;;

let word_to_list_inj = prove
  (`!w1 w2. word_to_list w1 = word_to_list w2 ==> w1 = w2`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM word_to_list_to_word] THEN
   ASM_REWRITE_TAC []);;

export_thm word_to_list_inj;;

let list_to_word_bit = prove
  (`!l n.
      word_bit (list_to_word l) n =
      (n < word_width /\ n < LENGTH l /\ EL n l)`,
   REWRITE_TAC [word_bit_div] THEN
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; nil_to_word_to_num; LT; ODD; EXP; DIV_1];
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC
      [LENGTH; cons_to_word_to_num; EXP; DIV_1; EL; HD; LT_NZ; NOT_SUC] THEN
    ASM_REWRITE_TAC [word_size_def; odd_mod_exp_2] THEN
    CONV_TAC (RATOR_CONV (ONCE_REWRITE_CONV [CONJ_SYM])) THEN
    AP_TERM_TAC THEN
    MP_TAC (SPEC `h:bool` BOOL_CASES_AX) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [GSYM ADD1; ODD_DOUBLE];
     ASM_REWRITE_TAC [ADD_0; GSYM NOT_EVEN; EVEN_DOUBLE]];
    ALL_TAC] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   bool_cases_tac' `SUC n < word_width` THENL
   [POP_ASSUM MP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [NOT_ODD] THEN
    MATCH_MP_TAC even_0 THEN
    REWRITE_TAC [div_exp_2_lt] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `word_size` THEN
    REWRITE_TAC [word_to_num_bound] THEN
    REWRITE_TAC [word_size_def; le_exp_2] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; nil_to_word_to_num; LT; NOT_ODD] THEN
    MATCH_MP_TAC even_0 THEN
    REWRITE_TAC [div_exp_2_lt; LT_NZ; exp_2_nz];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LENGTH; cons_to_word_to_num] THEN
   REWRITE_TAC [LT_SUC; EL; TL] THEN
   REWRITE_TAC [word_size_def; mod_div_exp_2; GSYM NOT_LT] THEN
   ASM_REWRITE_TAC [odd_mod_exp_2; SUB_EQ_0; GSYM NOT_LT] THEN
   FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `t : bool list` th)) THEN
   KNOW_TAC `n < word_width` THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   REWRITE_TAC [ODD_MOD] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `((2 * word_to_num (list_to_word t) + (if h then 1 else 0)) DIV 2) DIV
      (2 EXP n)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EXP] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC DIV_DIV THEN
    REWRITE_TAC [GSYM EXP; exp_2_nz];
    ALL_TAC] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC cons_div_2);;

export_thm list_to_word_bit;;

let short_list_to_word_to_list = prove
  (`!l.
      LENGTH l <= word_width ==>
      word_to_list (list_to_word l) =
      APPEND l (REPLICATE (word_width - LENGTH l) F)`,
   REWRITE_TAC [word_to_list_def; list_to_word_bit] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC nth_eq THEN
   REWRITE_TAC [LENGTH_MAP; length_interval] THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LENGTH_APPEND; LENGTH_REPLICATE] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [`word_bit (list_to_word l)`; `interval 0 word_width`;
                   `i : num`] nth_map) THEN
   COND_TAC THENL
   [ASM_REWRITE_TAC [length_interval];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (SPECL [`0`; `word_width`; `i : num`] nth_interval) THEN
   ASM_REWRITE_TAC [ADD] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [list_to_word_bit] THEN
   ASM_REWRITE_TAC [EL_APPEND] THEN
   bool_cases_tac `i < LENGTH (l : bool list)` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (ISPECL [`word_width - LENGTH (l : bool list)`; `F`;
                   `i - LENGTH (l : bool list)`] nth_replicate) THEN
   COND_TAC THENL
   [ASM_ARITH_TAC;
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm short_list_to_word_to_list;;

let long_list_to_word_to_list = prove
  (`!l.
      word_width <= LENGTH l ==>
      word_to_list (list_to_word l) = take word_width l`,
   REWRITE_TAC [word_to_list_def; list_to_word_bit] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC nth_eq THEN
   REWRITE_TAC [LENGTH_MAP; length_interval] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC length_take THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [`word_bit (list_to_word l)`; `interval 0 word_width`;
                   `i : num`] nth_map) THEN
   COND_TAC THENL
   [ASM_REWRITE_TAC [length_interval];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (SPECL [`0`; `word_width`; `i : num`] nth_interval) THEN
   ASM_REWRITE_TAC [ADD] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [list_to_word_bit] THEN
   ASM_REWRITE_TAC [] THEN
   KNOW_TAC `i < LENGTH (l : bool list)` THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC nth_take THEN
   ASM_REWRITE_TAC []);;

export_thm long_list_to_word_to_list;;

let list_to_word_to_list_eq = prove
  (`!l.
      word_to_list (list_to_word l) =
      if LENGTH l <= word_width then
        APPEND l (REPLICATE (word_width - LENGTH l) F)
      else
        take word_width l`,
   GEN_TAC THEN
   bool_cases_tac `LENGTH (l : bool list) <= word_width` THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC short_list_to_word_to_list THEN
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC long_list_to_word_to_list THEN
    ASM_ARITH_TAC]);;

export_thm list_to_word_to_list_eq;;

let list_to_word_to_list = prove
  (`!l. LENGTH l = word_width <=> word_to_list (list_to_word l) = l`,
   GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `take (LENGTH (l : bool list)) l` THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC long_list_to_word_to_list THEN
     ASM_REWRITE_TAC [LE_REFL];
     MATCH_ACCEPT_TAC take_length];
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    MATCH_ACCEPT_TAC length_word_to_list]);;

export_thm list_to_word_to_list;;

let word_shl_list = prove
  (`!l n.
      word_shl (list_to_word l) n =
      list_to_word (APPEND (REPLICATE n F) l)`,
   REWRITE_TAC [word_shl_def] THEN
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC word_to_num_inj THEN
   REWRITE_TAC [num_to_word_to_num] THEN
   SPEC_TAC (`n:num`,`n:num`) THEN
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EXP; REPLICATE; APPEND; MULT_CLAUSES] THEN
    REWRITE_TAC [GSYM num_to_word_to_num; word_to_num_to_word];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [REPLICATE; APPEND; cons_to_word_to_num; ADD_0] THEN
   POP_ASSUM (fun th -> REWRITE_TAC [GSYM th]) THEN
   MP_TAC (SPECL [`2`; `word_size`; `2 EXP n * word_to_num (list_to_word l)`]
                 MOD_MULT_RMOD) THEN
   COND_TAC THENL
   [ACCEPT_TAC word_size_nonzero;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [EXP; MULT_ASSOC]);;

export_thm word_shl_list;;

let short_word_shr_list = prove
  (`!l n.
      LENGTH l <= word_width ==>
      word_shr (list_to_word l) n =
      (if LENGTH l <= n then list_to_word []
       else list_to_word (drop n l))`,
   REWRITE_TAC [word_shr_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC word_to_num_inj THEN
   REWRITE_TAC [num_to_word_to_num] THEN
   bool_cases_tac `LENGTH (l : bool list) <= n` THENL
   [ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [nil_to_word_to_num] THEN
    MP_TAC (SPEC `word_size` MOD_0) THEN
    COND_TAC THENL
    [ACCEPT_TAC word_size_nonzero;
     ALL_TAC] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_LT THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP LENGTH (l : bool list)` THEN
    CONJ_TAC THENL
    [MATCH_ACCEPT_TAC list_to_word_to_num_bound;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [LE_EXP] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   KNOW_TAC `n <= LENGTH (l : bool list)` THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`n:num`,`n:num`) THEN
   SPEC_TAC (`l : bool list`,`l : bool list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LE; LENGTH] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [nil_to_word_to_num; drop_def] THEN
    NUM_REDUCE_TAC THEN
    MATCH_MP_TAC MOD_0 THEN
    ACCEPT_TAC word_size_nonzero;
    ALL_TAC] THEN
   GEN_TAC THEN
   MP_TAC (SPEC `n : num` num_CASES) THEN
   STRIP_TAC THENL
   [DISCH_THEN (K ALL_TAC) THEN
    DISCH_THEN (K ALL_TAC) THEN
    ASM_REWRITE_TAC [EXP; DIV_1; drop_def] THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_ACCEPT_TAC word_to_num_bound;
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [LENGTH; LE_SUC; cons_to_word_to_num; drop_def] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `n' : num` th)) THEN
   COND_TAC THENL
   [ASM_ARITH_TAC;
    ALL_TAC] THEN
   COND_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `(2 * word_to_num (list_to_word t) + (if h then 1 else 0)) DIV
      (2 EXP SUC n')` THEN
   CONJ_TAC THENL
   [AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC MOD_LT THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP SUC (LENGTH (t : bool list))` THEN
    CONJ_TAC THENL
    [MATCH_ACCEPT_TAC cons_to_word_to_num_bound;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [word_size_def; le_exp_2];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `((2 * word_to_num (list_to_word t) + (if h then 1 else 0)) DIV 2) DIV
      (2 EXP n')` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EXP] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC DIV_DIV THEN
    REWRITE_TAC [GSYM EXP; exp_2_nz];
    ALL_TAC] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC cons_div_2);;

export_thm short_word_shr_list;;

let long_word_shr_list = prove
  (`!l n.
      word_width <= LENGTH l ==>
      word_shr (list_to_word l) n =
      if word_width <= n then list_to_word []
      else list_to_word (drop n (take word_width l))`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `l : bool list` long_list_to_word_to_list) THEN
   COND_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th]) THEN
   CONV_TAC
     (LAND_CONV
        (LAND_CONV (ONCE_REWRITE_CONV [GSYM word_to_list_to_word]))) THEN
   MP_TAC (SPEC `list_to_word l` length_word_to_list) THEN
   DISCH_THEN (fun th -> REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
   MATCH_MP_TAC short_word_shr_list THEN
   ASM_REWRITE_TAC [LE_REFL]);;

export_thm long_word_shr_list;;

let word_shr_list = prove
  (`!l n.
      word_shr (list_to_word l) n =
      (if LENGTH l <= word_width then
         if LENGTH l <= n then list_to_word []
         else list_to_word (drop n l)
       else
         if word_width <= n then list_to_word []
         else list_to_word (drop n (take word_width l)))`,
   REPEAT GEN_TAC THEN
   bool_cases_tac `LENGTH (l : bool list) <= word_width` THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC short_word_shr_list THEN
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC long_word_shr_list THEN
    ASM_ARITH_TAC]);;

export_thm word_shr_list;;

let word_eq_bits = prove
  (`!w1 w2. (!i. i < word_width ==> word_bit w1 i = word_bit w2 i) ==> w1 = w2`,
   REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM word_to_list_to_word])) THEN
   REWRITE_TAC [list_to_word_bit] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC word_to_list_inj THEN
   MATCH_MP_TAC nth_eq THEN
   REWRITE_TAC [length_word_to_list] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `i : num` th)) THEN
   ASM_REWRITE_TAC [length_word_to_list]);;

export_thm word_eq_bits;;

(***
let num_to_word_list = prove
  (`(num_to_word 0 = list_to_word []) /\
    (!n. num_to_word n = list_to_word []) /\

let num_to_word_list = prove
  (`(num_to_word 0 = list_to_word []) /\
    (!n. num_to_word n = list_to_word []) /\

word_and (list_to_word []) l2 = list_to_word []) /\
    (!l1. word_and l1 (list_to_word []) = list_to_word []) /\
    (!h1 t1 h2 t2.

let word_and_list = prove
  (`(!l2. word_and (list_to_word []) l2 = list_to_word []) /\
    (!l1. word_and l1 (list_to_word []) = list_to_word []) /\
    (!h1 t1 h2 t2.
       word_and (list_to_word (CONS h1 t1)) (list_to_word (CONS h2 t2)) =
       list_to_word (CONS (h1 /\ h2) (word_to_list (word_and (list_to_word t1) (CONS h1 t1)) (list_to_word (CONS h2 t2)) =
!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;
***)

(* Apply theory functor word *)

new_type ("byte",0);;

new_constant ("byte_add", `:byte -> byte -> byte`);;
new_constant ("byte_mult", `:byte -> byte -> byte`);;
new_constant ("byte_neg", `:byte -> byte`);;
new_constant ("byte_sub", `:byte -> byte -> byte`);;
new_constant ("byte_le", `:byte -> byte -> bool`);;
new_constant ("byte_lt", `:byte -> byte -> bool`);;
new_constant ("byte_and", `:byte -> byte -> byte`);;
new_constant ("byte_bit", `:byte -> num -> bool`);;
new_constant ("list_to_byte", `:bool list -> byte`);;
new_constant ("num_to_byte", `:num -> byte`);;
new_constant ("byte_not", `:byte -> byte`);;
new_constant ("byte_or", `:byte -> byte -> byte`);;
new_constant ("byte_shl", `:byte -> num -> byte`);;
new_constant ("byte_shr", `:byte -> num -> byte`);;
new_constant ("byte_size", `:num`);;
new_constant ("byte_to_list", `:byte -> bool list`);;
new_constant ("byte_to_num", `:byte -> num`);;

let byte_size_def = new_axiom
  `byte_size = 2 EXP byte_width`;;

let byte_size_nonzero = new_axiom
  `~(byte_size = 0)`;;

let byte_to_num_to_byte = new_axiom
  `!x. num_to_byte (byte_to_num x) = x`;;

let num_to_byte_inj = new_axiom
  `!x y. x < byte_size /\ y < byte_size /\ num_to_byte x = num_to_byte y ==> x = y`;;

let num_to_byte_to_num = new_axiom
  `!x. byte_to_num (num_to_byte x) = x MOD byte_size`;;

let num_to_byte_add = new_axiom
  `!x1 y1. num_to_byte (x1 + y1) = byte_add (num_to_byte x1) (num_to_byte y1)`;;

let num_to_byte_mult = new_axiom
  `!x1 y1. num_to_byte (x1 * y1) = byte_mult (num_to_byte x1) (num_to_byte y1)`;;

let byte_neg_def = new_axiom
  `!x. byte_neg x = num_to_byte (byte_size - byte_to_num x)`;;

let byte_sub_def = new_axiom
  `!x y. byte_sub x y = byte_add x (byte_neg y)`;;

let byte_le_def = new_axiom
  `!x y. byte_le x y = byte_to_num x <= byte_to_num y`;;

let byte_lt_def = new_axiom
  `!x y. byte_lt x y = ~(byte_le y x)`;;

let byte_to_num_inj = new_axiom
  `!x y. byte_to_num x = byte_to_num y ==> x = y`;;

let num_to_byte_eq = new_axiom
  `!x y. num_to_byte x = num_to_byte y <=> x MOD byte_size = y MOD byte_size`;;

let byte_to_num_bound = new_axiom
  `!x. byte_to_num x < byte_size`;;

let byte_shl_def = new_axiom
 `!w n. byte_shl w n = num_to_byte (byte_to_num w * (2 EXP n))`;;

let byte_shr_def = new_axiom
 `!w n. byte_shr w n = num_to_byte (byte_to_num w DIV (2 EXP n))`;;

let byte_bit_def = new_axiom
 `!w n. byte_bit w n = ODD (byte_to_num (byte_shr w n))`;;

let byte_to_list_def = new_axiom
 `!w. byte_to_list w = MAP (byte_bit w) (interval 0 byte_width)`;;

let list_to_byte_def = new_axiom
  `(list_to_byte [] = num_to_byte 0) /\
   (!h t.
      list_to_byte (CONS h t) =
      if h then byte_add (byte_shl (list_to_byte t) 1) (num_to_byte 1)
      else byte_shl (list_to_byte t) 1)`;;

let byte_and_def = new_axiom
  `!w1 w2.
     byte_and w1 w2 =
     list_to_byte (zipwith ( /\ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_or_def = new_axiom
  `!w1 w2.
     byte_or w1 w2 =
     list_to_byte (zipwith ( \/ ) (byte_to_list w1) (byte_to_list w2))`;;

let byte_not_def = new_axiom
  `!w. byte_not w = list_to_byte (MAP (~) (byte_to_list w))`;;

(* A reduction conversion *)

let byte_reduce_conv =
    REWRITE_CONV
      [byte_to_num_to_byte;
       byte_le_def; byte_lt_def] THENC
    REWRITE_CONV
      [num_to_byte_to_num] THENC
    REWRITE_CONV
      [byte_width_def; byte_size_def; num_to_byte_eq] THENC
    NUM_REDUCE_CONV;;

logfile_end ();;

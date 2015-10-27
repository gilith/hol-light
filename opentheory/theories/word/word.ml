(* ========================================================================= *)
(* PARAMETRIC THEORY OF WORDS                                                *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base";
   "probability";
   "natural-bits";
   "natural-divides"];;

needs "opentheory/theories/tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/word/word.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness.                                                *)
(* ------------------------------------------------------------------------- *)

export_theory "word-witness";;

let () =
  let _ = new_definition `word_width = 0` in
  export_thm (REFL `word_width`);;

(* ------------------------------------------------------------------------- *)
(* Definition of word operations.                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

export_thm word_size_def;;

let word_size_nonzero = prove
 (`~(word_size = 0)`,
  REWRITE_TAC [word_size_def; EXP_EQ_0] THEN
  NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

(* Interpret parametric theory *)

interpret_theory
  {Import.source_theory = "modular";
   Import.interpretation = "opentheory/theories/word/word-def-modular.int";
   Import.theorem_renamer = Import.replace "modular" "word" o
                            Import.replace "modulus" "word_size";
   Import.destination_theory = "word-def"};;

(* ------------------------------------------------------------------------- *)
(* Definition of word to bit-list conversions.                               *)
(* ------------------------------------------------------------------------- *)

export_theory "word-bits-def";;

let word_shl_def = new_definition
  `!w n. word_shl w n = num_to_word (bit_shl (word_to_num w) n)`;;

export_thm word_shl_def;;

let word_shr_def = new_definition
  `!w n. word_shr w n = num_to_word (bit_shr (word_to_num w) n)`;;

export_thm word_shr_def;;

let word_bit_def = new_definition
  `!w n. word_bit w n = bit_nth (word_to_num w) n`;;

export_thm word_bit_def;;

let word_to_list_def = new_definition
  `!w. word_to_list w = num_to_bitvec (word_to_num w) word_width`;;

export_thm word_to_list_def;;

let list_to_word_def = new_definition
  `!l. list_to_word l = num_to_word (bits_to_num l)`;;

export_thm list_to_word_def;;

let is_word_list_def = new_definition
  `!l. is_word_list (l : bool list) <=> LENGTH l = word_width`;;

export_thm is_word_list_def;;

let word_and_def = new_definition
  `!w1 w2.
      word_and w1 w2 =
      num_to_word (bit_and (word_to_num w1) (word_to_num w2))`;;

export_thm word_and_def;;

let word_or_def = new_definition
  `!w1 w2.
      word_or w1 w2 =
      num_to_word (bit_or (word_to_num w1) (word_to_num w2))`;;

export_thm word_or_def;;

let word_not_def = new_definition
  `!w. word_not w = list_to_word (MAP (~) (word_to_list w))`;;

export_thm word_not_def;;

let (word_bits_lte_nil,word_bits_lte_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!q l. word_bits_lte q [] l = q) /\
     (!q h t l.
        word_bits_lte q (CONS h t) l =
        word_bits_lte ((~h /\ HD l) \/ (~(h /\ ~HD l) /\ q)) t (TL l))` in
  let wnil = prove
    (`!q. word_bits_lte q [] [] = q`,
     REWRITE_TAC [def])
  and wcons = prove
    (`!q h1 h2 t1 t2.
        word_bits_lte q (CONS h1 t1) (CONS h2 t2) =
        word_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`,
     REWRITE_TAC [def; HD; TL]) in
  (wnil,wcons);;

export_thm word_bits_lte_nil;;
export_thm word_bits_lte_cons;;

(* ------------------------------------------------------------------------- *)
(* Properties of word to bit-list conversions.                               *)
(* ------------------------------------------------------------------------- *)

export_theory "word-bits-thm";;

let length_word_to_list = prove
 (`!w. LENGTH (word_to_list w) = word_width`,
  REWRITE_TAC [word_to_list_def; length_num_to_bitvec]);;

export_thm length_word_to_list;;

let is_word_to_list = prove
 (`!w. is_word_list (word_to_list w)`,
  REWRITE_TAC [is_word_list_def; length_word_to_list]);;

export_thm is_word_to_list;;

let list_to_word_nil = prove
 (`list_to_word [] = num_to_word 0`,
  REWRITE_TAC [bits_to_num_nil; list_to_word_def]);;

export_thm list_to_word_nil;;

let list_to_word_cons = prove
 (`!h t.
     list_to_word (CONS h t) =
     if h then word_add (num_to_word 1) (word_shl (list_to_word t) 1)
     else word_shl (list_to_word t) 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [list_to_word_def; word_shl_def; bits_to_num_cons; bit_cons_def;
     bit_to_num_def; num_to_word_add; num_to_word_mult; bit_shl_one;
     word_to_num_to_word] THEN
  BOOL_CASES_TAC `h : bool` THEN
  REWRITE_TAC [word_add_left_zero]);;

export_thm list_to_word_cons;;

let bit_bound_word_to_num = prove
 (`!w. bit_bound (word_to_num w) word_width = word_to_num w`,
  REWRITE_TAC [bit_bound_def; GSYM word_size_def; word_to_num_mod_bound]);;

export_thm bit_bound_word_to_num;;

let num_to_word_to_num_bit_bound = prove
 (`!n. word_to_num (num_to_word n) = bit_bound n word_width`,
  REWRITE_TAC [num_to_word_to_num; bit_bound_def; word_size_def]);;

export_thm num_to_word_to_num_bit_bound;;

let nil_to_word_to_num = prove
 (`word_to_num (list_to_word []) = 0`,
  REWRITE_TAC
    [list_to_word_nil; num_to_word_to_num_bit_bound; zero_bit_bound]);;

export_thm nil_to_word_to_num;;

let list_to_word_to_num_bound = prove
 (`!l. word_to_num (list_to_word l) < 2 EXP (LENGTH l)`,
  GEN_TAC THEN
  REWRITE_TAC [list_to_word_def; num_to_word_to_num_bit_bound] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `bits_to_num l` THEN
  REWRITE_TAC [bits_to_num_bound; bit_bound_le]);;

export_thm list_to_word_to_num_bound;;

let bit_width_word_to_num = prove
 (`!w. bit_width (word_to_num w) <= word_width`,
  REWRITE_TAC [bit_width_upper_bound; GSYM word_size_def; word_to_num_bound]);;

export_thm bit_width_word_to_num;;

let word_to_list_to_num = prove
 (`!w. bits_to_num (word_to_list w) = word_to_num w`,
  REWRITE_TAC
    [word_to_list_def; num_to_bitvec_to_num; bit_bound_id;
     bit_width_word_to_num]);;

export_thm word_to_list_to_num;;

let word_to_list_to_word = prove
 (`!w. list_to_word (word_to_list w) = w`,
  REWRITE_TAC
    [word_to_list_def; list_to_word_def; num_to_bitvec_to_num;
     bit_bound_word_to_num; word_to_num_to_word]);;

export_thm word_to_list_to_word;;

let word_to_list_inj = prove
 (`!w1 w2. word_to_list w1 = word_to_list w2 ==> w1 = w2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM word_to_list_to_word] THEN
  ASM_REWRITE_TAC []);;

export_thm word_to_list_inj;;

let word_to_list_inj_eq = prove
 (`!w1 w2. word_to_list w1 = word_to_list w2 <=> w1 = w2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC word_to_list_inj;
   DISCH_THEN SUBST_VAR_TAC THEN
   REFL_TAC]);;

export_thm word_to_list_inj_eq;;

let list_to_word_bit = prove
 (`!l n.
     word_bit (list_to_word l) n =
     (n < word_width /\ n < LENGTH l /\ nth l n)`,
  REWRITE_TAC
    [word_bit_def; list_to_word_def; num_to_word_to_num_bit_bound;
     bit_nth_bound; bit_nth_bits_to_num]);;

export_thm list_to_word_bit;;

let word_bit_and = prove
 (`!k w1 w2. word_bit (word_and w1 w2) k <=> word_bit w1 k /\ word_bit w2 k`,
  REPEAT GEN_TAC THEN
  (CONV_TAC o RAND_CONV o LAND_CONV o LAND_CONV o REWR_CONV)
    (GSYM word_to_num_to_word) THEN
  REWRITE_TAC
    [word_bit_def; word_and_def; num_to_word_to_num_bit_bound;
     bit_nth_bound; bit_nth_and; CONJ_ASSOC]);;

export_thm word_bit_and;;

let word_and_list = prove
 (`!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM word_to_num_to_word))) THEN
  REWRITE_TAC
    [word_and_def; word_to_list_def; GSYM num_to_bitvec_bit_and;
     list_to_word_def; num_to_word_to_num_bit_bound;
     num_to_bitvec_to_num]);;

export_thm word_and_list;;

let word_bit_or = prove
 (`!k w1 w2. word_bit (word_or w1 w2) k <=> word_bit w1 k \/ word_bit w2 k`,
  REPEAT GEN_TAC THEN
  (CONV_TAC o RAND_CONV o LAND_CONV o LAND_CONV o REWR_CONV)
    (GSYM word_to_num_to_word) THEN
  (CONV_TAC o RAND_CONV o RAND_CONV o LAND_CONV o REWR_CONV)
    (GSYM word_to_num_to_word) THEN
  REWRITE_TAC
    [word_bit_def; word_or_def; num_to_word_to_num_bit_bound;
     bit_nth_bound; bit_nth_or; LEFT_OR_DISTRIB]);;

export_thm word_bit_or;;

let word_or_list = prove
 (`!w1 w2.
     word_or w1 w2 =
     list_to_word (zipwith ( \/ ) (word_to_list w1) (word_to_list w2))`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM word_to_num_to_word))) THEN
  REWRITE_TAC
    [word_or_def; word_to_list_def; GSYM num_to_bitvec_bit_or;
     list_to_word_def; num_to_word_to_num_bit_bound;
     num_to_bitvec_to_num]);;

export_thm word_or_list;;

let word_bit_not = prove
 (`!k w. word_bit (word_not w) k <=> k < word_width /\ ~word_bit w k`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM word_to_list_to_word])) THEN
  REWRITE_TAC
    [word_not_def; list_to_word_bit; LENGTH_MAP; length_word_to_list] THEN
  REVERSE_TAC (ASM_CASES_TAC `k < word_width`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC nth_map THEN
  ASM_REWRITE_TAC [length_word_to_list]);;

export_thm word_bit_not;;

let list_to_word_to_list_eq = prove
 (`!l.
     word_to_list (list_to_word l) =
     if LENGTH l <= word_width then
       APPEND l (REPLICATE F (word_width - LENGTH l))
     else
       take word_width l`,
  REWRITE_TAC
    [word_to_list_def; list_to_word_def; num_to_word_to_num_bit_bound;
     num_to_bitvec_bound; bits_to_num_to_bitvec]);;

export_thm list_to_word_to_list_eq;;

let list_to_word_to_list = prove
 (`!l. is_word_list l <=> word_to_list (list_to_word l) = l`,
  GEN_TAC THEN
  REWRITE_TAC [is_word_list_def] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC
     [list_to_word_to_list_eq; LE_REFL; SUB_REFL; REPLICATE; APPEND_NIL];
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   MATCH_ACCEPT_TAC length_word_to_list]);;

export_thm list_to_word_to_list;;

let word_shl_list = prove
 (`!l n.
     word_shl (list_to_word l) n =
     list_to_word (APPEND (REPLICATE F n) l)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC word_to_num_inj THEN
  REWRITE_TAC
    [word_shl_def; list_to_word_def; num_to_word_to_num_bit_bound;
     bits_to_num_append; LENGTH_REPLICATE; bits_to_num_replicate_false;
     ZERO_ADD; GSYM bit_bound_shl_add; bit_bound_bound_min] THEN
  ONCE_REWRITE_TAC [MIN_COMM] THEN
  REWRITE_TAC [MIN; LE_ADD]);;

export_thm word_shl_list;;

let short_word_shr_list = prove
 (`!l n.
     LENGTH l <= word_width ==>
     word_shr (list_to_word l) n =
     (if LENGTH l <= n then list_to_word []
      else list_to_word (drop n l))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC word_to_num_inj THEN
  REWRITE_TAC [word_shr_def; list_to_word_def; bits_to_num_nil] THEN
  REWRITE_TAC
    [bit_bound_bound_min; MIN; LE_ADD; GSYM COND_RAND; GSYM bit_shr_bound_add;
     GSYM bit_shr_bits_to_num; num_to_word_to_num_bit_bound] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  SUBGOAL_THEN
    `bit_bound (bits_to_num l) word_width = bits_to_num l`
    (CONV_TAC o RAND_CONV o LAND_CONV o REWR_CONV o SYM) THENL
  [REWRITE_TAC [bit_bound_id] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (l : bool list)` THEN
   ASM_REWRITE_TAC [bit_width_bits_to_num];
   ALL_TAC] THEN
  REWRITE_TAC [bit_bound_bound_min; MIN; LE_ADD]);;

export_thm short_word_shr_list;;

let long_word_shr_list = prove
 (`!l n.
     word_width <= LENGTH l ==>
     word_shr (list_to_word l) n =
     if word_width <= n then list_to_word []
     else list_to_word (drop n (take word_width l))`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `LENGTH (l : bool list) = word_width` THENL
  [FIRST_ASSUM (fun th -> REWRITE_TAC [GSYM th; take_length]) THEN
   MATCH_MP_TAC short_word_shr_list THEN
   ASM_REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM word_to_list_to_word)))) THEN
  ASM_REWRITE_TAC [list_to_word_to_list_eq] THEN
  COND_CASES_TAC THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `~(LENGTH (l : bool list) = word_width)` THEN
   ASM_REWRITE_TAC [GSYM LE_ANTISYM];
   ALL_TAC] THEN
  MP_TAC
    (SPECL [`take word_width l : bool list`; `n : num`]
       short_word_shr_list) THEN
  MP_TAC (ISPECL [`word_width`; `l : bool list`] length_take) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [LE_REFL]);;

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
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM NOT_LE]]);;

export_thm word_shr_list;;

let word_eq_bits = prove
 (`!w1 w2.
     (!i. i < word_width ==> word_bit w1 i = word_bit w2 i) ==> w1 = w2`,
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

let word_lte_cmp = prove
 (`!q l1 l2.
     LENGTH l1 = LENGTH l2 ==>
     word_bits_lte q l1 l2 = bit_cmp q (bits_to_num l1) (bits_to_num l2)`,
  CONV_TAC (REWR_CONV SWAP_FORALL_THM) THEN
  LIST_INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
   REWRITE_TAC [LENGTH; LENGTH_EQ_NIL] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [word_bits_lte_nil; bits_to_num_nil; zero_bit_cmp];
   ALL_TAC] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; NOT_SUC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [LENGTH; SUC_INJ] THEN
  STRIP_TAC THEN
  REWRITE_TAC [word_bits_lte_cons; bits_to_num_cons; bit_cmp_cons] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm word_lte_cmp;;

let word_lte_list = prove
 (`!q w1 w2.
     word_bits_lte q (word_to_list w1) (word_to_list w2) <=>
     (if q then word_le w1 w2 else word_lt w1 w2)`,
  REPEAT GEN_TAC THEN
  MP_TAC
    (SPECL [`q : bool`; `word_to_list w1`; `word_to_list w2`]
       word_lte_cmp) THEN
  REWRITE_TAC [length_word_to_list] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [bit_cmp_def; word_le_def; word_lt_def; word_to_list_to_num]);;

export_thm word_lte_list;;

let word_le_list = prove
 (`!w1 w2.
     word_bits_lte T (word_to_list w1) (word_to_list w2) <=> word_le w1 w2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`T`; `w1 : word`; `w2 : word`] word_lte_list) THEN
  REWRITE_TAC []);;

export_thm word_le_list;;

let word_lt_list = prove
 (`!w1 w2.
     word_bits_lte F (word_to_list w1) (word_to_list w2) <=> word_lt w1 w2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`F`; `w1 : word`; `w2 : word`] word_lte_list) THEN
  REWRITE_TAC []);;

export_thm word_lt_list;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "word-hol-light-thm";;

export_theory_thm_names "word"
  ["word-def";
   "word-bits-def";
   "word-bits-thm"];;

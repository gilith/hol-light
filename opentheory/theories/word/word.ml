(* ========================================================================= *)
(* PARAMETRIC THEORY OF WORDS                                                *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for a parametric theory of words.                         *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/word/word.int";;

(* ------------------------------------------------------------------------- *)
(* Parametric theory witness for words.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "word-witness";;

let () =
  let _ = new_definition `word_width = 0` in
  export_thm (REFL `word_width`);;

(* ------------------------------------------------------------------------- *)
(* Definition of word operations.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

(*PARAMETRIC
new_constant ("word_size", `:num`);;
*)

export_thm word_size_def;;

(*PARAMETRIC
let word_size_def = new_axiom
  `word_size = 2 EXP word_width`;;
*)

let word_size_nonzero = prove
 (`~(word_size = 0)`,
  REWRITE_TAC [word_size_def; EXP_EQ_0] THEN
  NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

(*PARAMETRIC
let word_size_nonzero = new_axiom
  `~(word_size = 0)`;;
*)

(* Parametric theory instantiation: modular *)

loads "opentheory/theories/word/word-modular.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of word to bit-list conversions.                               *)
(* ------------------------------------------------------------------------- *)

logfile "word-bits-def";;

let word_shl_def = new_definition
  `!w n. word_shl w n = num_to_word (bit_shl (word_to_num w) n)`;;

(*PARAMETRIC
new_constant ("word_shl", `:word -> num -> word`);;
*)

export_thm word_shl_def;;

(*PARAMETRIC
let word_shl_def = new_axiom
  `!w n. word_shl w n = num_to_word (bit_shl (word_to_num w) n)`;;
*)

let word_shr_def = new_definition
  `!w n. word_shr w n = num_to_word (bit_shr (word_to_num w) n)`;;

(*PARAMETRIC
new_constant ("word_shr", `:word -> num -> word`);;
*)

export_thm word_shr_def;;

(*PARAMETRIC
let word_shr_def = new_axiom
  `!w n. word_shr w n = num_to_word (bit_shr (word_to_num w) n)`;;
*)

let word_bit_def = new_definition
  `!w n. word_bit w n = bit_nth (word_to_num w) n`;;

(*PARAMETRIC
new_constant ("word_bit", `:word -> num -> bool`);;
*)

export_thm word_bit_def;;

(*PARAMETRIC
let word_bit_def = new_axiom
  `!w n. word_bit w n = bit_nth (word_to_num w) n`;;
*)

let word_to_list_def = new_definition
  `!w. word_to_list w = num_to_bitvec (word_to_num w) word_width`;;

(*PARAMETRIC
new_constant ("word_to_list", `:word -> bool list`);;
*)

export_thm word_to_list_def;;

(*PARAMETRIC
let word_to_list_def = new_axiom
  `!w. word_to_list w = num_to_bitvec (word_to_num w) word_width`;;
*)

let list_to_word_def = new_definition
  `!l. list_to_word l = num_to_word (bits_to_num l)`;;

(*PARAMETRIC
new_constant ("list_to_word", `:bool list -> word`);;
*)

export_thm list_to_word_def;;

(*PARAMETRIC
let list_to_word_def = new_axiom
  `!l. list_to_word l = num_to_word (bits_to_num l)`;;
*)

let is_word_list_def = new_definition
  `!l. is_word_list (l : bool list) <=> LENGTH l = word_width`;;

(*PARAMETRIC
new_constant ("is_word_list", `:bool list -> bool`);;
*)

export_thm is_word_list_def;;

(*PARAMETRIC
let is_word_list_def = new_axiom
  `!l. is_word_list (l : bool list) <=> LENGTH l = word_width`;;
*)

let word_and_def = new_definition
  `!w1 w2.
      word_and w1 w2 =
      num_to_word (bit_and (word_to_num w1) (word_to_num w2))`;;

(*PARAMETRIC
new_constant ("word_and", `:word -> word -> word`);;
*)

export_thm word_and_def;;

(*PARAMETRIC
let word_and_def = new_axiom
  `!w1 w2.
      word_and w1 w2 =
      num_to_word (bit_and (word_to_num w1) (word_to_num w2))`;;
*)

let word_or_def = new_definition
  `!w1 w2.
      word_or w1 w2 =
      num_to_word (bit_or (word_to_num w1) (word_to_num w2))`;;

(*PARAMETRIC
new_constant ("word_or", `:word -> word -> word`);;
*)

export_thm word_or_def;;

(*PARAMETRIC
let word_or_def = new_axiom
  `!w1 w2.
      word_or w1 w2 =
      num_to_word (bit_or (word_to_num w1) (word_to_num w2))`;;
*)

let word_not_def = new_definition
  `!w. word_not w = list_to_word (MAP (~) (word_to_list w))`;;

(*PARAMETRIC
new_constant ("word_not", `:word -> word`);;
*)

export_thm word_not_def;;

(*PARAMETRIC
let word_not_def = new_axiom
  `!w. word_not w = list_to_word (MAP (~) (word_to_list w))`;;
*)

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

(*PARAMETRIC
new_constant ("word_bits_lte", `:bool -> bool list -> bool list -> bool`);;
*)

export_thm word_bits_lte_nil;;
export_thm word_bits_lte_cons;;

(*PARAMETRIC
let word_bits_lte_nil = new_axiom
   `!q. word_bits_lte q [] [] = q`
and word_bits_lte_cons = new_axiom
   `!q h1 h2 t1 t2.
      word_bits_lte q (CONS h1 t1) (CONS h2 t2) =
      word_bits_lte ((~h1 /\ h2) \/ (~(h1 /\ ~h2) /\ q)) t1 t2`;;
*)

(*BEGIN-PARAMETRIC*)
let word_bits_lte_def = CONJ word_bits_lte_nil word_bits_lte_cons;;
(*END-PARAMETRIC*)

(* ------------------------------------------------------------------------- *)
(* Properties of word to bit-list conversions.                               *)
(* ------------------------------------------------------------------------- *)

logfile "word-bits-thm";;

let length_word_to_list = prove
 (`!w. LENGTH (word_to_list w) = word_width`,
  REWRITE_TAC [word_to_list_def; length_num_to_bitvec]);;

export_thm length_word_to_list;;

(*PARAMETRIC
let length_word_to_list = new_axiom
  `!w. LENGTH (word_to_list w) = word_width`;;
*)

let is_word_to_list = prove
 (`!w. is_word_list (word_to_list w)`,
  REWRITE_TAC [is_word_list_def; length_word_to_list]);;

export_thm is_word_to_list;;

(*PARAMETRIC
let is_word_to_list = new_axiom
  `!w. is_word_list (word_to_list w)`;;
*)

let list_to_word_nil = prove
 (`list_to_word [] = num_to_word 0`,
  REWRITE_TAC [bits_to_num_nil; list_to_word_def]);;

export_thm list_to_word_nil;;

(*PARAMETRIC
let list_to_word_nil = new_axiom
   `list_to_word [] = num_to_word 0`;;
*)

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

(*PARAMETRIC
let list_to_word_cons = new_axiom
   `!h t.
      list_to_word (CONS h t) =
      if h then word_add (num_to_word 1) (word_shl (list_to_word t) 1)
      else word_shl (list_to_word t) 1`;;
*)

let bit_bound_word_to_num = prove
 (`!w. bit_bound (word_to_num w) word_width = word_to_num w`,
  REWRITE_TAC [bit_bound_def; GSYM word_size_def; word_to_num_mod_bound]);;

export_thm bit_bound_word_to_num;;

(*PARAMETRIC
let bit_bound_word_to_num = new_axiom
  `!w. bit_bound (word_to_num w) word_width = word_to_num w`;;
*)

let num_to_word_to_num_bit_bound = prove
 (`!n. word_to_num (num_to_word n) = bit_bound n word_width`,
  REWRITE_TAC [num_to_word_to_num; bit_bound_def; word_size_def]);;

export_thm num_to_word_to_num_bit_bound;;

(*PARAMETRIC
let num_to_word_to_num_bit_bound = new_axiom
  `!n. word_to_num (num_to_word n) = bit_bound n word_width`;;
*)

let nil_to_word_to_num = prove
 (`word_to_num (list_to_word []) = 0`,
  REWRITE_TAC [list_to_word_nil; num_to_word_to_num_bit_bound; zero_bit_bound]);;

export_thm nil_to_word_to_num;;

(*PARAMETRIC
let nil_to_word_to_num = new_axiom
  `word_to_num (list_to_word []) = 0`;;
*)

let list_to_word_to_num_bound = prove
 (`!l. word_to_num (list_to_word l) < 2 EXP (LENGTH l)`,
  GEN_TAC THEN
  REWRITE_TAC [list_to_word_def; num_to_word_to_num_bit_bound] THEN
  MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `bits_to_num l` THEN
  REWRITE_TAC [bits_to_num_bound; bit_bound_le]);;

export_thm list_to_word_to_num_bound;;

(*PARAMETRIC
let list_to_word_to_num_bound = new_axiom
  `!l. word_to_num (list_to_word l) < 2 EXP (LENGTH l)`;;
*)

let bit_width_word_to_num = prove
 (`!w. bit_width (word_to_num w) <= word_width`,
  REWRITE_TAC [bit_width_upper_bound; GSYM word_size_def; word_to_num_bound]);;

export_thm bit_width_word_to_num;;

(*PARAMETRIC
let bit_width_word_to_num = new_axiom
  `!w. bit_width (word_to_num w) <= word_width`;;
*)

let word_to_list_to_num = prove
 (`!w. bits_to_num (word_to_list w) = word_to_num w`,
  REWRITE_TAC
    [word_to_list_def; num_to_bitvec_to_num; bit_bound_id;
     bit_width_word_to_num]);;

export_thm word_to_list_to_num;;

(*PARAMETRIC
let word_to_list_to_num = new_axiom
  `!w. bits_to_num (word_to_list w) = word_to_num w`;;
*)

let word_to_list_to_word = prove
 (`!w. list_to_word (word_to_list w) = w`,
  REWRITE_TAC
    [word_to_list_def; list_to_word_def; num_to_bitvec_to_num;
     bit_bound_word_to_num; word_to_num_to_word]);;

export_thm word_to_list_to_word;;

(*PARAMETRIC
let word_to_list_to_word = new_axiom
  `!w. list_to_word (word_to_list w) = w`;;
*)

let word_to_list_inj = prove
 (`!w1 w2. word_to_list w1 = word_to_list w2 ==> w1 = w2`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM word_to_list_to_word] THEN
  ASM_REWRITE_TAC []);;

export_thm word_to_list_inj;;

(*PARAMETRIC
let word_to_list_inj = new_axiom
  `!w1 w2. word_to_list w1 = word_to_list w2 ==> w1 = w2`;;
*)

let word_to_list_inj_eq = prove
 (`!w1 w2. word_to_list w1 = word_to_list w2 <=> w1 = w2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC word_to_list_inj;
   DISCH_THEN SUBST_VAR_TAC THEN
   REFL_TAC]);;

export_thm word_to_list_inj_eq;;

(*PARAMETRIC
let word_to_list_inj_eq = new_axiom
  `!w1 w2. word_to_list w1 = word_to_list w2 <=> w1 = w2`;;
*)

let list_to_word_bit = prove
 (`!l n.
     word_bit (list_to_word l) n =
     (n < word_width /\ n < LENGTH l /\ nth l n)`,
  REWRITE_TAC
    [word_bit_def; list_to_word_def; num_to_word_to_num_bit_bound;
     bit_nth_bound; bit_nth_bits_to_num]);;

export_thm list_to_word_bit;;

(*PARAMETRIC
let list_to_word_bit = new_axiom
  `!l n.
     word_bit (list_to_word l) n =
     (n < word_width /\ n < LENGTH l /\ nth l n)`;;
*)

let word_bit_and = prove
 (`!k w1 w2. word_bit (word_and w1 w2) k <=> word_bit w1 k /\ word_bit w2 k`,
  REPEAT GEN_TAC THEN
  (CONV_TAC o RAND_CONV o LAND_CONV o LAND_CONV o REWR_CONV)
    (GSYM word_to_num_to_word) THEN
  REWRITE_TAC
    [word_bit_def; word_and_def; num_to_word_to_num_bit_bound;
     bit_nth_bound; bit_nth_and; CONJ_ASSOC]);;

export_thm word_bit_and;;

(*PARAMETRIC
let word_bit_and = new_axiom
  `!k w1 w2. word_bit (word_and w1 w2) k <=> word_bit w1 k /\ word_bit w2 k`;;
*)

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

(*PARAMETRIC
let word_and_list = new_axiom
  `!w1 w2.
     word_and w1 w2 =
     list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;
*)

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

(*PARAMETRIC
let word_bit_or = new_axiom
  `!k w1 w2. word_bit (word_or w1 w2) k <=> word_bit w1 k \/ word_bit w2 k`;;
*)

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

(*PARAMETRIC
let word_or_list = new_axiom
  `!w1 w2.
     word_or w1 w2 =
     list_to_word (zipwith ( \/ ) (word_to_list w1) (word_to_list w2))`;;
*)

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

(*PARAMETRIC
let word_bit_not = new_axiom
  `!k w. word_bit (word_not w) k <=> k < word_width /\ ~word_bit w k`;;
*)

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

(*PARAMETRIC
let list_to_word_to_list_eq = new_axiom
  `!l.
     word_to_list (list_to_word l) =
     if LENGTH l <= word_width then
       APPEND l (REPLICATE F (word_width - LENGTH l))
     else
       take word_width l`;;
*)

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

(*PARAMETRIC
let list_to_word_to_list = new_axiom
  `!l. LENGTH l = word_width <=> word_to_list (list_to_word l) = l`;;
*)

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

(*PARAMETRIC
let word_shl_list = new_axiom
  `!l n.
     word_shl (list_to_word l) n =
     list_to_word (APPEND (REPLICATE F n) l)`;;
*)

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

(*PARAMETRIC
let short_word_shr_list = new_axiom
  `!l n.
     LENGTH l <= word_width ==>
     word_shr (list_to_word l) n =
     (if LENGTH l <= n then list_to_word []
      else list_to_word (drop n l))`;;
*)

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

(*PARAMETRIC
let long_word_shr_list = new_axiom
  `!l n.
     word_width <= LENGTH l ==>
     word_shr (list_to_word l) n =
     if word_width <= n then list_to_word []
     else list_to_word (drop n (take word_width l))`;;
*)

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

(*PARAMETRIC
let word_shr_list = new_axiom
  `!l n.
     word_shr (list_to_word l) n =
     (if LENGTH l <= word_width then
        if LENGTH l <= n then list_to_word []
        else list_to_word (drop n l)
      else
        if word_width <= n then list_to_word []
        else list_to_word (drop n (take word_width l)))`;;
*)

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

(*PARAMETRIC
let word_eq_bits = new_axiom
  `!w1 w2.
     (!i. i < word_width ==> word_bit w1 i = word_bit w2 i) ==> w1 = w2`;;
*)

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

(*PARAMETRIC
let word_lte_cmp = new_axiom
  `!q l1 l2.
     LENGTH l1 = LENGTH l2 ==>
     word_bits_lte q l1 l2 = bit_cmp q (bits_to_num l1) (bits_to_num l2)`;;
*)

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

(*PARAMETRIC
let word_lte_list = new_axiom
  `!q w1 w2.
     word_bits_lte q (word_to_list w1) (word_to_list w2) <=>
     (if q then word_le w1 w2 else word_lt w1 w2)`;;
*)

let word_le_list = prove
 (`!w1 w2.
     word_bits_lte T (word_to_list w1) (word_to_list w2) <=> word_le w1 w2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`T`; `w1 : word`; `w2 : word`] word_lte_list) THEN
  REWRITE_TAC []);;

export_thm word_le_list;;

(*PARAMETRIC
let word_le_list = new_axiom
  `!w1 w2.
     word_bits_lte T (word_to_list w1) (word_to_list w2) <=> word_le w1 w2`;;
*)

let word_lt_list = prove
 (`!w1 w2.
     word_bits_lte F (word_to_list w1) (word_to_list w2) <=> word_lt w1 w2`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`F`; `w1 : word`; `w2 : word`] word_lte_list) THEN
  REWRITE_TAC []);;

export_thm word_lt_list;;

(*PARAMETRIC
let word_lt_list = new_axiom
  `!w1 w2.
     word_bits_lte F (word_to_list w1) (word_to_list w2) <=> word_lt w1 w2`;;
*)

(* ------------------------------------------------------------------------- *)
(* Proof tools for words after width parameter is instantiated to a numeral. *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
let word_reduce_conv =
  REWRITE_CONV
    [word_to_num_to_word;
     word_le_def; word_lt_def] THENC
  REWRITE_CONV
    [num_to_word_to_num] THENC
  REWRITE_CONV
    [word_width_def; word_size_def; num_to_word_eq] THENC
  NUM_REDUCE_CONV;;

let word_width_conv = REWR_CONV word_width_def;;

let list_to_word_to_list_conv =
  REWR_CONV list_to_word_to_list_eq THENC
  cond_conv
    (LAND_CONV length_conv THENC
     RAND_CONV word_width_conv THENC
     NUM_REDUCE_CONV)
    (RAND_CONV
       (RAND_CONV
          (LAND_CONV word_width_conv THENC
           RAND_CONV length_conv THENC
           NUM_REDUCE_CONV) THENC
        replicate_conv) THENC
     append_conv)
    (LAND_CONV word_width_conv THENC
     take_conv);;

let numeral_to_word_list_conv =
  let list_to_word_conv = REWR_CONV (GSYM list_to_word_def) in
  RAND_CONV numeral_to_bits_conv THENC
  list_to_word_conv;;

let word_and_list_conv =
  let th = SPECL [`list_to_word l1`; `list_to_word l2`] word_and_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_word_to_list_conv THENC
     RAND_CONV list_to_word_to_list_conv THENC
     zipwith_conv and_simp_conv);;

let word_or_list_conv =
  let th = SPECL [`list_to_word l1`; `list_to_word l2`] word_or_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV list_to_word_to_list_conv THENC
     RAND_CONV list_to_word_to_list_conv THENC
     zipwith_conv or_simp_conv);;

let word_shr_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] word_shr_list in
  REWR_CONV th THENC
  cond_conv
    (RATOR_CONV (RAND_CONV length_conv) THENC
     RAND_CONV word_width_conv THENC
     NUM_REDUCE_CONV)
    (cond_conv
      (RATOR_CONV (RAND_CONV length_conv) THENC
       NUM_REDUCE_CONV)
      ALL_CONV
      (RAND_CONV drop_conv))
    (cond_conv
      (RATOR_CONV (RAND_CONV word_width_conv) THENC
       NUM_REDUCE_CONV)
      ALL_CONV
      (RAND_CONV
         (RAND_CONV
            (RATOR_CONV (RAND_CONV word_width_conv) THENC
             take_conv) THENC
          drop_conv)));;

let word_shl_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] word_shl_list in
  REWR_CONV th THENC
  RAND_CONV
    (LAND_CONV replicate_conv THENC
     append_conv);;

let word_bit_list_conv =
  let th = SPECL [`l : bool list`; `NUMERAL n`] list_to_word_bit in
  REWR_CONV th THENC
  andalso_conv
    (RAND_CONV word_width_conv THENC
     NUM_REDUCE_CONV)
    (andalso_conv
      (RAND_CONV length_conv THENC
       NUM_REDUCE_CONV)
      nth_conv);;

let word_bits_lte_conv =
  let nil_conv = REWR_CONV (CONJUNCT1 word_bits_lte_def) in
  let cons_conv = REWR_CONV (CONJUNCT2 word_bits_lte_def) in
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

let word_le_list_conv =
  let th = SYM (SPECL [`list_to_word l1`; `list_to_word l2`] word_le_list) in
  REWR_CONV th THENC
  LAND_CONV list_to_word_to_list_conv THENC
  RAND_CONV list_to_word_to_list_conv THENC
  word_bits_lte_conv;;

let word_lt_list_conv =
  let th = SYM (SPECL [`list_to_word l1`; `list_to_word l2`] word_lt_list) in
  REWR_CONV th THENC
  LAND_CONV list_to_word_to_list_conv THENC
  RAND_CONV list_to_word_to_list_conv THENC
  word_bits_lte_conv;;

let word_eq_list_conv =
  let th = SYM (SPECL [`list_to_word l1`; `list_to_word l2`]
                  word_to_list_inj_eq) in
  REWR_CONV th THENC
  LAND_CONV list_to_word_to_list_conv THENC
  RAND_CONV list_to_word_to_list_conv THENC
  list_eq_conv iff_simp_conv;;

let word_bit_conv =
  word_width_conv ORELSEC
  list_to_word_to_list_conv ORELSEC
  numeral_to_word_list_conv ORELSEC
  word_and_list_conv ORELSEC
  word_or_list_conv ORELSEC
  word_shr_list_conv ORELSEC
  word_shl_list_conv ORELSEC
  word_bit_list_conv ORELSEC
  word_le_list_conv ORELSEC
  word_lt_list_conv ORELSEC
  word_eq_list_conv;;

let bit_blast_subterm_conv = word_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* word *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* word *)

let prove_word_list_cases n =
  let interval =
      let rec intv i n = if n = 0 then [] else i :: intv (i + 1) (n - 1) in
      intv 0 in
  let lemma1 =
      let nunary = funpow n (fun t -> mk_comb (`SUC`,t)) `0` in
      let goal = mk_eq (`LENGTH (word_to_list w)`,nunary) in
      let tac =
          REWRITE_TAC [length_word_to_list; word_width_def] THEN
          NUM_REDUCE_TAC in
      prove (goal,tac) in
  let witnesses =
      let addtl l = mk_comb (`TL : bool list -> bool list`, hd l) :: l in
      let tls = rev (funpow (n - 1) addtl [`l : bool list`]) in
      map (fun t -> mk_comb (`HD : bool list -> bool`, t)) tls in
  let goal =
      let is = interval n in
      let xs = map (fun i -> mk_var ("x" ^ string_of_int i, bool_ty)) is in
      let w = mk_var ("w", `:word`) in
      let body = mk_eq (w, mk_comb (`list_to_word`, mk_list (xs,bool_ty))) in
      mk_forall (w, list_mk_exists (xs,body)) in
  let tac =
      GEN_TAC THEN
      CONV_TAC
        (funpow n (RAND_CONV o ABS_CONV)
           (LAND_CONV (ONCE_REWRITE_CONV [GSYM word_to_list_to_word]))) THEN
      MP_TAC lemma1 THEN
      SPEC_TAC (`word_to_list w`, `l : bool list`) THEN
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
*)

logfile_end ();;

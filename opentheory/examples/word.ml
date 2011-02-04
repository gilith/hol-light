(* ------------------------------------------------------------------------- *)
(* A functor theory of words.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "list-interval-def";;

let interval_def = new_recursive_definition num_RECURSION
  `(!m. interval m 0 = []) /\
   (!m n. interval m (SUC n) = CONS m (interval (SUC m) n))`;;

export_thm interval_def;;

logfile "list-interval-thm";;

let length_interval = prove
  (`!m n. LENGTH (interval m n) = n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   SIMP_TAC [LENGTH; interval_def; SUC_INJ]);;

export_thm length_interval;;

logfile "list-zipwith-def";;

let zipwith_raw_def = new_recursive_definition list_RECURSION
  `(!f l. zipwith f [] l = []) /\
   (!f h t l.
      zipwith f (CONS h t) l =
      CONS (f h (HD l)) (zipwith f t (TL l)))`;;

let zipwith_def = prove
   (`(!f. zipwith (f : A -> B -> C) [] [] = []) /\
     (!f h1 h2 t1 t2.
        zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
        CONS (f h1 h2) (zipwith f t1 t2))`,
    REWRITE_TAC [zipwith_raw_def; HD; TL]);;

export_thm zipwith_def;;

logfile "list-zipwith-thm";;

let length_zipwith = prove
  (`!(f : A -> B -> C) l1 l2 n.
      LENGTH l1 = n /\ LENGTH l2 = n ==> LENGTH (zipwith f l1 l2) = n`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [LENGTH; zipwith_def] THEN
   GEN_TAC THEN
   MP_TAC (SPEC `n:num` num_CASES) THEN
   STRIP_TAC THEN
   ASM_SIMP_TAC [NOT_SUC; SUC_INJ] THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC);;

export_thm length_zipwith;;

new_constant ("word_width", `:num`);;

logfile "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

export_thm word_size_def;;

let word_size_nonzero = prove
  (`~(word_size = 0)`,
   REWRITE_TAC [word_size_def; EXP_EQ_0] THEN
   NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

(* Apply theory functor modular *)

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
  `!x y. x < word_size /\ y < word_size /\ num_to_word x = num_to_word y ==> x = y`;;

let num_to_word_to_num = new_axiom
  `!x. word_to_num (num_to_word x) = x MOD word_size`;;

let num_to_word_add = new_axiom
  `!x1 y1. num_to_word (x1 + y1) = word_add (num_to_word x1) (num_to_word y1)`;;

let num_to_word_mult = new_axiom
  `!x1 y1. num_to_word (x1 * y1) = word_mult (num_to_word x1) (num_to_word y1)`;;

let word_neg_def = new_axiom
  `!x. word_neg x = num_to_word (word_size - word_to_num x)`;;

let word_sub_def = new_axiom
  `!x y. word_sub x y = word_add x (word_neg y)`;;

let word_le_def = new_axiom
  `!x y. word_le x y = word_to_num x <= word_to_num y`;;

let word_lt_def = new_axiom
  `!x y. word_lt x y = ~(word_le y x)`;;

let word_to_num_inj = new_axiom
  `!x y. word_to_num x = word_to_num y ==> x = y`;;

let num_to_word_eq = new_axiom
  `!x y. num_to_word x = num_to_word y <=> x MOD word_size = y MOD word_size`;;

logfile "word-bits";;

let word_shl_def = new_definition
 `!w n. word_shl w n = num_to_word (word_to_num w * (2 EXP n))`;;

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

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* A functor theory of words.                                                *)
(* ------------------------------------------------------------------------- *)

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

let word_to_num_bound = new_axiom
  `!x. word_to_num x < word_size`;;

logfile "word-bits-def";;

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

logfile "word-bits-thm";;

let length_word_to_list = prove
  (`!w. LENGTH (word_to_list w) = word_width`,
   REWRITE_TAC [word_to_list_def; LENGTH_MAP; length_interval]);;

export_thm length_word_to_list;;

(***
let list_to_word_to_list = prove
  (`!l. LENGTH l = word_width <=> word_to_list (list_to_word l) = l`,
   GEN_TAC THEN
   EQ_TAC THENL
   [

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

logfile_end ();;

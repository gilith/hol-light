(* ------------------------------------------------------------------------- *)
(* A functor theory of words.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "list-interval-def";;

let interval_def = new_recursive_definition num_RECURSION
  `(interval m 0 = []) /\
   (interval m (SUC n) = CONS m (interval (SUC m) n))`;;

export_thm interval_def;;

logfile "list-zipwith-def";;

let zipwith_raw_def = new_recursive_definition list_RECURSION
  `(zipwith f [] l = []) /\
   (zipwith f (CONS h t) l = CONS (f h (HD l)) (zipwith f t (TL l)))`;;

let zipwith_def = prove
   (`(!f. zipwith (f : A -> B -> C) [] [] = []) /\
     (!f h1 h2 t1 t2.
        zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
        CONS (f h1 h2) (zipwith f t1 t2))`,
    REWRITE_TAC [zipwith_raw_def; HD; TL]);;

export_thm zipwith_def;;

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

logfile "word-bits";;

let word_shl_def = new_definition
 `word_shl w n = num_to_word (word_to_num w * (2 EXP n))`;;

export_thm word_shl_def;;

let word_shr_def = new_definition
 `word_shr w n = num_to_word (word_to_num w DIV (2 EXP n))`;;

export_thm word_shr_def;;

let word_bit_def = new_definition
 `word_bit w n = ODD (word_to_num (word_shr w n))`;;

export_thm word_bit_def;;

let word_to_list_def = new_definition
 `word_to_list w = MAP (word_bit w) (interval 0 word_width)`;;

export_thm word_to_list_def;;

let list_to_word_def = new_recursive_definition list_RECURSION
  `(list_to_word [] = num_to_word 0) /\
   (list_to_word (CONS h t) =
    if h then word_add (word_shl (list_to_word t) 1) (num_to_word 1)
    else word_shl (list_to_word t) 1)`;;

export_thm list_to_word_def;;

let word_and_def = new_definition
  `word_and w1 w2 =
   list_to_word (zipwith ( /\ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_and_def;;

let word_or_def = new_definition
  `word_or w1 w2 =
   list_to_word (zipwith ( \/ ) (word_to_list w1) (word_to_list w2))`;;

export_thm word_or_def;;

let word_not_def = new_definition
  `word_not w = list_to_word (MAP (~) (word_to_list w))`;;

export_thm word_not_def;;

logfile_end ();;

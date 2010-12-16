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

new_constant ("word_to_num", `:word -> num`);;

logfile "word-bits";;

let word_to_list_f_def = new_recursive_definition num_RECURSION
 `(!k. word_to_list_f 0 k = []) /\
  (!n k. word_to_list_f (SUC n) k = CONS (ODD k) (word_to_list_f n (k DIV 2)))`;;

export_thm word_to_list_f_def;;

let word_to_list_def = new_definition
  `word_to_list w = word_to_list_f word_width (word_to_num w)`;;

export_thm word_to_list_def;;

logfile_end ();;

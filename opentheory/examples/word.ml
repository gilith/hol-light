(* ------------------------------------------------------------------------- *)
(* A functor theory of words.                                                *)
(* ------------------------------------------------------------------------- *)

new_constant ("word_width", `:num`);;

logfile "word-def";;

let word_size_def = new_definition
  `word_size = 2 EXP word_width`;;

export_thm word_size_def;;

let word_size_nonzero = prove
  (`0 < word_size`,
   REWRITE_TAC [word_size_def; EXP_LT_0] THEN
   NUM_REDUCE_TAC);;

export_thm word_size_nonzero;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* A type of Unicode characters.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "char-plane-def";;

let plane_size_def = new_definition
  `plane_size = 17`;;

export_thm plane_size_def;;

let plane_size_nonzero = prove
  (`0 < plane_size`,
   REWRITE_TAC [plane_size_def] THEN
   NUM_REDUCE_TAC);;

export_thm plane_size_nonzero;;

(* Apply theory functor modular *)

new_type ("plane",0);;

new_constant ("plane_to_num", `:plane -> num`);;

logfile "char-position-def";;

let position_width_def = new_definition
  `position_width = 16`;;

export_thm position_width_def;;

(* Apply theory functor word *)

new_type ("position",0);;

new_constant ("position_to_num", `:plane -> num`);;

logfile "char-def";;

let unicode_INDUCT,unicode_RECURSION = define_type
  "unicode = Unicode plane position";;

export_thm unicode_INDUCT;;
export_thm unicode_RECURSION;;

logfile_end ();;

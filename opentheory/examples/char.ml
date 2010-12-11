(* ------------------------------------------------------------------------- *)
(* A type of Unicode characters.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "char-def";;

(* plane[0..16] * code point[0..65535] *)

let plane_size_def = new_definition
  `plane_size = 17`;;

export_thm plane_size_def;;

let plane_size_nonzero = prove
  (`0 < plane_size`,
   REWRITE_TAC [plane_size_def] THEN
   NUM_REDUCE_TAC);;

export_thm plane_size_nonzero;;

logfile_end ();;

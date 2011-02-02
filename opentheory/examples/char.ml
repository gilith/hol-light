(* ------------------------------------------------------------------------- *)
(* A type of Unicode characters.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "char-def";;

let is_plane_def = new_definition
  `is_plane p = byte_lt p (num_to_byte 17)`;;

export_thm is_plane_def;;

let plane_exists = prove
  (`?p. is_plane p`,
   EXISTS_TAC `num_to_byte 0` THEN
   REWRITE_TAC [is_parser_def; case_option_def]);;

let plane_tybij =
    new_type_definition "plane" ("mk_plane","dest_plane") plane_exists;;

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

(* ------------------------------------------------------------------------- *)
(* UTF-8 encodings of unicode characters.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8";;

(* decode : byte list -> (char * byte list) option *)

logfile_end ();;

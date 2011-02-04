(* ------------------------------------------------------------------------- *)
(* A type of Unicode characters.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "char-def";;

(* Planes *)

let is_plane_def = new_definition
  `!p. is_plane p = byte_lt p (num_to_byte 17)`;;

export_thm is_plane_def;;

let plane_exists = prove
  (`?p. is_plane p`,
   EXISTS_TAC `num_to_byte 0` THEN
   REWRITE_TAC [is_plane_def] THEN
   CONV_TAC byte_reduce_conv);;

let plane_tybij =
    new_type_definition "plane" ("mk_plane","dest_plane") plane_exists;;

(* Positions *)

let is_position_def = new_definition
  `!p. is_position (p : word16) = T`;;

export_thm is_position_def;;

let position_exists = prove
  (`?p. is_position p`,
   EXISTS_TAC `p : word16` THEN
   REWRITE_TAC [is_position_def]);;

let position_tybij =
    new_type_definition
      "position" ("mk_position","dest_position") position_exists;;

(* Unicode characters *)

let is_unicode_def = new_definition
  `!pl pos. is_unicode (p : word16) = T`;;

export_thm is_position_def;;

newtype Unicode =
    Unicode { unUnicode :: (Plane,Position) }
  deriving (Eq,Show)

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

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

export_thm plane_tybij;;

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

export_thm position_tybij;;

(* Unicode characters *)

let is_unicode_def = new_definition
  `!pl pos.
     is_unicode (pl,pos) =
     let pli = dest_plane pl in
     let posi = dest_position pos in
     ~(pli = num_to_byte 0) \/
     word16_lt posi (num_to_word16 55296) \/
     (word16_lt (num_to_word16 57343) posi /\
      word16_lt posi (num_to_word16 65534))`;;

export_thm is_unicode_def;;

let unicode_exists = prove
  (`?pl_pos. is_unicode pl_pos`,
   EXISTS_TAC `(mk_plane (num_to_byte 1), (pos : position))` THEN
   REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC (SPEC `num_to_byte 1` (CONJUNCT2 plane_tybij)) THEN
   REWRITE_TAC [is_plane_def] THEN
   CONV_TAC byte_reduce_conv THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC byte_reduce_conv);;

let unicode_tybij =
    new_type_definition "unicode" ("mk_unicode","dest_unicode") unicode_exists;;

export_thm unicode_tybij;;

(* ------------------------------------------------------------------------- *)
(* UTF-8 encodings of unicode characters.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8";;

(* decode : byte list -> (char * byte list) option *)

logfile_end ();;

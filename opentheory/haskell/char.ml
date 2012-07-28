(* ========================================================================= *)
(* UNICODE CHARACTERS IN HASKELL                                             *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(***
type_invention_error := false;;
***)

(* ------------------------------------------------------------------------- *)
(* Definition.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-def";;

(* Unicode characters *)

let planeH_tybij = define_haskell_type
  `:plane`
  [];;

export_thm planeH_tybij;;

let positionH_tybij = define_haskell_type
  `:position`
  [];;

export_thm positionH_tybij;;

let unicodeH_tybij = define_haskell_type
  `:unicode`
  [];;

export_thm unicodeH_tybij;;

let mk_planeH_def = define_haskell_const
  `mk_plane : byte -> plane`;;

export_thm mk_planeH_def;;

let dest_planeH_def = define_haskell_const
  `dest_plane : plane -> byte`;;

export_thm dest_planeH_def;;

let mk_positionH_def = define_haskell_const
  `mk_position : word16 -> position`;;

export_thm mk_positionH_def;;

let dest_positionH_def = define_haskell_const
  `dest_position : position -> word16`;;

export_thm dest_positionH_def;;

let mk_unicodeH_def = define_haskell_const
  `mk_unicode : plane # position -> unicode`;;

export_thm mk_unicodeH_def;;

let dest_unicodeH_def = define_haskell_const
  `dest_unicode : unicode -> plane # position`;;

export_thm dest_unicodeH_def;;

(* UTF-8 encoding *)

let decoder_parseH_def = define_haskell_const
  `decoder_parse :
   byte -> byte pstream -> (unicode # byte pstream) option`;;

export_thm decoder_parseH_def;;

let decoderH_def = define_haskell_const
  `decoder : (byte,unicode) parser`;;

export_thm decoderH_def;;

let decode_pstreamH_def = define_haskell_const
  `decode_pstream : byte pstream -> unicode pstream`;;

export_thm decode_pstreamH_def;;

(* ------------------------------------------------------------------------- *)
(* Properties.                                                               *)
(* ------------------------------------------------------------------------- *)

(***
logfile "haskell-char-thm";;

(* Unicode characters *)

let planeH_mk_dest = prove
 (`!p : planeH. mk_planeH (dest_planeH p) = p`,
  REWRITE_TAC
    [mk_planeH_def; dest_planeH_def; plane_tybij; planeH_tybij]);;

export_thm planeH_mk_dest;;

let positionH_mk_dest = prove
 (`!p : positionH. mk_positionH (dest_positionH p) = p`,
  REWRITE_TAC
    [mk_positionH_def; dest_positionH_def; position_tybij; positionH_tybij]);;

export_thm positionH_mk_dest;;

let unicodeH_mk_dest = prove
 (`!c : unicodeH. mk_unicodeH (dest_unicodeH c) = c`,
  GEN_TAC THEN
  REWRITE_TAC [dest_unicodeH_def; LET_DEF; LET_END_DEF] THEN
  MP_TAC (SPEC `drop_unicodeH c` dest_unicode_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [mk_unicodeH_def; planeH_tybij; positionH_tybij] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [unicodeH_tybij]);;

export_thm unicodeH_mk_dest;;

(* UTF-8 encoding *)
***)

(* ------------------------------------------------------------------------- *)
(* Source.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-src";;

(* Unicode characters *)

let () = (export_haskell_thm o prove)
 (`!p : planeH. mk_planeH (dest_planeH p) = p`,
  HASKELL_TAC [plane_tybij]);;

let () = (export_haskell_thm o prove)
 (`!p : positionH. mk_positionH (dest_positionH p) = p`,
  HASKELL_TAC [position_tybij]);;

let () = (export_haskell_thm o prove)
 (`!c : unicodeH. mk_unicodeH (dest_unicodeH p) = p`,
  HASKELL_TAC [unicode_tybij]);;

(* UTF-8 encoding *)

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

(***
logfile "haskell-char-test";;

(* Unicode characters *)

(* UTF-8 encoding *)
***)

logfile_end ();;

(* ========================================================================= *)
(* UNICODE CHARACTERS IN HASKELL                                             *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-def";;

(* Unicode characters *)

let (planeH_lift_drop,planeH_drop_lift) =
  let exists = prove (`?(p : plane). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "planeH" ("lift_planeH","drop_planeH") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm planeH_lift_drop;;
export_thm planeH_drop_lift;;

let planeH_tybij = CONJ planeH_lift_drop planeH_drop_lift;;

let (positionH_lift_drop,positionH_drop_lift) =
  let exists = prove (`?(p : position). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "positionH" ("lift_positionH","drop_positionH") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm positionH_lift_drop;;
export_thm positionH_drop_lift;;

let positionH_tybij = CONJ positionH_lift_drop positionH_drop_lift;;

let (unicodeH_lift_drop,unicodeH_drop_lift) =
  let exists = prove (`?(p : unicode). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "unicodeH" ("lift_unicodeH","drop_unicodeH") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm unicodeH_lift_drop;;
export_thm unicodeH_drop_lift;;

let unicodeH_tybij = CONJ unicodeH_lift_drop unicodeH_drop_lift;;

let mk_planeH_def = new_definition
  `!b : byte. mk_planeH b = lift_planeH (mk_plane b)`;;

export_thm mk_planeH_def;;

let dest_planeH_def = new_definition
  `!p : planeH. dest_planeH p = dest_plane (drop_planeH p)`;;

export_thm dest_planeH_def;;

let mk_positionH_def = new_definition
  `!w : word16. mk_positionH w = lift_positionH (mk_position w)`;;

export_thm mk_positionH_def;;

let dest_positionH_def = new_definition
  `!p : positionH. dest_positionH p = dest_position (drop_positionH p)`;;

export_thm dest_positionH_def;;

let mk_unicodeH_def = new_definition
  `!pl pos.
      mk_unicodeH (pl,pos) =
      lift_unicodeH (mk_unicode (drop_planeH pl, drop_positionH pos))`;;

export_thm mk_unicodeH_def;;

let dest_unicodeH_def = new_definition
  `!c.
      dest_unicodeH c =
      let (pl,pos) = dest_unicode (drop_unicodeH c) in
      (lift_planeH pl, lift_positionH pos)`;;

export_thm dest_unicodeH_def;;

(* UTF-8 encoding *)

(***
let decoder_parseH_def = new_definition
  `decoder_parseH =
   lift_parser_functionH
     (\b s. parse_map lift_unicodeH decoder)`;;

export_thm decoderH_def;;

let decoderH_def = new_definition
  `decoderH = lift_parserH (parse_map lift_unicodeH decoder)`;;

export_thm decoderH_def;;

let decode_pstreamH_def = new_definition
  `!bs.
     decode_pstreamH bs =
     lift_pstreamH (decode_pstream (drop_pstreamH bs))`;;

export_thm decode_pstreamH_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties.                                                               *)
(* ------------------------------------------------------------------------- *)

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

(* ------------------------------------------------------------------------- *)
(* Source.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-src";;

(* Unicode characters *)

let () = export_haskell_thm planeH_mk_dest;;

let () = export_haskell_thm positionH_mk_dest;;

let () = export_haskell_thm unicodeH_mk_dest;;

(* UTF-8 encoding *)

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-test";;

(* Unicode characters *)

(* UTF-8 encoding *)

logfile_end ();;

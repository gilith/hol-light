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

let equal_planeH_def = new_definition
  `equal_planeH = ((=) : planeH -> planeH -> bool)`;;

add_haskell_thm equal_planeH_def;;
export_thm equal_planeH_def;;

let mk_planeH_def = define_haskell_const
  `mk_plane : byte -> plane`;;

export_thm mk_planeH_def;;

let dest_planeH_def = define_haskell_const
  `dest_plane : plane -> byte`;;

export_thm dest_planeH_def;;

let rdecode_planeH_def = define_haskell_const
  `rdecode_plane : random -> plane # random`;;

export_thm rdecode_planeH_def;;

let equal_positionH_def = new_definition
  `equal_positionH = ((=) : positionH -> positionH -> bool)`;;

add_haskell_thm equal_positionH_def;;
export_thm equal_positionH_def;;

let mk_positionH_def = define_haskell_const
  `mk_position : word16 -> position`;;

export_thm mk_positionH_def;;

let dest_positionH_def = define_haskell_const
  `dest_position : position -> word16`;;

export_thm dest_positionH_def;;

let rdecode_positionH_def = define_haskell_const
  `rdecode_position : random -> position # random`;;

export_thm rdecode_positionH_def;;

let equal_unicodeH_def = new_definition
  `equal_unicodeH = ((=) : unicodeH -> unicodeH -> bool)`;;

add_haskell_thm equal_unicodeH_def;;
export_thm equal_unicodeH_def;;

let mk_unicodeH_def = define_haskell_const
  `mk_unicode : plane # position -> unicode`;;

export_thm mk_unicodeH_def;;

let dest_unicodeH_def = define_haskell_const
  `dest_unicode : unicode -> plane # position`;;

export_thm dest_unicodeH_def;;

let rdecode_unicodeH_def = define_haskell_const
  `rdecode_unicode : random -> unicode # random`;;

export_thm rdecode_unicodeH_def;;

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
 (`!p. mk_planeH (dest_planeH p) = p`,
  HASKELL_TAC [plane_tybij]);;

let () = (export_haskell_thm o prove)
 (`!p1 p2. equal_planeH p1 p2 = (dest_planeH p1 = dest_planeH p2)`,
  HASKELL_TAC [dest_plane_inj]);;

let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_planeH r =
     let (n,r') = rdecode_uniformH 17 r in
     (mk_planeH (num_to_byte n), r')`,
  GEN_TAC THEN
  HASKELL_TAC [rdecode_plane_def] THEN
  PAIR_CASES_TAC `rdecode_uniform 17 r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [rdecode_plane_def; LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC []);;

let () = (export_haskell_thm o prove)
 (`!p. mk_positionH (dest_positionH p) = p`,
  HASKELL_TAC [position_tybij]);;

let () = (export_haskell_thm o prove)
 (`!p1 p2. equal_positionH p1 p2 = (dest_positionH p1 = dest_positionH p2)`,
  HASKELL_TAC [dest_position_inj]);;

(***
let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_positionH r =
     let (w,r') = rdecode_word16H r in
     (mk_positionH w, r')`,
  HASKELL_TAC []
  GEN_TAC THEN
  HASKELL_TAC [rdecode_plane_def] THEN
  PAIR_CASES_TAC `rdecode_uniform 17 r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `n : num`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [rdecode_plane_def; LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC []);;
***)

let () = (export_haskell_thm o prove)
 (`!c. mk_unicodeH (dest_unicodeH c) = c`,
  HASKELL_TAC [unicode_tybij]);;

let () = (export_haskell_thm o prove)
 (`!c1 c2.
     equal_unicodeH c1 c2 =
     let (pl1,pos1) = dest_unicodeH c1 in
     let (pl2,pos2) = dest_unicodeH c2 in
     equal_planeH pl1 pl2 /\ equal_positionH pos1 pos2`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [] THEN
  MP_TAC (SPEC `destH_unicodeH c1` dest_unicode_cases) THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `destH_unicodeH c2` dest_unicode_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  REWRITE_TAC [GSYM PAIR_EQ] THEN
  EQ_TAC THENL
  [POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [unicode_rep_abs]) THEN
   DISCH_THEN
     (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [unicode_rep_abs]) THEN
   DISCH_THEN
     (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

(* UTF-8 encoding *)

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-char-test";;

(* Unicode characters *)

let () = (export_haskell_thm o prove)
 (`!r.
     let (c,r') = rdecode_unicodeH r in
     let (pl,pos) = dest_unicodeH c in
     let pli = dest_planeH pl in
     let posi = dest_positionH pos in
     ~(pli = num_to_byte 0) \/
     word16_lt posi (num_to_word16 55296) \/
     (word16_lt (num_to_word16 57343) posi /\
      word16_lt posi (num_to_word16 65534))`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_unicodeH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `c : unicodeH`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MP_TAC (SPEC `destH_unicodeH c` dest_unicode_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  HASKELL_TAC [] THEN
  UNDISCH_TAC `is_unicode (pl,pos)` THEN
  REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF]);;

(***
(* UTF-8 encoding *)
***)

logfile_end ();;

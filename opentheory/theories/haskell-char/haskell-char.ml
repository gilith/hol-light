(* ========================================================================= *)
(* UNICODE CHARACTERS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for stream parsers.                                       *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/haskell-char/haskell-char.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Unicode characters.                                         *)
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

let is_contH_def = define_haskell_const
  `is_cont : byte -> bool`;;

export_thm is_contH_def;;

let parse_contH_def = define_haskell_const
  `parse_cont : (byte,byte) parser`;;

export_thm parse_contH_def;;

let parse_cont2H_def = define_haskell_const
  `parse_cont2 : (byte, byte # byte) parser`;;

export_thm parse_cont2H_def;;

let parse_cont3H_def = define_haskell_const
  `parse_cont3 : (byte, byte # byte # byte) parser`;;

export_thm parse_cont3H_def;;

let decode_cont1H_def = define_haskell_const
  `decode_cont1 : byte -> byte -> unicode option`;;

export_thm decode_cont1H_def;;

let decode_cont2H_def = define_haskell_const
  `decode_cont2 : byte -> byte # byte -> unicode option`;;

export_thm decode_cont2H_def;;

let decode_cont3H_def = define_haskell_const
  `decode_cont3 : byte -> byte # byte # byte -> unicode option`;;

export_thm decode_cont3H_def;;

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

let decodeH_def = define_haskell_const
  `decode : byte list -> (unicode list) option`;;

export_thm decodeH_def;;

let encode_cont1H_def = define_haskell_const
  `encode_cont1 : byte -> byte -> byte list`;;

export_thm encode_cont1H_def;;

let encode_cont2H_def = define_haskell_const
  `encode_cont2 : byte -> byte -> byte list`;;

export_thm encode_cont2H_def;;

let encode_cont3H_def = define_haskell_const
  `encode_cont3 : byte -> byte -> byte -> byte list`;;

export_thm encode_cont3H_def;;

let encoderH_def = define_haskell_const
  `encoder : unicode -> byte list`;;

export_thm encoderH_def;;

let encodeH_def = define_haskell_const
  `encode : unicode list -> byte list`;;

export_thm encodeH_def;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for Unicode characters.                                    *)
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

let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_positionH r =
     let (w,r') = rdecode_word16H r in
     (mk_positionH w, r')`,
  GEN_TAC THEN
  HASKELL_TAC [rdecode_position_def] THEN
  PAIR_CASES_TAC `rdecode_word16 r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `w : word16`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC []);;

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

let () = (export_haskell_thm o prove)
 (`!r.
     rdecode_unicodeH r =
     let (pl,r') = rdecode_planeH r in
     let pli = dest_planeH pl in
     let (pos,r'') =
         if ~(pli = num_to_byte 0) then rdecode_positionH r' else
         let (n,r''') = rdecode_uniformH 63486 r' in
         let n' = if n < 55296 then n else n + 2048 in
         (mk_positionH (num_to_word16 n'), r''') in
     (mk_unicodeH (pl,pos), r'')`,
  GEN_TAC THEN
  HASKELL_TAC [rdecode_unicode_def] THEN
  PAIR_CASES_TAC `rdecode_plane r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `pl : plane`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  ASM_CASES_TAC `dest_plane pl = num_to_byte 0` THENL
  [PAIR_CASES_TAC `rdecode_uniform 63486 r'` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `n : num`
       (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [] THEN
   HASKELL_TAC [];
   PAIR_CASES_TAC `rdecode_position r'` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `pos : position`
       (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [] THEN
   HASKELL_TAC []]);;

(* UTF-8 encoding *)

let () = (export_haskell_thm o prove)
 (`!b. is_contH b <=> byte_bit b 7 /\ ~byte_bit b 6`,
  HASKELL_TAC [is_cont_def]);;

let () = (export_haskell_thm o prove)
 (`parse_contH = parse_someH is_contH`,
  HASKELL_TAC [parse_cont_def]);;

let () = (export_haskell_thm o prove)
 (`parse_cont2H = parse_pairH parse_contH parse_contH`,
  HASKELL_TAC [parse_cont2_def]);;

let () = (export_haskell_thm o prove)
 (`parse_cont3H = parse_pairH parse_contH parse_cont2H`,
  HASKELL_TAC [parse_cont3_def]);;

let () = (export_haskell_thm o prove)
 (`!b0 b1.
     decode_cont1H b0 b1 =
     let pl = mk_planeH (num_to_byte 0) in
     let p1 = byte_shr (byte_and b0 (num_to_byte 28)) 2 in
     let y0 = byte_shl (byte_and b0 (num_to_byte 3)) 6 in
     let x0 = byte_and b1 (num_to_byte 63) in
     let p0 = byte_or y0 x0 in
     if p1 = num_to_byte 0 /\ ~byte_bit p0 7 then
       NONE
     else
       let pos = mk_positionH (bytes_to_word16 p0 p1) in
       let ch = mk_unicodeH (pl,pos) in
       SOME ch`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [decode_cont1_def] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  COND_CASES_TAC THEN
  HASKELL_TAC [map_option_def]);;

let () = (export_haskell_thm o prove)
 (`!b0 b1 b2.
     decode_cont2H b0 (b1,b2) =
     let z1 = byte_shl (byte_and b0 (num_to_byte 15)) 4 in
     let y1 = byte_shr (byte_and b1 (num_to_byte 60)) 2 in
     let p1 = byte_or z1 y1 in
     if byte_lt p1 (num_to_byte 8) \/
        (byte_le (num_to_byte 216) p1 /\
         byte_le p1 (num_to_byte 223)) then NONE
     else
       let y0 = byte_shl (byte_and b1 (num_to_byte 3)) 6 in
       let x0 = byte_and b2 (num_to_byte 63) in
       let p0 = byte_or y0 x0 in
       if p1 = num_to_byte 255 /\ byte_le (num_to_byte 254) p0 then NONE
       else
         let pl = mk_planeH (num_to_byte 0) in
         let pos = mk_positionH (bytes_to_word16 p0 p1) in
         let ch = mk_unicodeH (pl,pos) in
         SOME ch`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [decode_cont2_def] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [map_option_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [map_option_def]);;

let () = (export_haskell_thm o prove)
 (`!b0 b1 b2 b3.
     decode_cont3H b0 (b1,(b2,b3)) =
     let w = byte_shl (byte_and b0 (num_to_byte 7)) 2 in
     let z = byte_shr (byte_and b1 (num_to_byte 48)) 4 in
     let p = byte_or w z in
     if p = num_to_byte 0 \/ byte_lt (num_to_byte 16) p then NONE
     else
       let pl = mk_planeH p in
       let z1 = byte_shl (byte_and b1 (num_to_byte 15)) 4 in
       let y1 = byte_shr (byte_and b2 (num_to_byte 60)) 2 in
       let p1 = byte_or z1 y1 in
       let y0 = byte_shl (byte_and b2 (num_to_byte 3)) 6 in
       let x0 = byte_and b3 (num_to_byte 63) in
       let p0 = byte_or y0 x0 in
       let pos = mk_positionH (bytes_to_word16 p0 p1) in
       let ch = mk_unicodeH (pl,pos) in
       SOME ch`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [decode_cont3_def] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [map_option_def]);;

let () = (export_haskell_thm o prove)
 (`!b0 s.
     decoder_parseH b0 s =
     if byte_bit b0 7 then
       if byte_bit b0 6 then
         if byte_bit b0 5 then
           if byte_bit b0 4 then
             if byte_bit b0 3 then NONE
             else parseH (parse_partial_mapH (decode_cont3H b0) parse_cont3H) s
           else
             parseH (parse_partial_mapH (decode_cont2H b0) parse_cont2H) s
         else
           parseH (parse_partial_mapH (decode_cont1H b0) parse_contH) s
       else
         NONE
     else
       let pl = mk_planeH (num_to_byte 0) in
       let pos = mk_positionH (bytes_to_word16 b0 (num_to_byte 0)) in
       let ch = mk_unicodeH (pl,pos) in
       SOME (ch,s)`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [decoder_parse_def] THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MP_TAC (ISPEC `s : byte pstreamH` (CONJUNCT1 pstreamH_tybij)) THEN
  MP_TAC (ISPEC `destH_pstreamH s : byte pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
      (DISJ_CASES_THEN2 STRIP_ASSUME_TAC
        (X_CHOOSE_THEN `b : byte`
          (X_CHOOSE_THEN `s' : byte pstream` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  REPEAT
    (COND_CASES_TAC THEN
     HASKELL_TAC [] THEN
     ASM_REWRITE_TAC
       [map_option_def; map_fst_def; map_snd_def; o_THM; parse_def]) THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN
  REWRITE_TAC [map_option_o] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC
    [parse_partial_map_def;
     REWRITE_RULE [parser_tybij] is_parser_partial_map] THEN
  REWRITE_TAC [parser_partial_map_def] THENL
  [MP_TAC (ISPECL [`parse_cont3`; `b : byte`; `s' : byte pstream`]
     dest_parser_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `b123 : byte # byte # byte`
         (X_CHOOSE_THEN `s'' : byte pstream` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; o_THM] THEN
   option_cases_tac `decode_cont3 b0 b123` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; map_fst_def];
   MP_TAC (ISPECL [`parse_cont2`; `b : byte`; `s' : byte pstream`]
     dest_parser_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `b12 : byte # byte`
         (X_CHOOSE_THEN `s'' : byte pstream` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; o_THM] THEN
   option_cases_tac `decode_cont2 b0 b12` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; map_fst_def];
   MP_TAC (ISPECL [`parse_cont`; `b : byte`; `s' : byte pstream`]
     dest_parser_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `b1 : byte`
         (X_CHOOSE_THEN `s'' : byte pstream` STRIP_ASSUME_TAC))) THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; o_THM] THEN
   option_cases_tac `decode_cont1 b0 b1` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def; map_option_def; map_fst_def]]);;

let () = (export_haskell_thm o prove)
 (`decoderH = mk_parserH decoder_parseH`,
  HASKELL_TAC [decoder_def] THEN
  REWRITE_TAC [parse_map_def; parse_partial_map_def] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `b : byte` THEN
  X_GEN_TAC `s : byte pstream` THEN
  HASKELL_TAC [parser_partial_map_def] THEN
  SUBST1_TAC (REWRITE_RULE [parser_tybij] is_parser_decoder_parse) THEN
  option_cases_tac `decoder_parse b s` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `xs' : unicode # byte pstream` SUBST1_TAC) THEN
  PAIR_CASES_TAC `xs' : unicode # byte pstream` THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_fst_def]);;

let () = (export_haskell_thm o prove)
 (`decode_pstreamH = parse_pstreamH decoderH`,
  HASKELL_TAC [decode_pstream_def; parse_pstream_map]);;

let () = (export_haskell_thm o prove)
 (`!bs. decodeH bs = pstream_to_listH (decode_pstreamH (list_to_pstreamH bs))`,
  HASKELL_TAC [decode_def; pstream_to_list_map]);;

let () = (export_haskell_thm o prove)
 (`!p1 p0.
     encode_cont1H p1 p0 =
     let b00 = byte_shl p1 2 in
     let b01 = byte_shr (byte_and p0 (num_to_byte 192)) 6 in
     let b0 = byte_or (num_to_byte 192) (byte_or b00 b01) in
     let b10 = byte_and p0 (num_to_byte 63) in
     let b1 = byte_or (num_to_byte 128) b10 in
     CONS b0 (CONS b1 [])`,
  HASKELL_TAC [encode_cont1_def]);;

let () = (export_haskell_thm o prove)
 (`!p1 p0.
     encode_cont2H p1 p0 =
     let b00 = byte_shr (byte_and p1 (num_to_byte 240)) 4 in
     let b0 = byte_or (num_to_byte 224) b00 in
     let b10 = byte_shl (byte_and p1 (num_to_byte 15)) 2 in
     let b11 = byte_shr (byte_and p0 (num_to_byte 192)) 6 in
     let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
     let b20 = byte_and p0 (num_to_byte 63) in
     let b2 = byte_or (num_to_byte 128) b20 in
     CONS b0 (CONS b1 (CONS b2 []))`,
  HASKELL_TAC [encode_cont2_def]);;

let () = (export_haskell_thm o prove)
 (`!p p1 p0.
     encode_cont3H p p1 p0 =
     let b00 = byte_shr (byte_and p (num_to_byte 28)) 2 in
     let b0 = byte_or (num_to_byte 240) b00 in
     let b10 = byte_shl (byte_and p (num_to_byte 3)) 4 in
     let b11 = byte_shr (byte_and p1 (num_to_byte 240)) 4 in
     let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
     let b20 = byte_shl (byte_and p1 (num_to_byte 15)) 2 in
     let b21 = byte_shr (byte_and p0 (num_to_byte 192)) 6 in
     let b2 = byte_or (num_to_byte 128) (byte_or b20 b21) in
     let b30 = byte_and p0 (num_to_byte 63) in
     let b3 = byte_or (num_to_byte 128) b30 in
     CONS b0 (CONS b1 (CONS b2 (CONS b3 [])))`,
  HASKELL_TAC [encode_cont3_def]);;

let () = (export_haskell_thm o prove)
 (`encoderH =
   \ch.
     let (pl,pos) = dest_unicodeH ch in
     let p = dest_planeH pl in
     let (p0,p1) = word16_to_bytes (dest_positionH pos) in
     if p = num_to_byte 0 then
       if p1 = num_to_byte 0 /\ ~byte_bit p0 7 then
         CONS p0 []
       else
         if byte_and (num_to_byte 248) p1 = num_to_byte 0 then
           encode_cont1H p1 p0
         else
           encode_cont2H p1 p0
     else
       encode_cont3H p p1 p0`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   X_GEN_TAC `ch : unicodeH` THEN
   HASKELL_TAC [encoder_def] THEN
   MP_TAC (SPEC `destH_unicodeH ch` dest_unicode_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST1_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF; map_fst_def; map_snd_def] THEN
   HASKELL_TAC []);;

let () = (export_haskell_thm o prove)
 (`!chs. encodeH chs = concat (MAP encoderH chs)`,
   GEN_TAC THEN
   HASKELL_TAC [encode_def]);;

(* ------------------------------------------------------------------------- *)
(* QuickCheck tests for Unicode characters.                                  *)
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

(* UTF-8 encoding *)

let () = (export_haskell_thm o prove)
 (`!r.
     let (cs,r') = rdecode_listH rdecode_unicodeH r in
     equal_optionH (equal_listH equal_unicodeH)
       (decodeH (encodeH cs)) (SOME cs)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_unicodeH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `cs : unicodeH list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [decode_encode; map_option_def]);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (bs,r') = rdecode_listH rdecode_byteH r in
     case_option T (\cs. (equal_listH (=)) (encodeH cs) bs) (decodeH bs)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_byteH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `bs : byte list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MP_TAC (SPEC `bs : byte list` encode_decode) THEN
  option_cases_tac `decode bs` THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def] THEN
  HASKELL_TAC []);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (cs,r') = rdecode_listH rdecode_unicodeH r in
     lengthH cs <= lengthH (encodeH cs)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_unicodeH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `cs : unicodeH list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `LENGTH (MAP destH_unicodeH cs)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LENGTH_MAP; LE_REFL];
   MATCH_ACCEPT_TAC encode_length]);;

logfile_end ();;

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

logfile "char-thm";;

let plane_cases = prove
  (`!pl. ?b. is_plane b /\ pl = mk_plane b`,
   GEN_TAC THEN
   EXISTS_TAC `dest_plane pl` THEN
   REWRITE_TAC [plane_tybij]);;

export_thm plane_cases;;

let dest_plane_cases = prove
  (`!pl. ?b. is_plane b /\ pl = mk_plane b /\ dest_plane pl = b`,
   GEN_TAC THEN
   MP_TAC (SPEC `pl : plane` plane_cases) THEN
   REWRITE_TAC [plane_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `b : byte` THEN
   ASM_REWRITE_TAC []);;

export_thm dest_plane_cases;;

let position_cases = prove
  (`!pos. ?w. is_position w /\ pos = mk_position w`,
   GEN_TAC THEN
   EXISTS_TAC `dest_position pos` THEN
   REWRITE_TAC [position_tybij]);;

export_thm position_cases;;

let dest_position_cases = prove
  (`!pos. ?w. is_position w /\ pos = mk_position w /\ dest_position pos = w`,
   GEN_TAC THEN
   MP_TAC (SPEC `pos : position` position_cases) THEN
   REWRITE_TAC [position_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `w : word16` THEN
   ASM_REWRITE_TAC []);;

export_thm dest_position_cases;;

let unicode_cases = prove
  (`!c. ?pl pos. is_unicode (pl,pos) /\ c = mk_unicode (pl,pos)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (dest_unicode c)` THEN
   EXISTS_TAC `SND (dest_unicode c)` THEN
   REWRITE_TAC [unicode_tybij]);;

export_thm unicode_cases;;

let dest_unicode_cases = prove
  (`!c. ?pl pos.
      is_unicode (pl,pos) /\ c = mk_unicode (pl,pos) /\
      dest_unicode c = (pl,pos)`,
   GEN_TAC THEN
   MP_TAC (SPEC `c : unicode` unicode_cases) THEN
   REWRITE_TAC [unicode_tybij] THEN
   STRIP_TAC THEN
   EXISTS_TAC `pl : plane` THEN
   EXISTS_TAC `pos : position` THEN
   ASM_REWRITE_TAC []);;

export_thm dest_unicode_cases;;

(* ------------------------------------------------------------------------- *)
(* UTF-8 encodings of unicode characters.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8-def";;

let is_cont_def = new_definition
  `!b. is_cont b <=> byte_bit b 7 /\ ~byte_bit b 6`;;

export_thm is_cont_def;;

let parse_cont_def = new_definition
  `parse_cont = parse_some is_cont`;;

export_thm parse_cont_def;;

let parse_cont2_def = new_definition
  `parse_cont2 = parse_pair parse_cont parse_cont`;;

export_thm parse_cont2_def;;

let parse_cont3_def = new_definition
  `parse_cont3 = parse_pair parse_cont parse_cont2`;;

export_thm parse_cont3_def;;

let decode_cont1_def = new_definition
  `!b0 b1.
     decode_cont1 b0 b1 =
     let pl = mk_plane (num_to_byte 0) in
     let p0 = byte_shr (byte_and b0 (num_to_byte 28)) 2 in
     let y1 = byte_shl (byte_and b0 (num_to_byte 3)) 6 in
     let x1 = byte_and b1 (num_to_byte 63) in
     let p1 = byte_or y1 x1 in
     if p0 = num_to_byte 0 /\ byte_lt p1 (num_to_byte 128) then
       NONE
     else
       let pos = mk_position (bytes_to_word16 p0 p1) in
       let ch = mk_unicode (pl,pos) in
       SOME ch`;;

export_thm decode_cont1_def;;

let decode_cont2_def = new_definition
  `!b0 b1 b2.
     decode_cont2 b0 (b1,b2) =
     let z0 = byte_shl (byte_and b0 (num_to_byte 15)) 4 in
     let y0 = byte_shr (byte_and b1 (num_to_byte 60)) 2 in
     let p0 = byte_or z0 y0 in
     if byte_lt p0 (num_to_byte 8) \/
        (byte_le (num_to_byte 216) p0 /\
         byte_le p0 (num_to_byte 223)) then NONE
     else
       let y1 = byte_shl (byte_and b1 (num_to_byte 3)) 6 in
       let x1 = byte_and b2 (num_to_byte 63) in
       let p1 = byte_or y1 x1 in
       if p0 = num_to_byte 255 /\ byte_le (num_to_byte 254) p1 then NONE
       else
         let pl = mk_plane (num_to_byte 0) in
         let pos = mk_position (bytes_to_word16 p0 p1) in
         let ch = mk_unicode (pl,pos) in
         SOME ch`;;

export_thm decode_cont2_def;;

let decode_cont3_def = new_definition
  `!b0 b1 b2 b3.
     decode_cont3 b0 (b1,(b2,b3)) =
     let w = byte_shl (byte_and b0 (num_to_byte 7)) 2 in
     let z = byte_shr (byte_and b1 (num_to_byte 48)) 4 in
     let p = byte_or w z in
     if p = num_to_byte 0 \/ byte_lt (num_to_byte 16) p then NONE
     else
       let pl = mk_plane p in
       let z0 = byte_shl (byte_and b1 (num_to_byte 15)) 4 in
       let y0 = byte_shr (byte_and b2 (num_to_byte 60)) 2 in
       let p0 = byte_or z0 y0 in
       let y1 = byte_shl (byte_and b2 (num_to_byte 3)) 6 in
       let x1 = byte_and b3 (num_to_byte 63) in
       let p1 = byte_or y1 x1 in
       let pos = mk_position (bytes_to_word16 p0 p1) in
       let ch = mk_unicode (pl,pos) in
       SOME ch`;;

export_thm decode_cont3_def;;

let decoder_parse_def = new_definition
  `!b0 s.
     decoder_parse b0 s =
     if byte_bit b0 7 then
       if byte_bit b0 6 then
         if byte_bit b0 5 then
           if byte_bit b0 4 then
             if byte_bit b0 3 then NONE
             else parse (parse_partial_map (decode_cont3 b0) parse_cont3) s
           else
             parse (parse_partial_map (decode_cont2 b0) parse_cont2) s
         else
           parse (parse_partial_map (decode_cont1 b0) parse_cont) s
       else
         NONE
     else
       let pl = mk_plane (num_to_byte 0) in
       let pos = mk_position (bytes_to_word16 (num_to_byte 0) b0) in
       let ch = mk_unicode (pl,pos) in
       SOME (ch,s)`;;

export_thm decoder_parse_def;;

let decoder_def = new_definition
  `decoder = mk_parser decoder_parse`;;

export_thm decoder_def;;

let decode_stream_def = new_definition
  `decode_stream = parse_stream decoder`;;

export_thm decode_stream_def;;

let decode_def = new_definition
  `!bs. decode bs = stream_to_list (decode_stream (list_to_stream bs))`;;

export_thm decode_def;;

let encode_cont1_def = new_definition
  `!p0 p1.
     encode_cont1 p0 p1 =
     let b00 = byte_shl p0 2 in
     let b01 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
     let b0 = byte_or (num_to_byte 192) (byte_or b00 b01) in
     let b10 = byte_and p1 (num_to_byte 63) in
     let b1 = byte_or (num_to_byte 128) b10 in
     CONS b0 (CONS b1 [])`;;

export_thm encode_cont1_def;;

let encode_cont2_def = new_definition
  `!p0 p1.
     encode_cont2 p0 p1 =
     let b00 = byte_shr (byte_and p0 (num_to_byte 240)) 4 in
     let b0 = byte_or (num_to_byte 224) b00 in
     let b10 = byte_shl (byte_and p0 (num_to_byte 15)) 2 in
     let b11 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
     let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
     let b20 = byte_and p1 (num_to_byte 63) in
     let b2 = byte_or (num_to_byte 128) b20 in
     CONS b0 (CONS b1 (CONS b2 []))`;;

export_thm encode_cont2_def;;

let encode_cont3_def = new_definition
  `!p p0 p1.
     encode_cont3 p p0 p1 =
     let b00 = byte_shr (byte_and p (num_to_byte 28)) 2 in
     let b0 = byte_or (num_to_byte 240) b00 in
     let b10 = byte_shl (byte_and p (num_to_byte 3)) 4 in
     let b11 = byte_shr (byte_and p0 (num_to_byte 240)) 4 in
     let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
     let b20 = byte_shl (byte_and p0 (num_to_byte 15)) 2 in
     let b21 = byte_shr (byte_and p1 (num_to_byte 192)) 6 in
     let b2 = byte_or (num_to_byte 128) (byte_or b20 b21) in
     let b30 = byte_and p1 (num_to_byte 63) in
     let b3 = byte_or (num_to_byte 128) b30 in
     CONS b0 (CONS b1 (CONS b2 (CONS b3 [])))`;;

export_thm encode_cont3_def;;

let encoder_def = new_definition
  `!ch.
     encoder ch =
     let (pl,pos) = dest_unicode ch in
     let p = dest_plane pl in
     let (p0,p1) = word16_to_bytes (dest_position pos) in
     if p = num_to_byte 0 then
       if p0 = num_to_byte 0 /\ ~byte_bit p1 7 then
         CONS p1 []
       else
         if byte_and (num_to_byte 248) p0 = num_to_byte 0 then
           encode_cont1 p0 p1
         else
           encode_cont2 p0 p1
     else
       encode_cont3 p p0 p1`;;

export_thm encoder_def;;

let encode_def = new_definition
  `!chs. encode chs = concat (MAP encoder chs)`;;

export_thm encode_def;;

logfile "char-utf8-thm";;

let is_parser_decoder_parse = prove
  (`is_parser decoder_parse`,
   REWRITE_TAC [is_parser_def; decoder_parse_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `byte_bit x 7` BOOL_CASES_AX) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def; COND_CLAUSES] THENL
   [MP_TAC (SPEC `byte_bit x 6` BOOL_CASES_AX) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; COND_CLAUSES] THEN
    MP_TAC (SPEC `byte_bit x 5` BOOL_CASES_AX) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; COND_CLAUSES] THENL
    [MP_TAC (SPEC `byte_bit x 4` BOOL_CASES_AX) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def; COND_CLAUSES] THENL
     [MP_TAC (SPEC `byte_bit x 3` BOOL_CASES_AX) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def; COND_CLAUSES] THEN
      MP_TAC (ISPECL [`parse_partial_map (decode_cont3 x) parse_cont3`;
                      `xs : byte stream`] parse_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MATCH_MP_TAC is_suffix_stream_proper THEN
      ASM_REWRITE_TAC [];
      MP_TAC (ISPECL [`parse_partial_map (decode_cont2 x) parse_cont2`;
                      `xs : byte stream`] parse_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MATCH_MP_TAC is_suffix_stream_proper THEN
      ASM_REWRITE_TAC []];
     MP_TAC (ISPECL [`parse_partial_map (decode_cont1 x) parse_cont`;
                     `xs : byte stream`] parse_cases) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     MATCH_MP_TAC is_suffix_stream_proper THEN
     ASM_REWRITE_TAC []];
    REWRITE_TAC
      [LET_DEF; LET_END_DEF; case_option_def; is_suffix_stream_refl]]);;

export_thm is_parser_decoder_parse;;

let dest_parser_decoder = prove
  (`dest_parser decoder = decoder_parse`,
   REWRITE_TAC
     [decoder_def; GSYM (CONJUNCT2 parser_tybij);
      is_parser_decoder_parse]);;

export_thm dest_parser_decoder;;

let parse_decoder = prove
  (`parse decoder = case_stream NONE NONE decoder_parse`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `x : byte stream` stream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def; case_stream_def; dest_parser_decoder]);;

export_thm parse_decoder;;

(***
let decoder_encoder_inverse = prove
  (`parse_inverse decoder encoder`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [encoder_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC (SPEC `x : unicode` dest_unicode_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `pl : plane` dest_plane_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (SPEC `pos : position` dest_position_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `w : word16` dest_bytes_to_word16_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   bool_cases_tac `b = num_to_byte 0` THENL
   [ASM_REWRITE_TAC [] THEN
    bool_cases_tac `b0 = num_to_byte 0 /\ ~byte_bit b1 7` THENL
    [ASM_REWRITE_TAC [append_stream_def] THEN
     REWRITE_TAC [parse_decoder; case_stream_def; decoder_parse_def] THEN
     ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
     ASM_REWRITE_TAC [] THEN
     bool_cases_tac `byte_and (num_to_byte 248) b0 = num_to_byte 0` THENL
     [ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [encode_cont1_def] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      MP_TAC (SPEC `b0 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      REWRITE_TAC [append_stream_def] THEN
      REWRITE_TAC [parse_decoder; case_stream_def] THEN
      REWRITE_TAC [decoder_parse_def] THEN
      bit_blast_tac THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC
        [parse_parse_partial_map; parse_parse_some; parse_cont_def;
         case_option_def; case_stream_def; is_cont_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [case_option_def] THEN
      REWRITE_TAC [decode_cont1_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      PAT_ASSUM `~(x /\ y)` THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      AP_TERM_TAC THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      bit_blast_tac;
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [encode_cont2_def] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      MP_TAC (SPEC `b0 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      REWRITE_TAC [append_stream_def] THEN
      REWRITE_TAC [parse_decoder; case_stream_def] THEN
      REWRITE_TAC [decoder_parse_def] THEN
      bit_blast_tac THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC
        [parse_parse_partial_map; parse_parse_some; parse_cont2_def;
         parse_parse_pair; parse_cont_def;
         case_option_def; case_stream_def; is_cont_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [case_option_def; case_stream_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [case_option_def] THEN
      REWRITE_TAC [decode_cont2_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      KNOW_TAC
        `~(~x7 /\ ~x6 /\ ~x5 /\ ~x4 /\ ~x3 \/
           (x7 /\ x6 /\ (x5 \/ x4 /\ x3)) /\ (~x7 \/ ~x6 \/ ~x5))` THENL
      [POP_ASSUM MP_TAC THEN
       POP_ASSUM MP_TAC THEN
       POP_ASSUM_LIST (K ALL_TAC) THEN
       BOOL_CASES_TAC `x5 : bool` THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `x6 : bool` THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `x7 : bool` THEN
       REWRITE_TAC [] THEN

ASM_MESON_TAC []

      PAT_ASSUM `~(x /\ y)` THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      AP_TERM_TAC THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_TERM_TAC THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      bit_blast_tac;
      

   REWRITE_TAC [parse_decoder_def]

export_thm decoder_encoder_inverse;;

let decoder_encoder_strong_inverse = prove
  (`parse_strong_inverse decoder encoder`,
   REWRITE_TAC [parse_strong_inverse_def] THEN

export_thm decoder_encoder_strong_inverse;;
***)

logfile_end ();;

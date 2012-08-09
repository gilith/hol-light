(* ========================================================================= *)
(* UNICODE CHARACTERS                                                        *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

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

let (plane_abs_rep,plane_rep_abs) =
  let tybij =
    new_type_definition "plane" ("mk_plane","dest_plane") plane_exists in
  CONJ_PAIR tybij;;

export_thm plane_abs_rep;;
export_thm plane_rep_abs;;

let plane_tybij = CONJ plane_abs_rep plane_rep_abs;;

let rdecode_plane_def = new_definition
  `!r.
     rdecode_plane r =
     let (n,r') = rdecode_uniform 17 r in
     (mk_plane (num_to_byte n), r')`;;

export_thm rdecode_plane_def;;

(* Positions *)

let is_position_def =
  let def = new_definition
    `!p. is_position (p : word16) = T` in
  REWRITE_RULE [] def;;

export_thm is_position_def;;

let position_exists = prove
  (`?p. is_position p`,
   EXISTS_TAC `p : word16` THEN
   REWRITE_TAC [is_position_def]);;

let (position_abs_rep,position_rep_abs) =
  let tybij =
    new_type_definition
      "position" ("mk_position","dest_position") position_exists in
  CONJ_PAIR (REWRITE_RULE [is_position_def] tybij);;

export_thm position_abs_rep;;
export_thm position_rep_abs;;

let position_tybij = CONJ position_abs_rep position_rep_abs;;

let rdecode_position_def = new_definition
  `!r.
     rdecode_position r =
     let (w,r') = rdecode_word16 r in
     (mk_position w, r')`;;

export_thm rdecode_position_def;;

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

let (unicode_abs_rep,unicode_rep_abs) =
  let tybij =
    new_type_definition
      "unicode" ("mk_unicode","dest_unicode") unicode_exists in
  CONJ_PAIR tybij;;

export_thm unicode_abs_rep;;
export_thm unicode_rep_abs;;

let unicode_tybij = CONJ unicode_abs_rep unicode_rep_abs;;

let rdecode_unicode_def = new_definition
  `!r.
     rdecode_unicode r =
     let (pl,r') = rdecode_plane r in
     let pli = dest_plane pl in
     let (pos,r'') =
         if ~(pli = num_to_byte 0) then rdecode_position r' else
         let (n,r''') = rdecode_uniform 63486 r' in
         let n' = if n < 55296 then n else n + 2048 in
         (mk_position (num_to_word16 n'), r''') in
     (mk_unicode (pl,pos), r'')`;;

export_thm rdecode_unicode_def;;

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

let dest_plane_inj = prove
  (`!pl1 pl2. dest_plane pl1 = dest_plane pl2 <=> pl1 = pl2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM plane_abs_rep] THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm dest_plane_inj;;

let position_cases = prove
  (`!pos. ?w. pos = mk_position w`,
   GEN_TAC THEN
   EXISTS_TAC `dest_position pos` THEN
   REWRITE_TAC [position_tybij]);;

export_thm position_cases;;

let dest_position_cases = prove
  (`!pos. ?w. pos = mk_position w /\ dest_position pos = w`,
   GEN_TAC THEN
   MP_TAC (SPEC `pos : position` position_cases) THEN
   STRIP_TAC THEN
   EXISTS_TAC `w : word16` THEN
   ASM_REWRITE_TAC [position_tybij]);;

export_thm dest_position_cases;;

let dest_position_inj = prove
  (`!pos1 pos2. dest_position pos1 = dest_position pos2 <=> pos1 = pos2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM position_abs_rep] THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm dest_position_inj;;

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

let dest_unicode_inj = prove
  (`!c1 c2. dest_unicode c1 = dest_unicode c2 <=> c1 = c2`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ONCE_REWRITE_TAC [GSYM unicode_abs_rep] THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm dest_unicode_inj;;

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
     let p1 = byte_shr (byte_and b0 (num_to_byte 28)) 2 in
     let y0 = byte_shl (byte_and b0 (num_to_byte 3)) 6 in
     let x0 = byte_and b1 (num_to_byte 63) in
     let p0 = byte_or y0 x0 in
     if p1 = num_to_byte 0 /\ ~byte_bit p0 7 then
       NONE
     else
       let pos = mk_position (bytes_to_word16 p0 p1) in
       let ch = mk_unicode (pl,pos) in
       SOME ch`;;

export_thm decode_cont1_def;;

let decode_cont2_def = new_definition
  `!b0 b1 b2.
     decode_cont2 b0 (b1,b2) =
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
       let z1 = byte_shl (byte_and b1 (num_to_byte 15)) 4 in
       let y1 = byte_shr (byte_and b2 (num_to_byte 60)) 2 in
       let p1 = byte_or z1 y1 in
       let y0 = byte_shl (byte_and b2 (num_to_byte 3)) 6 in
       let x0 = byte_and b3 (num_to_byte 63) in
       let p0 = byte_or y0 x0 in
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
       let pos = mk_position (bytes_to_word16 b0 (num_to_byte 0)) in
       let ch = mk_unicode (pl,pos) in
       SOME (ch,s)`;;

export_thm decoder_parse_def;;

let decoder_def = new_definition
  `decoder = mk_parser decoder_parse`;;

export_thm decoder_def;;

let decode_pstream_def = new_definition
  `decode_pstream = parse_pstream decoder`;;

export_thm decode_pstream_def;;

let decode_def = new_definition
  `!bs. decode bs = pstream_to_list (decode_pstream (list_to_pstream bs))`;;

export_thm decode_def;;

let encode_cont1_def = new_definition
  `!p1 p0.
     encode_cont1 p1 p0 =
     let b00 = byte_shl p1 2 in
     let b01 = byte_shr (byte_and p0 (num_to_byte 192)) 6 in
     let b0 = byte_or (num_to_byte 192) (byte_or b00 b01) in
     let b10 = byte_and p0 (num_to_byte 63) in
     let b1 = byte_or (num_to_byte 128) b10 in
     CONS b0 (CONS b1 [])`;;

export_thm encode_cont1_def;;

let encode_cont2_def = new_definition
  `!p1 p0.
     encode_cont2 p1 p0 =
     let b00 = byte_shr (byte_and p1 (num_to_byte 240)) 4 in
     let b0 = byte_or (num_to_byte 224) b00 in
     let b10 = byte_shl (byte_and p1 (num_to_byte 15)) 2 in
     let b11 = byte_shr (byte_and p0 (num_to_byte 192)) 6 in
     let b1 = byte_or (num_to_byte 128) (byte_or b10 b11) in
     let b20 = byte_and p0 (num_to_byte 63) in
     let b2 = byte_or (num_to_byte 128) b20 in
     CONS b0 (CONS b1 (CONS b2 []))`;;

export_thm encode_cont2_def;;

let encode_cont3_def = new_definition
  `!p p1 p0.
     encode_cont3 p p1 p0 =
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
     CONS b0 (CONS b1 (CONS b2 (CONS b3 [])))`;;

export_thm encode_cont3_def;;

let encoder_def = new_definition
  `!ch.
     encoder ch =
     let (pl,pos) = dest_unicode ch in
     let p = dest_plane pl in
     let (p0,p1) = word16_to_bytes (dest_position pos) in
     if p = num_to_byte 0 then
       if p1 = num_to_byte 0 /\ ~byte_bit p0 7 then
         CONS p0 []
       else
         if byte_and (num_to_byte 248) p1 = num_to_byte 0 then
           encode_cont1 p1 p0
         else
           encode_cont2 p1 p0
     else
       encode_cont3 p p1 p0`;;

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
                      `xs : byte pstream`] parse_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MATCH_MP_TAC is_suffix_pstream_proper THEN
      ASM_REWRITE_TAC [];
      MP_TAC (ISPECL [`parse_partial_map (decode_cont2 x) parse_cont2`;
                      `xs : byte pstream`] parse_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      MATCH_MP_TAC is_suffix_pstream_proper THEN
      ASM_REWRITE_TAC []];
     MP_TAC (ISPECL [`parse_partial_map (decode_cont1 x) parse_cont`;
                     `xs : byte pstream`] parse_cases) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def] THEN
     MATCH_MP_TAC is_suffix_pstream_proper THEN
     ASM_REWRITE_TAC []];
    REWRITE_TAC
      [LET_DEF; LET_END_DEF; case_option_def; is_suffix_pstream_refl]]);;

export_thm is_parser_decoder_parse;;

let dest_parser_decoder = prove
  (`dest_parser decoder = decoder_parse`,
   REWRITE_TAC
     [decoder_def; GSYM (CONJUNCT2 parser_tybij);
      is_parser_decoder_parse]);;

export_thm dest_parser_decoder;;

let parse_decoder = prove
  (`parse decoder = case_pstream NONE NONE decoder_parse`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `x : byte pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def; case_pstream_def; dest_parser_decoder]);;

export_thm parse_decoder;;

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
   DISCH_THEN (X_CHOOSE_THEN `p : byte` STRIP_ASSUME_TAC) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (SPEC `pos : position` dest_position_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `w : word16` dest_bytes_to_word16_cases) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `p0 : byte`
       (X_CHOOSE_THEN `p1 : byte` STRIP_ASSUME_TAC)) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   bool_cases_tac `p = num_to_byte 0` THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [] THEN
    bool_cases_tac `p1 = num_to_byte 0 /\ ~byte_bit p0 7` THENL
    [FIRST_X_ASSUM SUBST_VAR_TAC THEN
     ASM_REWRITE_TAC [append_pstream_def] THEN
     REWRITE_TAC [parse_decoder; case_pstream_def; decoder_parse_def] THEN
     ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
     ASM_REWRITE_TAC [] THEN
     bool_cases_tac `byte_and (num_to_byte 248) p1 = num_to_byte 0` THENL
     [ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [encode_cont1_def] THEN
      REPEAT (POP_ASSUM MP_TAC) THEN
      MP_TAC (SPEC `p1 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      MP_TAC (SPEC `p0 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      REWRITE_TAC [append_pstream_def] THEN
      REWRITE_TAC [parse_decoder; case_pstream_def] THEN
      REWRITE_TAC [decoder_parse_def] THEN
      bit_blast_tac THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC
        [parse_parse_partial_map; parse_parse_some; parse_cont_def;
         case_option_def; case_pstream_def; is_cont_def] THEN
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
      MP_TAC (SPEC `p1 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      MP_TAC (SPEC `p0 : byte` byte_list_cases) THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      REWRITE_TAC [append_pstream_def] THEN
      REWRITE_TAC [parse_decoder; case_pstream_def] THEN
      REWRITE_TAC [decoder_parse_def] THEN
      bit_blast_tac THEN
      REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC
        [parse_parse_partial_map; parse_parse_some; parse_cont2_def;
         parse_parse_pair; parse_cont_def;
         case_option_def; case_pstream_def; is_cont_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [case_option_def; case_pstream_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [case_option_def] THEN
      REWRITE_TAC [decode_cont2_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      MATCH_MP_TAC EQ_SYM THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      REWRITE_TAC [case_option_def; option_distinct] THEN
      KNOW_TAC `!c b. ~c /\ b ==> (if c then F else b)` THENL
      [REWRITE_TAC [COND_EXPAND] THEN
       ITAUT_TAC;
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
      [PAT_ASSUM `is_unicode X` THEN
       ASM_REWRITE_TAC [is_unicode_def; position_tybij] THEN
       PAT_ASSUM `is_plane X` THEN
       REWRITE_TAC [plane_tybij] THEN
       DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
       bit_blast_tac THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       bit_blast_tac THEN
       ASM_TAUT_TAC;
       ALL_TAC] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      REWRITE_TAC [case_option_def; option_distinct] THEN
      KNOW_TAC `!c. ~c ==> (if c then F else T)` THENL
      [REWRITE_TAC [COND_EXPAND];
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      PAT_ASSUM `is_unicode X` THEN
      ASM_REWRITE_TAC [is_unicode_def; position_tybij] THEN
      PAT_ASSUM `is_plane X` THEN
      ASM_REWRITE_TAC [plane_tybij] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      ASM_TAUT_TAC]];
    ASM_REWRITE_TAC [] THEN
    PAT_ASSUM `is_unicode X` THEN
    DISCH_THEN (K ALL_TAC) THEN
    REWRITE_TAC [encode_cont3_def] THEN
    REPEAT (POP_ASSUM MP_TAC) THEN
    MP_TAC (SPEC `p : byte` byte_list_cases) THEN
    STRIP_TAC THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `p1 : byte` byte_list_cases) THEN
    STRIP_TAC THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPEC `p0 : byte` byte_list_cases) THEN
    STRIP_TAC THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    bit_blast_tac THEN
    REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    bit_blast_tac THEN
    REWRITE_TAC [append_pstream_def] THEN
    REWRITE_TAC [parse_decoder; case_pstream_def] THEN
    REWRITE_TAC [decoder_parse_def] THEN
    bit_blast_tac THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC
      [parse_parse_partial_map; parse_parse_some; parse_cont3_def;
       parse_parse_pair; parse_cont2_def; parse_cont_def;
       case_option_def; case_pstream_def; is_cont_def] THEN
    bit_blast_tac THEN
    REWRITE_TAC [case_option_def; case_pstream_def] THEN
    bit_blast_tac THEN
    REWRITE_TAC [case_option_def; case_pstream_def] THEN
    bit_blast_tac THEN
    REWRITE_TAC [case_option_def; case_pstream_def] THEN
    REWRITE_TAC [decode_cont3_def] THEN
    bit_blast_tac THEN
    REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    bit_blast_tac THEN
    MATCH_MP_TAC EQ_SYM THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    ONCE_REWRITE_TAC [COND_RAND] THEN
    REWRITE_TAC [case_option_def; option_distinct] THEN
    KNOW_TAC `!c b. ~c /\ b ==> (if c then F else b)` THENL
    [REWRITE_TAC [COND_EXPAND] THEN
     ITAUT_TAC;
     ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [PAT_ASSUM `is_plane X` THEN
     ASM_REWRITE_TAC [is_plane_def] THEN
     bit_blast_tac THEN
     ASM_TAUT_TAC;
     ALL_TAC] THEN
    AP_TERM_TAC THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    PAT_ASSUM `is_plane X` THEN
    ASM_REWRITE_TAC [is_plane_def] THEN
    bit_blast_tac THEN
    ASM_TAUT_TAC]);;

export_thm decoder_encoder_inverse;;

let decoder_encoder_strong_inverse = prove
  (`parse_strong_inverse decoder encoder`,
   REWRITE_TAC
     [parse_strong_inverse_def; decoder_encoder_inverse; parse_decoder] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `s : byte pstream` pstream_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `b0 : byte`
           (X_CHOOSE_THEN `s0 : byte pstream` SUBST_VAR_TAC)))) THENL
   [ASM_REWRITE_TAC [case_pstream_def; option_distinct];
    ASM_REWRITE_TAC [case_pstream_def; option_distinct];
    ALL_TAC] THEN
   REWRITE_TAC [case_pstream_def; decoder_parse_def] THEN
   MP_TAC (SPEC `b0 : byte` byte_list_cases) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `b00 : bool`
       (X_CHOOSE_THEN `b01 : bool`
         (X_CHOOSE_THEN `b02 : bool`
           (X_CHOOSE_THEN `b03 : bool`
             (X_CHOOSE_THEN `b04 : bool`
               (X_CHOOSE_THEN `b05 : bool`
                 (X_CHOOSE_THEN `b06 : bool`
                   (X_CHOOSE_THEN `b07 : bool`
                      SUBST_VAR_TAC)))))))) THEN
   bit_blast_tac THEN
   BOOL_CASES_TAC `b07 : bool` THENL
   [REWRITE_TAC [] THEN
    BOOL_CASES_TAC `b06 : bool` THENL
    [REWRITE_TAC [] THEN
     BOOL_CASES_TAC `b05 : bool` THENL
     [REWRITE_TAC [] THEN
      BOOL_CASES_TAC `b04 : bool` THENL
      [REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b03 : bool` THENL
       [REWRITE_TAC [option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC
         [parse_parse_partial_map; parse_parse_some; parse_cont3_def;
          parse_parse_pair; parse_cont2_def; parse_cont_def;
          case_option_def; case_pstream_def; is_cont_def] THEN
       MP_TAC (ISPEC `s0 : byte pstream` pstream_cases) THEN
       DISCH_THEN
         (DISJ_CASES_THEN2 SUBST_VAR_TAC
           (DISJ_CASES_THEN2 SUBST_VAR_TAC
              (X_CHOOSE_THEN `b1 : byte`
                (X_CHOOSE_THEN `s1 : byte pstream` SUBST_VAR_TAC)))) THENL
       [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_pstream_def] THEN
       MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
       DISCH_THEN
         (X_CHOOSE_THEN `b10 : bool`
           (X_CHOOSE_THEN `b11 : bool`
             (X_CHOOSE_THEN `b12 : bool`
               (X_CHOOSE_THEN `b13 : bool`
                 (X_CHOOSE_THEN `b14 : bool`
                   (X_CHOOSE_THEN `b15 : bool`
                     (X_CHOOSE_THEN `b16 : bool`
                       (X_CHOOSE_THEN `b17 : bool`
                          SUBST_VAR_TAC)))))))) THEN
       bit_blast_tac THEN
       BOOL_CASES_TAC' `b17 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b16 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_option_def] THEN
       MP_TAC (ISPEC `s1 : byte pstream` pstream_cases) THEN
       DISCH_THEN
         (DISJ_CASES_THEN2 SUBST_VAR_TAC
           (DISJ_CASES_THEN2 SUBST_VAR_TAC
              (X_CHOOSE_THEN `b2 : byte`
                (X_CHOOSE_THEN `s2 : byte pstream` SUBST_VAR_TAC)))) THENL
       [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_pstream_def] THEN
       MP_TAC (SPEC `b2 : byte` byte_list_cases) THEN
       DISCH_THEN
         (X_CHOOSE_THEN `b20 : bool`
           (X_CHOOSE_THEN `b21 : bool`
             (X_CHOOSE_THEN `b22 : bool`
               (X_CHOOSE_THEN `b23 : bool`
                 (X_CHOOSE_THEN `b24 : bool`
                   (X_CHOOSE_THEN `b25 : bool`
                     (X_CHOOSE_THEN `b26 : bool`
                       (X_CHOOSE_THEN `b27 : bool`
                          SUBST_VAR_TAC)))))))) THEN
       bit_blast_tac THEN
       BOOL_CASES_TAC' `b27 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b26 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_option_def] THEN
       MP_TAC (ISPEC `s2 : byte pstream` pstream_cases) THEN
       DISCH_THEN
         (DISJ_CASES_THEN2 SUBST_VAR_TAC
           (DISJ_CASES_THEN2 SUBST_VAR_TAC
              (X_CHOOSE_THEN `b3 : byte`
                (X_CHOOSE_THEN `s3 : byte pstream` SUBST_VAR_TAC)))) THENL
       [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_pstream_def] THEN
       MP_TAC (SPEC `b3 : byte` byte_list_cases) THEN
       DISCH_THEN
         (X_CHOOSE_THEN `b30 : bool`
           (X_CHOOSE_THEN `b31 : bool`
             (X_CHOOSE_THEN `b32 : bool`
               (X_CHOOSE_THEN `b33 : bool`
                 (X_CHOOSE_THEN `b34 : bool`
                   (X_CHOOSE_THEN `b35 : bool`
                     (X_CHOOSE_THEN `b36 : bool`
                       (X_CHOOSE_THEN `b37 : bool`
                          SUBST_VAR_TAC)))))))) THEN
       bit_blast_tac THEN
       BOOL_CASES_TAC' `b37 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b36 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_option_def] THEN
       REWRITE_TAC [decode_cont3_def] THEN
       bit_blast_tac THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       bit_blast_tac THEN
       CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       REWRITE_TAC [case_option_def; option_distinct] THEN
       MATCH_MP_TAC
         (TAUT `!c b d. (~c ==> b ==> d) ==> (if c then F else b) ==> d`) THEN
       STRIP_TAC THEN
       SUBGOAL_THEN `b02 <=> ~b01 /\ ~b00 /\ ~b15 /\ ~b14`
         (fun th -> POP_ASSUM (K ALL_TAC) THEN SUBST_VAR_TAC th) THENL
       [POP_ASSUM MP_TAC THEN
        BOOL_CASES_TAC `b02 : bool` THEN
        REWRITE_TAC [DE_MORGAN_THM] THEN
        STRIP_TAC THEN
        ASM_REWRITE_TAC [];
        ALL_TAC] THEN
       REWRITE_TAC [option_inj; PAIR_EQ] THEN
       STRIP_TAC THEN
       POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
       POP_ASSUM SUBST_VAR_TAC THEN
       REWRITE_TAC [encoder_def] THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       KNOW_TAC
         `!x y f (z : byte pstream).
            dest_unicode (mk_unicode y) = y /\ x = append_pstream (f y) z ==>
            x = append_pstream (f (dest_unicode (mk_unicode y))) z` THENL
       [SIMP_TAC [];
        ALL_TAC] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       REWRITE_TAC [GSYM unicode_rep_abs] THEN
       KNOW_TAC
         `!x y z.
            is_plane x /\
            (is_plane x ==>
             is_unicode (mk_plane x, mk_position y) /\ z) ==>
            is_unicode (mk_plane x, mk_position y) /\ z` THENL
       [SIMP_TAC [];
        ALL_TAC] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       CONJ_TAC THENL
       [REWRITE_TAC [is_plane_def] THEN
        bit_blast_tac;
        ALL_TAC] THEN
       REWRITE_TAC [is_unicode_def; position_tybij] THEN
       DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_tybij] th]) THEN
       SUBGOAL_THEN
         `(list_to_byte
             [b14; b15; b00; b01; ~b01 /\ ~b00 /\ ~b15 /\ ~b14; F; F; F] =
           num_to_byte 0) <=> F` ASSUME_TAC THENL
       [bit_blast_tac THEN
        TAUT_TAC;
        ALL_TAC] THEN
       CONJ_TAC THENL
       [ASM_REWRITE_TAC [LET_DEF; LET_END_DEF];
        ALL_TAC] THEN
       POP_ASSUM SUBST1_TAC THEN
       REWRITE_TAC [] THEN
       SPEC_TAC (`~b01 /\ ~b00 /\ ~b15 /\ ~b14`, `b02 : bool`) THEN
       GEN_TAC THEN
       bit_blast_tac THEN
       REWRITE_TAC [encode_cont3_def] THEN
       bit_blast_tac THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       bit_blast_tac THEN
       REWRITE_TAC [append_pstream_def];
       REWRITE_TAC
         [parse_parse_partial_map; parse_parse_some; parse_cont3_def;
          parse_parse_pair; parse_cont2_def; parse_cont_def;
          case_option_def; case_pstream_def; is_cont_def] THEN
       MP_TAC (ISPEC `s0 : byte pstream` pstream_cases) THEN
       DISCH_THEN
         (DISJ_CASES_THEN2 SUBST_VAR_TAC
           (DISJ_CASES_THEN2 SUBST_VAR_TAC
              (X_CHOOSE_THEN `b1 : byte`
                (X_CHOOSE_THEN `s1 : byte pstream` SUBST_VAR_TAC)))) THENL
       [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_pstream_def] THEN
       MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
       DISCH_THEN
         (X_CHOOSE_THEN `b10 : bool`
           (X_CHOOSE_THEN `b11 : bool`
             (X_CHOOSE_THEN `b12 : bool`
               (X_CHOOSE_THEN `b13 : bool`
                 (X_CHOOSE_THEN `b14 : bool`
                   (X_CHOOSE_THEN `b15 : bool`
                     (X_CHOOSE_THEN `b16 : bool`
                       (X_CHOOSE_THEN `b17 : bool`
                          SUBST_VAR_TAC)))))))) THEN
       bit_blast_tac THEN
       BOOL_CASES_TAC' `b17 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b16 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_option_def] THEN
       MP_TAC (ISPEC `s1 : byte pstream` pstream_cases) THEN
       DISCH_THEN
         (DISJ_CASES_THEN2 SUBST_VAR_TAC
           (DISJ_CASES_THEN2 SUBST_VAR_TAC
              (X_CHOOSE_THEN `b2 : byte`
                (X_CHOOSE_THEN `s2 : byte pstream` SUBST_VAR_TAC)))) THENL
       [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_pstream_def] THEN
       MP_TAC (SPEC `b2 : byte` byte_list_cases) THEN
       DISCH_THEN
         (X_CHOOSE_THEN `b20 : bool`
           (X_CHOOSE_THEN `b21 : bool`
             (X_CHOOSE_THEN `b22 : bool`
               (X_CHOOSE_THEN `b23 : bool`
                 (X_CHOOSE_THEN `b24 : bool`
                   (X_CHOOSE_THEN `b25 : bool`
                     (X_CHOOSE_THEN `b26 : bool`
                       (X_CHOOSE_THEN `b27 : bool`
                          SUBST_VAR_TAC)))))))) THEN
       bit_blast_tac THEN
       BOOL_CASES_TAC' `b27 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [] THEN
       BOOL_CASES_TAC `b26 : bool` THENL
       [REWRITE_TAC [case_option_def; option_distinct];
        ALL_TAC] THEN
       REWRITE_TAC [case_option_def] THEN
       REWRITE_TAC [decode_cont2_def] THEN
       bit_blast_tac THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       bit_blast_tac THEN
       CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       REWRITE_TAC [case_option_def; option_distinct] THEN
       MATCH_MP_TAC
         (TAUT `!c b d. (~c ==> b ==> d) ==> (if c then F else b) ==> d`) THEN
       STRIP_TAC THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       REWRITE_TAC [case_option_def; option_distinct] THEN
       MATCH_MP_TAC
         (TAUT `!c b d. (~c ==> b ==> d) ==> (if c then F else b) ==> d`) THEN
       STRIP_TAC THEN
       REWRITE_TAC [option_inj; PAIR_EQ] THEN
       STRIP_TAC THEN
       POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
       POP_ASSUM SUBST_VAR_TAC THEN
       REWRITE_TAC [encoder_def] THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       KNOW_TAC
         `!x y f (z : byte pstream).
            dest_unicode (mk_unicode y) = y /\ x = append_pstream (f y) z ==>
            x = append_pstream (f (dest_unicode (mk_unicode y))) z` THENL
       [SIMP_TAC [];
        ALL_TAC] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       REWRITE_TAC [GSYM unicode_rep_abs] THEN
       KNOW_TAC
         `!x y z.
            is_plane x /\
            (is_plane x ==>
             is_unicode (mk_plane x, mk_position y) /\ z) ==>
            is_unicode (mk_plane x, mk_position y) /\ z` THENL
       [SIMP_TAC [];
        ALL_TAC] THEN
       DISCH_THEN MATCH_MP_TAC THEN
       CONJ_TAC THENL
       [REWRITE_TAC [is_plane_def] THEN
        bit_blast_tac;
        ALL_TAC] THEN
       REWRITE_TAC [is_unicode_def; position_tybij] THEN
       DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_tybij] th]) THEN
       CONJ_TAC THENL
       [REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
        DISJ2_TAC THEN
        bit_blast_tac THEN
        ASM_TAUT_TAC;
        ALL_TAC] THEN
       bit_blast_tac THEN
       REWRITE_TAC [] THEN
       bit_blast_tac THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       ONCE_REWRITE_TAC [COND_RATOR] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       MATCH_MP_TAC (TAUT `~X /\ Z ==> (if X then Y else Z)`) THEN
       CONJ_TAC THENL
       [ASM_TAUT_TAC;
        ALL_TAC] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       ONCE_REWRITE_TAC [COND_RATOR] THEN
       ONCE_REWRITE_TAC [COND_RAND] THEN
       MATCH_MP_TAC (TAUT `~X /\ Z ==> (if X then Y else Z)`) THEN
       CONJ_TAC THENL
       [ASM_TAUT_TAC;
        ALL_TAC] THEN
       REWRITE_TAC [encode_cont2_def] THEN
       bit_blast_tac THEN
       REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       bit_blast_tac THEN
       REWRITE_TAC [append_pstream_def]];
      REWRITE_TAC
        [parse_parse_partial_map; parse_parse_some; parse_cont3_def;
         parse_parse_pair; parse_cont2_def; parse_cont_def;
         case_option_def; case_pstream_def; is_cont_def] THEN
      MP_TAC (ISPEC `s0 : byte pstream` pstream_cases) THEN
      DISCH_THEN
        (DISJ_CASES_THEN2 SUBST_VAR_TAC
          (DISJ_CASES_THEN2 SUBST_VAR_TAC
             (X_CHOOSE_THEN `b1 : byte`
               (X_CHOOSE_THEN `s1 : byte pstream` SUBST_VAR_TAC)))) THENL
      [ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
       ASM_REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
       ALL_TAC] THEN
      REWRITE_TAC [case_pstream_def] THEN
      MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
      DISCH_THEN
        (X_CHOOSE_THEN `b10 : bool`
          (X_CHOOSE_THEN `b11 : bool`
            (X_CHOOSE_THEN `b12 : bool`
              (X_CHOOSE_THEN `b13 : bool`
                (X_CHOOSE_THEN `b14 : bool`
                  (X_CHOOSE_THEN `b15 : bool`
                    (X_CHOOSE_THEN `b16 : bool`
                      (X_CHOOSE_THEN `b17 : bool`
                         SUBST_VAR_TAC)))))))) THEN
      bit_blast_tac THEN
      BOOL_CASES_TAC' `b17 : bool` THENL
      [REWRITE_TAC [case_option_def; option_distinct];
       ALL_TAC] THEN
      REWRITE_TAC [] THEN
      BOOL_CASES_TAC `b16 : bool` THENL
      [REWRITE_TAC [case_option_def; option_distinct];
       ALL_TAC] THEN
      REWRITE_TAC [case_option_def] THEN
      REWRITE_TAC [decode_cont1_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      REWRITE_TAC [case_option_def; option_distinct] THEN
      MATCH_MP_TAC
        (TAUT `!c b d. (~c ==> b ==> d) ==> (if c then F else b) ==> d`) THEN
      STRIP_TAC THEN
      REWRITE_TAC [option_inj; PAIR_EQ] THEN
      STRIP_TAC THEN
      POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      REWRITE_TAC [encoder_def] THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      KNOW_TAC
        `!x y f (z : byte pstream).
           dest_unicode (mk_unicode y) = y /\ x = append_pstream (f y) z ==>
           x = append_pstream (f (dest_unicode (mk_unicode y))) z` THENL
      [SIMP_TAC [];
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC [GSYM unicode_rep_abs] THEN
      KNOW_TAC
        `!x y z.
           is_plane x /\
           (is_plane x ==>
            is_unicode (mk_plane x, mk_position y) /\ z) ==>
           is_unicode (mk_plane x, mk_position y) /\ z` THENL
      [SIMP_TAC [];
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
      [REWRITE_TAC [is_plane_def] THEN
       bit_blast_tac;
       ALL_TAC] THEN
      REWRITE_TAC [is_unicode_def; position_tybij] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_tybij] th]) THEN
      CONJ_TAC THENL
      [REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
       DISJ2_TAC THEN
       DISJ1_TAC THEN
       bit_blast_tac;
       ALL_TAC] THEN
      bit_blast_tac THEN
      REWRITE_TAC [] THEN
      bit_blast_tac THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      ONCE_REWRITE_TAC [COND_RATOR] THEN
      ONCE_REWRITE_TAC [COND_RAND] THEN
      MATCH_MP_TAC (TAUT `~X /\ Z ==> (if X then Y else Z)`) THEN
      CONJ_TAC THENL
      [ASM_TAUT_TAC;
       ALL_TAC] THEN
      REWRITE_TAC [encode_cont1_def] THEN
      bit_blast_tac THEN
      REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
      bit_blast_tac THEN
      REWRITE_TAC [append_pstream_def]];
     REWRITE_TAC [option_distinct]];
    REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    REWRITE_TAC [option_inj; PAIR_EQ] THEN
    STRIP_TAC THEN
    POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [encoder_def] THEN
    REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
    KNOW_TAC
      `!x y f (z : byte pstream).
         dest_unicode (mk_unicode y) = y /\ x = append_pstream (f y) z ==>
         x = append_pstream (f (dest_unicode (mk_unicode y))) z` THENL
    [SIMP_TAC [];
     ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC [GSYM unicode_rep_abs] THEN
    KNOW_TAC
      `!x y z.
         is_plane x /\
         (is_plane x ==>
          is_unicode (mk_plane x, mk_position y) /\ z) ==>
         is_unicode (mk_plane x, mk_position y) /\ z` THENL
    [SIMP_TAC [];
     ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL
    [REWRITE_TAC [is_plane_def] THEN
     bit_blast_tac;
     ALL_TAC] THEN
    REWRITE_TAC [is_unicode_def; position_tybij] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_tybij] th]) THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
     DISJ2_TAC THEN
     DISJ1_TAC THEN
     bit_blast_tac;
     ALL_TAC] THEN
    bit_blast_tac THEN
    REWRITE_TAC [] THEN
    bit_blast_tac THEN
    REWRITE_TAC [append_pstream_def]]);;

export_thm decoder_encoder_strong_inverse;;

let decode_encode = prove
  (`!cs. decode (encode cs) = SOME cs`,
   GEN_TAC THEN
   REWRITE_TAC [decode_def; encode_def; decode_pstream_def] THEN
   REWRITE_TAC [GSYM list_to_pstream_to_list] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC parse_pstream_inverse THEN
   ACCEPT_TAC decoder_encoder_inverse);;

export_thm decode_encode;;

let encode_decode = prove
  (`!bs. case_option T (\cs. encode cs = bs) (decode bs)`,
   GEN_TAC THEN
   REWRITE_TAC [decode_def; encode_def; decode_pstream_def] THEN
   MP_TAC (ISPECL [`decoder`; `encoder`; `list_to_pstream (bs : byte list)`]
                  parse_pstream_strong_inverse) THEN
   COND_TAC THENL
   [ACCEPT_TAC decoder_encoder_strong_inverse;
    ALL_TAC] THEN
   REWRITE_TAC [list_to_pstream_to_list; option_inj] THEN
   DISCH_THEN (ACCEPT_TAC o ONCE_REWRITE_RULE [EQ_SYM_EQ]));;

export_thm encode_decode;;

let decode_pstream_length = prove
  (`!bs. length_pstream (decode_pstream bs) <= length_pstream bs`,
   GEN_TAC THEN
   REWRITE_TAC [decode_pstream_def] THEN
   MATCH_ACCEPT_TAC parse_pstream_length);;

export_thm decode_pstream_length;;

let decode_length = prove
  (`!bs. case_option T (\cs. LENGTH cs <= LENGTH bs) (decode bs)`,
   GEN_TAC THEN
   REWRITE_TAC [decode_def] THEN
   REWRITE_TAC [GSYM list_to_pstream_length] THEN
   SPEC_TAC (`list_to_pstream (bs : byte list)`, `bs : byte pstream`) THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `pstream_to_list (decode_pstream bs)` option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   MP_TAC (ISPEC `decode_pstream bs` pstream_to_list_length) THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th; list_to_pstream_length]) THEN
   MATCH_ACCEPT_TAC decode_pstream_length);;

export_thm decode_length;;

let encode_length = prove
  (`!cs. LENGTH cs <= LENGTH (encode cs)`,
   GEN_TAC THEN
   MP_TAC (SPEC `encode cs` decode_length) THEN
   REWRITE_TAC [decode_encode; case_option_def]);;

export_thm encode_length;;

logfile_end ();;

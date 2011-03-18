(* ------------------------------------------------------------------------- *)
(* A type of 16-bit words.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "word16-def";;

let word16_width_def = new_definition
  `word16_width = 16`;;

export_thm word16_width_def;;

logfile_end ();;

(* Parametric theory instantiation: word *)

loads "opentheory/examples/word16-word.ml";;

let bit_blast_conv =
    DEPTH_CONV
      (word16_bit_conv ORELSEC
       byte_bit_conv ORELSEC
       list_bit_conv ORELSEC
       bool_simp_conv);;

let bit_blast_tac = CONV_TAC bit_blast_conv;;

logfile "word16-bits";;

let word16_list_cases = prove
  (`!w. ?x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
      w = list_to_word16 [x0; x1; x2; x3; x4; x5; x6; x7;
                          x8; x9; x10; x11; x12; x13; x14; x15]`,
   GEN_TAC THEN
   CONV_TAC
     (funpow 16 (RAND_CONV o ABS_CONV)
        (LAND_CONV (ONCE_REWRITE_CONV [GSYM word16_to_list_to_word16]))) THEN
   KNOW_TAC
     `LENGTH (word16_to_list w) =
      SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC
        (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0)))))))))))))))` THENL
   [REWRITE_TAC [length_word16_to_list; word16_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   SPEC_TAC (`word16_to_list w`, `l : bool list`) THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `HD (l : bool list)` THEN
   EXISTS_TAC `HD (TL (l : bool list))` THEN
   EXISTS_TAC `HD (TL (TL (l : bool list)))` THEN
   EXISTS_TAC `HD (TL (TL (TL (l : bool list))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (l : bool list)))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (l : bool list))))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (TL (l : bool list)))))))` THEN
   EXISTS_TAC `HD (TL (TL (TL (TL (TL (TL (TL (l : bool list))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (l : bool list)))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (l : bool list))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list)))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list))))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list)))))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list))))))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list)))))))))))))))` THEN
   EXISTS_TAC
     `HD (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL (TL
        (l : bool list))))))))))))))))` THEN
   AP_TERM_TAC THEN
   POP_ASSUM MP_TAC THEN
   N_TAC 16
     (MP_TAC (ISPEC `l : bool list` list_CASES) THEN
      STRIP_TAC THENL
      [ASM_REWRITE_TAC [LENGTH; NOT_SUC];
       ALL_TAC] THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      REWRITE_TAC [LENGTH; SUC_INJ; HD; TL; CONS_11] THEN
      SPEC_TAC (`t : bool list`, `l : bool list`) THEN
      GEN_TAC) THEN
   REWRITE_TAC [LENGTH_EQ_NIL]);;

export_thm word16_list_cases;;

logfile "word16-bytes-def";;

let word16_to_bytes_def = new_definition
  `!w.
     word16_to_bytes w =
     (num_to_byte (word16_to_num (word16_shr w 8)),
      num_to_byte (word16_to_num (word16_and w (num_to_word16 255))))`;;

export_thm word16_to_bytes_def;;

let bytes_to_word16_def = new_definition
  `!b1 b2.
     bytes_to_word16 b1 b2 =
     word16_or
       (word16_shl (num_to_word16 (byte_to_num b1)) 8)
       (num_to_word16 (byte_to_num b2))`;;

export_thm bytes_to_word16_def;;

logfile "word16-bytes-thm";;

let byte_to_word16_list = prove
  (`!b. num_to_word16 (byte_to_num b) = list_to_word16 (byte_to_list b)`,
   GEN_TAC THEN
   MATCH_MP_TAC word16_eq_bits THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [list_to_word16_bit] THEN
   REWRITE_TAC [word16_bit_div; num_to_word16_to_num] THEN
   REWRITE_TAC [word16_size_def; mod_div_exp_2] THEN
   ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   REWRITE_TAC [odd_mod_exp_2] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `i < byte_width /\ i < LENGTH (byte_to_list b) /\
      EL i (byte_to_list b)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM list_to_byte_bit; byte_to_list_to_byte] THEN
    REWRITE_TAC [byte_bit_div] THEN
    MATCH_MP_TAC (ITAUT `x ==> (y /\ x <=> y)`) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC [length_byte_to_list; CONJ_ASSOC]]);;

export_thm byte_to_word16_list;;

let word16_to_byte_list = prove
  (`!w. num_to_byte (word16_to_num w) = list_to_byte (word16_to_list w)`,
   GEN_TAC THEN
   MATCH_MP_TAC byte_eq_bits THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [list_to_byte_bit] THEN
   REWRITE_TAC [byte_bit_div; num_to_byte_to_num] THEN
   REWRITE_TAC [byte_size_def; mod_div_exp_2] THEN
   ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   REWRITE_TAC [odd_mod_exp_2] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `i < word16_width /\ i < LENGTH (word16_to_list w) /\
      EL i (word16_to_list w)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM list_to_word16_bit; word16_to_list_to_word16] THEN
    REWRITE_TAC [word16_bit_div] THEN
    MATCH_MP_TAC (ITAUT `x ==> (y /\ x <=> y)`) THEN
    ASM_ARITH_TAC;
    REWRITE_TAC [length_word16_to_list; CONJ_ASSOC]]);;

export_thm word16_to_byte_list;;

let bytes_to_word16_list = prove
  (`!b0 b1.
      list_to_word16 (APPEND (byte_to_list b1) (byte_to_list b0)) =
      bytes_to_word16 b0 b1`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [bytes_to_word16_def; byte_to_word16_list] THEN
   MP_TAC (SPEC `b0 : byte` byte_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   MP_TAC (SPEC `b1 : byte` byte_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   bit_blast_tac);;

export_thm bytes_to_word16_list;;

let word16_to_bytes_list = prove
  (`!w.
      (list_to_byte (drop 8 (word16_to_list w)),
       list_to_byte (take 8 (word16_to_list w))) =
      word16_to_bytes w`,
   GEN_TAC THEN
   REWRITE_TAC [word16_to_bytes_def; word16_to_byte_list] THEN
   MP_TAC (SPEC `w : word16` word16_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   bit_blast_tac);;

export_thm word16_to_bytes_list;;

let bytes_to_word16_list_conv =
    let th = SYM (SPECL [`list_to_byte l0`; `list_to_byte l1`]
                    bytes_to_word16_list) in
    REWR_CONV th THENC
    RAND_CONV
      (RATOR_CONV (RAND_CONV list_to_byte_to_list_conv) THENC
       RAND_CONV list_to_byte_to_list_conv THENC
       append_conv);;

let word16_to_bytes_list_conv =
    let th = SYM (SPEC `list_to_word16 l` word16_to_bytes_list) in
    REWR_CONV th THENC
    (RATOR_CONV o RAND_CONV o RAND_CONV)
      (RAND_CONV list_to_word16_to_list_conv THENC
       drop_conv) THENC
    (RAND_CONV o RAND_CONV)
      (RAND_CONV list_to_word16_to_list_conv THENC
       take_conv);;

let word16_bytes_conv =
    bytes_to_word16_list_conv ORELSEC
    word16_to_bytes_list_conv;;

let bit_blast_conv =
    DEPTH_CONV
      (word16_bytes_conv ORELSEC
       word16_bit_conv ORELSEC
       byte_bit_conv ORELSEC
       list_bit_conv ORELSEC
       bool_simp_conv);;

let bit_blast_tac = CONV_TAC bit_blast_conv;;

let dest_bytes_to_word16_cases = prove
  (`!w. ?b0 b1. w = bytes_to_word16 b0 b1 /\ word16_to_bytes w = (b0,b1)`,
   GEN_TAC THEN
   EXISTS_TAC `FST (word16_to_bytes w)` THEN
   EXISTS_TAC `SND (word16_to_bytes w)` THEN
   REWRITE_TAC [] THEN
   REWRITE_TAC [word16_to_bytes_def; bytes_to_word16_def] THEN
   REWRITE_TAC [byte_to_word16_list; word16_to_byte_list] THEN
   MP_TAC (SPEC `w : word16` word16_list_cases) THEN
   STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   bit_blast_tac THEN
   REWRITE_TAC []);;

export_thm dest_bytes_to_word16_cases;;

let bytes_to_word16_cases = prove
  (`!w. ?b0 b1. w = bytes_to_word16 b0 b1`,
   GEN_TAC THEN
   MP_TAC (SPEC `w : word16` dest_bytes_to_word16_cases) THEN
   STRIP_TAC THEN
   EXISTS_TAC `b0 : byte` THEN
   EXISTS_TAC `b1 : byte` THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm bytes_to_word16_cases;;

logfile_end ();;

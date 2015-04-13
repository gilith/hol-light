(* ========================================================================= *)
(* UNICODE CHARACTERS                                                        *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Unicode characters.                                   *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/char/char.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Unicode characters.                                         *)
(* ------------------------------------------------------------------------- *)

logfile "char-def";;

let dest_plane_unicode_def = new_definition
  `!n. dest_plane_unicode n = bit_shr n 16`;;

export_thm dest_plane_unicode_def;;

let dest_position_unicode_def = new_definition
  `!n. dest_position_unicode n = bit_bound n 16`;;

export_thm dest_position_unicode_def;;

let is_unicode_def = new_definition
  `!n.
     is_unicode n =
     let pl = dest_plane_unicode n in
     let pos = dest_position_unicode n in
     pl < 17 /\
     pos < 65534 /\
     (pl = 0 ==>
      ~(55296 <= pos /\ pos < 57344) /\
      ~(64976 <= pos /\ pos < 65008))`;;

export_thm is_unicode_def;;

let unicode_exists = prove
  (`?n. is_unicode n`,
   EXISTS_TAC `0` THEN
   REWRITE_TAC
     [is_unicode_def; dest_plane_unicode_def; dest_position_unicode_def;
      zero_bit_shr; zero_bit_bound] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
   NUM_REDUCE_TAC);;

let (mk_dest_unicode,dest_mk_unicode) =
  let tybij =
    new_type_definition
      "unicode" ("mk_unicode","dest_unicode") unicode_exists in
  CONJ_PAIR tybij;;

export_thm mk_dest_unicode;;
export_thm dest_mk_unicode;;

let unicode_tybij = CONJ mk_dest_unicode dest_mk_unicode;;

let plane_unicode_def = new_definition
  `!c. plane_unicode c = dest_plane_unicode (dest_unicode c)`;;

export_thm plane_unicode_def;;

let position_unicode_def = new_definition
  `!c. position_unicode c = dest_position_unicode (dest_unicode c)`;;

export_thm position_unicode_def;;

let random_unicode_def = new_definition
  `!r.
     random_unicode r =
     let n0 = random_uniform 1111998 r in
     let n1 = if n0 < 55296 then n0 else n0 + 2048 in
     let pl = n1 DIV 65534 in
     let pos = n1 MOD 65534 in
     let n2 = pos + bit_shl pl 16 in
     mk_unicode n2`;;

export_thm random_unicode_def;;

(* ~~~~~~~ *)
(* Strings *)
(* ~~~~~~~ *)

new_type_abbrev("string",`:unicode list`);;

(* ------------------------------------------------------------------------- *)
(* Properties of Unicode characters.                                         *)
(* ------------------------------------------------------------------------- *)

logfile "char-thm";;

let unicode_cases = prove
 (`!c. ?n. is_unicode n /\ c = mk_unicode n`,
  GEN_TAC THEN
  EXISTS_TAC `dest_unicode c` THEN
  REWRITE_TAC [unicode_tybij]);;

export_thm unicode_cases;;

let dest_unicode_cases = prove
 (`!c. ?n. is_unicode n /\ c = mk_unicode n /\ dest_unicode c = n`,
  GEN_TAC THEN
  MP_TAC (SPEC `c : unicode` unicode_cases) THEN
  REWRITE_TAC [unicode_tybij] THEN
  STRIP_TAC THEN
  EXISTS_TAC `n : num` THEN
  ASM_REWRITE_TAC []);;

export_thm dest_unicode_cases;;

let dest_unicode_inj = prove
 (`!c1 c2. dest_unicode c1 = dest_unicode c2 <=> c1 = c2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM mk_dest_unicode] THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm dest_unicode_inj;;

let dest_plane_unicode_eq_zero = prove
 (`!n. (dest_plane_unicode n = 0) <=> n < 65536`,
  GEN_TAC THEN
  REWRITE_TAC
    [dest_plane_unicode_def; bit_shr_eq_zero; bit_width_upper_bound;
     NUM_REDUCE_CONV `2 EXP 16`]);;

export_thm dest_plane_unicode_eq_zero;;

let dest_plane_position_unicode = prove
 (`!c. dest_unicode c = position_unicode c + bit_shl (plane_unicode c) 16`,
  REWRITE_TAC
    [position_unicode_def; dest_position_unicode_def; plane_unicode_def;
     dest_plane_unicode_def; bit_bound]);;

export_thm dest_plane_position_unicode;;

let plane_unicode_bound = prove
 (`!c. plane_unicode c < 17`,
  GEN_TAC THEN
  MP_TAC (SPEC `c : unicode` dest_unicode_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [plane_unicode_def] THEN
  UNDISCH_TAC `is_unicode n` THEN
  REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC);;

export_thm plane_unicode_bound;;

let position_unicode_bound = prove
 (`!c. position_unicode c < 65534`,
  GEN_TAC THEN
  MP_TAC (SPEC `c : unicode` dest_unicode_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [position_unicode_def] THEN
  UNDISCH_TAC `is_unicode n` THEN
  REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
  STRIP_TAC);;

export_thm position_unicode_bound;;

let dest_unicode_bound = prove
 (`!c. dest_unicode c < 1114110`,
  GEN_TAC THEN
  REWRITE_TAC [dest_plane_position_unicode] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `65534 + bit_shl (plane_unicode c) 16` THEN
  REWRITE_TAC [LT_ADD_RCANCEL; position_unicode_bound] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `65534 + bit_shl 16 16` THEN
  REWRITE_TAC [LE_ADD_LCANCEL; bit_shl_mono_le] THEN
  CONJ_TAC THENL
  [REWRITE_TAC [GSYM LT_SUC_LE; NUM_REDUCE_CONV `SUC 16`; plane_unicode_bound];
   REWRITE_TAC [bit_shl_def] THEN
   NUM_REDUCE_TAC]);;

export_thm dest_unicode_bound;;

let is_unicode_bound = prove
 (`!n. is_unicode n ==> n < 1114110`,
  GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `n : num` dest_mk_unicode) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [dest_unicode_bound]);;

export_thm is_unicode_bound;;

let is_unicode_bit_width = prove
 (`!n. is_unicode n ==> bit_width n <= 21`,
  GEN_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC [bit_width_upper_bound] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `1114110` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC is_unicode_bound THEN
   ASM_REWRITE_TAC [];
   NUM_REDUCE_TAC]);;

export_thm is_unicode_bit_width;;

let finite_is_unicode = prove
 (`FINITE { n | is_unicode n }`,
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{ n | n < 1114110}` THEN
  REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM; is_unicode_bound]);;

export_thm finite_is_unicode;;

let image_is_unicode = prove
 (`IMAGE mk_unicode { n | is_unicode n } = UNIV`,
  REWRITE_TAC [EXTENSION] THEN
  X_GEN_TAC `c : unicode` THEN
  REWRITE_TAC [IN_UNIV; IN_IMAGE; IN_ELIM] THEN
  EXISTS_TAC `dest_unicode c` THEN
  REWRITE_TAC [unicode_tybij]);;

export_thm image_is_unicode;;

let finite_unicode = prove
 (`FINITE (UNIV : unicode set)`,
  REWRITE_TAC [SYM image_is_unicode] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_ACCEPT_TAC finite_is_unicode);;

export_thm finite_unicode;;

(* This is 1,112,064 valid code points minus 66 non-characters *)
let card_unicode_univ = prove
 (`CARD (UNIV : unicode set) = 1111998`,
  REWRITE_TAC [SYM image_is_unicode] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD { n | is_unicode n }` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_IMAGE_INJ THEN
   REWRITE_TAC [finite_is_unicode; IN_ELIM] THEN
   X_GEN_TAC `n1 : num` THEN
   X_GEN_TAC `n2 : num` THEN
   REWRITE_TAC [dest_mk_unicode] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `CARD { n | is_unicode n /\ dest_plane_unicode n = 0 } +
     CARD { n | is_unicode n /\ ~(dest_plane_unicode n = 0) }` THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `{ n | is_unicode n } =
      { n | is_unicode n /\ dest_plane_unicode n = 0 } UNION
      { n | is_unicode n /\ ~(dest_plane_unicode n = 0) }` SUBST1_TAC THENL
   [REWRITE_TAC [EXTENSION] THEN
    X_GEN_TAC `n : num` THEN
    REWRITE_TAC [IN_UNION; IN_ELIM] THEN
    BOOL_CASES_TAC `dest_plane_unicode n = 0` THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC CARD_UNION THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{ n | is_unicode n }` THEN
    REWRITE_TAC [finite_is_unicode; SUBSET; IN_ELIM] THEN
    X_GEN_TAC `n : num` THEN
    STRIP_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{ n | is_unicode n }` THEN
    REWRITE_TAC [finite_is_unicode; SUBSET; IN_ELIM] THEN
    X_GEN_TAC `n : num` THEN
    STRIP_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [DISJOINT; EXTENSION] THEN
   X_GEN_TAC `n : num` THEN
   REWRITE_TAC [IN_INTER; NOT_IN_EMPTY; IN_ELIM] THEN
   BOOL_CASES_TAC `dest_plane_unicode n = 0` THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `63454 +
     CARD { n | is_unicode n /\ ~(dest_plane_unicode n = 0) }` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   SUBGOAL_THEN
     `{ n | is_unicode n /\ dest_plane_unicode n = 0 } =
      { n | n < 55296 } UNION
      ({ n | n < 64976 } DIFF { n | n < 57344 }) UNION
      ({ n | n < 65534 } DIFF { n | n < 65008 })` SUBST1_TAC THENL
   [REWRITE_TAC [EXTENSION] THEN
    X_GEN_TAC `n : num` THEN
    REWRITE_TAC
      [IN_ELIM; IN_UNION; IN_DIFF; is_unicode_def; LET_DEF; LET_END_DEF] THEN
    REVERSE_TAC (ASM_CASES_TAC `dest_plane_unicode n = 0`) THENL
    [ASM_REWRITE_TAC [] THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [CONTRAPOS_THM; dest_plane_unicode_eq_zero] THEN
     STRIP_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `55296` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC;
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `64976` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC;
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `65534` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `dest_position_unicode n = n` SUBST1_TAC THENL
    [MP_TAC (SPECL [`n : num`; `16`] bit_bound) THEN
     ASM_REWRITE_TAC
       [GSYM dest_plane_unicode_def; GSYM dest_position_unicode_def;
        zero_bit_shl; ADD_0];
     ALL_TAC] THEN
    REWRITE_TAC [SYM (NUM_REDUCE_CONV `SUC 16`); LT_0] THEN
    REWRITE_TAC [DE_MORGAN_THM; NOT_LE] THEN
    ASM_CASES_TAC `n < 55296` THENL
    [ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `n < 64976` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `55296` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC;
      ALL_TAC] THEN
     SUBGOAL_THEN `n < 65534` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `55296` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `n < 57344` THENL
    [ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `n < 65008` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `57344` THEN
      ASM_REWRITE_TAC [] THEN
      NUM_REDUCE_TAC;
      ALL_TAC] THEN
     ASM_REWRITE_TAC [DE_MORGAN_THM];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `n < 64976` THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `64976` THEN
     ASM_REWRITE_TAC [] THEN
     NUM_REDUCE_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD { n | n < 55296 } +
      CARD (({ n | n < 64976 } DIFF { n | n < 57344 }) UNION
            ({ n | n < 65534 } DIFF { n | n < 65008 }))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN
    CONJ_TAC THENL
    [REWRITE_TAC [FINITE_NUMSEG_LT];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [REWRITE_TAC [FINITE_UNION] THEN
     CONJ_TAC THEN
     MATCH_MP_TAC FINITE_DIFF THEN
     REWRITE_TAC [FINITE_NUMSEG_LT];
     ALL_TAC] THEN
    REWRITE_TAC
      [DISJOINT; EXTENSION; IN_INTER; IN_DIFF; IN_UNION; NOT_IN_EMPTY;
       IN_ELIM; DE_MORGAN_THM] THEN
    X_GEN_TAC `n : num` THEN
    REVERSE_TAC (ASM_CASES_TAC `n < 55296`) THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `n < 57344` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `55296` THEN
     ASM_REWRITE_TAC [] THEN
     NUM_REDUCE_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `n < 65008` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `55296` THEN
     ASM_REWRITE_TAC [] THEN
     NUM_REDUCE_TAC;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD { n | n < 55296 } +
      (CARD ({ n | n < 64976 } DIFF { n | n < 57344 }) +
       CARD ({ n | n < 65534 } DIFF { n | n < 65008 }))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EQ_ADD_LCANCEL] THEN
    MATCH_MP_TAC CARD_UNION THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_DIFF THEN
     REWRITE_TAC [FINITE_NUMSEG_LT];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_DIFF THEN
     REWRITE_TAC [FINITE_NUMSEG_LT];
     ALL_TAC] THEN
    REWRITE_TAC
      [DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY; IN_ELIM;
       DE_MORGAN_THM] THEN
    X_GEN_TAC `n : num` THEN
    ASM_CASES_TAC `n < 65008` THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    DISJ1_TAC THEN
    DISJ1_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [CONTRAPOS_THM] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `64976` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   MP_TAC (ISPECL [`{n | n < 64976}`; `{n | n < 57344}`] CARD_DIFF) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM] THEN
    X_GEN_TAC `n : num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `57344` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (ISPECL [`{n | n < 65534}`; `{n | n < 65008}`] CARD_DIFF) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM] THEN
    X_GEN_TAC `n : num` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `65008` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [CARD_NUMSEG_LT] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `CARD {n | is_unicode n /\ ~(dest_plane_unicode n = 0)} = 16 * 65534`
    (fun th -> SUBST1_TAC th THEN NUM_REDUCE_TAC) THEN
  SUBGOAL_THEN
    `{n | is_unicode n /\ ~(dest_plane_unicode n = 0)} =
     IMAGE (\(pl,pos). pos + bit_shl pl 16)
       ({pl | ~(pl = 0) /\ pl < 17} CROSS {pos | pos < 65534})`
    SUBST1_TAC THENL
  [REWRITE_TAC [EXTENSION; IN_ELIM; IN_IMAGE; EXISTS_PAIR_THM; IN_CROSS] THEN
   X_GEN_TAC `n : num` THEN
   REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
   ASM_CASES_TAC `dest_plane_unicode n = 0` THENL
   [ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
    X_GEN_TAC `pl : num` THEN
    X_GEN_TAC `pos : num` THEN
    POP_ASSUM MP_TAC THEN
    CONV_TAC (REWR_CONV (GSYM CONTRAPOS_THM)) THEN
    REWRITE_TAC [dest_plane_unicode_def] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [add_bit_shr; ADD_EQ_0];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `dest_plane_unicode n` THEN
    EXISTS_TAC `dest_position_unicode n` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [dest_position_unicode_def; dest_plane_unicode_def; bit_bound];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `pl : num`
       (X_CHOOSE_THEN `pos : num` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC
     [dest_position_unicode_def; dest_plane_unicode_def; add_bit_shr;
      add_bit_bound] THEN
   SUBGOAL_THEN `bit_bound pos 16 = pos` ASSUME_TAC THENL
   [MP_TAC (SPECL [`pos : num`; `16`] bit_bound) THEN
    DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC [EQ_ADD_LCANCEL_0; bit_shl_eq_zero; bit_shr_eq_zero] THEN
    CONV_TAC (RAND_CONV (REWR_CONV (SYM (SPEC `16` bit_width_ones)))) THEN
    MATCH_MP_TAC bit_width_mono THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `65534` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [bit_shr_bound; ZERO_ADD];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `CARD ({pl | ~(pl = 0) /\ pl < 17} CROSS {pos | pos < 65534})` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_IMAGE_INJ THEN
   REVERSE_TAC CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_CROSS THEN
    REWRITE_TAC [FINITE_NUMSEG_LT] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{pl | pl < 17}` THEN
    REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM] THEN
    REPEAT STRIP_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [FORALL_PAIR_THM; IN_CROSS; IN_ELIM; PAIR_EQ] THEN
   X_GEN_TAC `pl1 : num` THEN
   X_GEN_TAC `pos1 : num` THEN
   X_GEN_TAC `pl2 : num` THEN
   X_GEN_TAC `pos2 : num` THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `bit_bound pos1 16 = pos1` ASSUME_TAC THENL
   [MP_TAC (SPECL [`pos1 : num`; `16`] bit_bound) THEN
    DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC [EQ_ADD_LCANCEL_0; bit_shl_eq_zero; bit_shr_eq_zero] THEN
    CONV_TAC (RAND_CONV (REWR_CONV (SYM (SPEC `16` bit_width_ones)))) THEN
    MATCH_MP_TAC bit_width_mono THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `65534` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `bit_bound pos2 16 = pos2` ASSUME_TAC THENL
   [MP_TAC (SPECL [`pos2 : num`; `16`] bit_bound) THEN
    DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC [EQ_ADD_LCANCEL_0; bit_shl_eq_zero; bit_shr_eq_zero] THEN
    CONV_TAC (RAND_CONV (REWR_CONV (SYM (SPEC `16` bit_width_ones)))) THEN
    MATCH_MP_TAC bit_width_mono THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `65534` THEN
    ASM_REWRITE_TAC [] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `bit_shr (pos1 + bit_shl pl1 16) 16 = bit_shr (pos2 + bit_shl pl2 16) 16`
      MP_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [add_bit_shr; bit_shr_bound; ZERO_ADD];
    SUBGOAL_THEN
      `bit_bound (pos1 + bit_shl pl1 16) 16 =
       bit_bound (pos2 + bit_shl pl2 16) 16`
      MP_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC [add_bit_bound] THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `CARD {pl | ~(pl = 0) /\ pl < 17} * CARD {pos | pos < 65534}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_CROSS THEN
   REWRITE_TAC [FINITE_NUMSEG_LT] THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{pl | pl < 17}` THEN
   REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_ELIM] THEN
   REPEAT STRIP_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [CARD_NUMSEG_LT; EQ_MULT_RCANCEL] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN
    `{pl | ~(pl = 0) /\ pl < 17} = {pl | pl < 17} DIFF {0}`
    SUBST1_TAC THENL
  [REWRITE_TAC [EXTENSION; IN_SING; IN_ELIM; IN_DIFF] THEN
   X_GEN_TAC `pl : num` THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {pl | pl < 17} - CARD {0}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_DIFF THEN
   REWRITE_TAC [FINITE_NUMSEG_LT; SUBSET; IN_SING; IN_ELIM] THEN
   X_GEN_TAC `pl : num` THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [CARD_NUMSEG_LT; CARD_SING] THEN
  NUM_REDUCE_TAC);;

export_thm card_unicode_univ;;

let is_unicode_src = prove
 (`!n.
     is_unicode n =
     let pl = dest_plane_unicode n in
     let pos = dest_position_unicode n in
     pos < 65534 /\
     if ~(pl = 0) then pl < 17 else
     ~(55296 <= pos /\ pos < 57344) /\
     ~(64976 <= pos /\ pos < 65008)`,
  GEN_TAC THEN
  REWRITE_TAC [is_unicode_def; LET_DEF; LET_END_DEF] THEN
  ASM_CASES_TAC `dest_position_unicode n < 65534` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_CASES_TAC `dest_plane_unicode n = 0` THEN
  ASM_REWRITE_TAC [LT_NZ; SYM (NUM_REDUCE_CONV `SUC 16`); NOT_SUC]);;

export_thm is_unicode_src;;

let plane_unicode_src = prove
 (`plane_unicode = dest_plane_unicode o dest_unicode`,
  REWRITE_TAC [FUN_EQ_THM; plane_unicode_def; o_THM]);;

export_thm plane_unicode_src;;

let position_unicode_src = prove
 (`position_unicode = dest_position_unicode o dest_unicode`,
  REWRITE_TAC [FUN_EQ_THM; position_unicode_def; o_THM]);;

export_thm position_unicode_src;;

(* ------------------------------------------------------------------------- *)
(* Definition of the UTF-8 encoding of Unicode characters.                   *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8-def";;

let encode_ascii_utf8_def = new_definition
  `!n. encode_ascii_utf8 n = [num_to_byte n]`;;

export_thm encode_ascii_utf8_def;;

let encode_two_byte_utf8_def = new_definition
  `!n.
     encode_two_byte_utf8 n =
     let n1 = bit_shr n 6 in
     let b0 = byte_or (num_to_byte 192) (num_to_byte n1) in
     let b1 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n 6)) in
     CONS b0 (CONS b1 [])`;;

export_thm encode_two_byte_utf8_def;;

let encode_three_byte_utf8_def = new_definition
  `!n.
     encode_three_byte_utf8 n =
     let n1 = bit_shr n 6 in
     let n2 = bit_shr n1 6 in
     let b0 = byte_or (num_to_byte 224) (num_to_byte n2) in
     let b1 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n1 6)) in
     let b2 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n 6)) in
     CONS b0 (CONS b1 (CONS b2 []))`;;

export_thm encode_three_byte_utf8_def;;

let encode_four_byte_utf8_def = new_definition
  `!n.
     encode_four_byte_utf8 n =
     let n1 = bit_shr n 6 in
     let n2 = bit_shr n1 6 in
     let n3 = bit_shr n2 6 in
     let b0 = byte_or (num_to_byte 240) (num_to_byte n3) in
     let b1 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n2 6)) in
     let b2 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n1 6)) in
     let b3 = byte_or (num_to_byte 128) (num_to_byte (bit_bound n 6)) in
     CONS b0 (CONS b1 (CONS b2 (CONS b3 [])))`;;

export_thm encode_four_byte_utf8_def;;

let encode_unicode_utf8_def = new_definition
  `!c.
     encode_unicode_utf8 c =
     let n = dest_unicode c in
     if n < 128 then encode_ascii_utf8 n else
     if n < 2048 then encode_two_byte_utf8 n else
     if n < 65536 then encode_three_byte_utf8 n else
     encode_four_byte_utf8 n`;;

export_thm encode_unicode_utf8_def;;

let encode_utf8_def = new_definition
  `!c. encode_utf8 c = concat (MAP encode_unicode_utf8 c)`;;

export_thm encode_utf8_def;;

let reencode_unicode_utf8_def = new_definition
  `!x. reencode_unicode_utf8 x = case_sum (\b. [b]) (\c. encode_unicode_utf8 c) x`;;

export_thm reencode_unicode_utf8_def;;

let reencode_utf8_def = new_definition
  `!c. reencode_utf8 c = concat (MAP reencode_unicode_utf8 c)`;;

export_thm reencode_utf8_def;;

let parser_ascii_utf8_def = new_definition
  `parser_ascii_utf8 =
   parser_token (\b. if byte_bit b 7 then NONE else SOME (byte_to_num b))`;;

export_thm parser_ascii_utf8_def;;

let is_continuation_utf8_def = new_definition
  `!b. is_continuation_utf8 b <=> byte_bit b 7 /\ ~byte_bit b 6`;;

export_thm is_continuation_utf8_def;;

let add_continuation_utf8_def = new_definition
  `!b n.
     add_continuation_utf8 b n =
     if is_continuation_utf8 b then
       SOME (byte_to_num (byte_and b (num_to_byte 63)) + bit_shl n 6)
     else
       NONE`;;

export_thm add_continuation_utf8_def;;

let parser_two_byte_utf8_def = new_definition
  `!b.
     parser_two_byte_utf8 b =
     parser_filter
       (parser_foldn add_continuation_utf8 0
         (byte_to_num (byte_and b (num_to_byte 31))))
       (\n. 128 <= n)`;;

export_thm parser_two_byte_utf8_def;;

let parser_three_byte_utf8_def = new_definition
  `!b.
     parser_three_byte_utf8 b =
     parser_filter
       (parser_foldn add_continuation_utf8 1
          (byte_to_num (byte_and b (num_to_byte 15))))
       (\n. 2048 <= n)`;;

export_thm parser_three_byte_utf8_def;;

let parser_four_byte_utf8_def = new_definition
  `!b.
     parser_four_byte_utf8 b =
     parser_filter
       (parser_foldn add_continuation_utf8 2
          (byte_to_num (byte_and b (num_to_byte 7))))
       (\n. 65536 <= n)`;;

export_thm parser_four_byte_utf8_def;;

let parser_multibyte_utf8_def = new_definition
  `parser_multibyte_utf8 =
   parser_sequence
     (parser_token
        (\b.
           if byte_bit b 6 then
             if byte_bit b 5 then
               if byte_bit b 4 then
                 if byte_bit b 3 then NONE
                 else SOME (parser_four_byte_utf8 b)
               else SOME (parser_three_byte_utf8 b)
             else SOME (parser_two_byte_utf8 b)
           else NONE))`;;

export_thm parser_multibyte_utf8_def;;

let parser_num_utf8_def = new_definition
  `parser_num_utf8 =
   parser_orelse parser_ascii_utf8 parser_multibyte_utf8`;;

export_thm parser_num_utf8_def;;

let parser_unicode_utf8_def = new_definition
  `parser_unicode_utf8 =
   parser_map_partial
     parser_num_utf8
     (\n. if is_unicode n then SOME (mk_unicode n) else NONE)`;;

export_thm parser_unicode_utf8_def;;

let parser_utf8_def = new_definition
  `parser_utf8 =
   parser_orelse
     (parser_map parser_unicode_utf8 INR)
     (parser_map parser_any INL)`;;

export_thm parser_utf8_def;;

let decode_utf8_def = new_definition
  `!b.
     decode_utf8 b =
     FST (pstream_to_list (parse parser_utf8 (list_to_pstream b)))`;;

export_thm decode_utf8_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the UTF-8 encoding of Unicode characters.                   *)
(* ------------------------------------------------------------------------- *)

logfile "char-utf8-thm";;

let map_inl_reencode_utf8 = prove
 (`!b. reencode_utf8 (MAP INL b) = b`,
  REWRITE_TAC [reencode_utf8_def] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MAP; concat_def];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [MAP; concat_def] THEN
  REWRITE_TAC [reencode_unicode_utf8_def; case_sum_def; APPEND_SING]);;

export_thm map_inl_reencode_utf8;;

let map_inr_reencode_utf8 = prove
 (`!c. reencode_utf8 (MAP INR c) = encode_utf8 c`,
  REWRITE_TAC [reencode_utf8_def; encode_utf8_def] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MAP];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [MAP; concat_def] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [reencode_unicode_utf8_def; case_sum_def]);;

export_thm map_inr_reencode_utf8;;

let parser_ascii_utf8_encode_ascii = prove
 (`!n b.
     n < 128 ==>
     apply_parser parser_ascii_utf8 (append_pstream (encode_ascii_utf8 n) b) =
     SOME (n,b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (STRIP_ASSUME_TAC o
     REWRITE_RULE
       [GSYM bit_width_upper_bound; SYM (NUM_REDUCE_CONV `2 EXP 7`)]) THEN
  REWRITE_TAC
    [encode_ascii_utf8_def; parser_ascii_utf8_def; apply_parser_token;
     append_pstream_def; case_pstream_def; byte_bit_def;
     num_to_byte_to_num_bit_bound; bit_nth_bound] THEN
  SUBGOAL_THEN
    `bit_bound n 7 = n`
    ASSUME_TAC THENL
  [ASM_REWRITE_TAC [bit_bound_id];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_nth n 7 <=> F`
    SUBST1_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [bit_nth_bound; LT_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_bound n byte_width = n`
    SUBST1_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC
     [bit_bound_bound_min; byte_width_def; NUM_REDUCE_CONV `MIN 7 8`];
   ALL_TAC] THEN
  REWRITE_TAC [case_option_def]);;

export_thm parser_ascii_utf8_encode_ascii;;

let parser_ascii_utf8_encode_two_byte = prove
 (`!n b.
     apply_parser parser_ascii_utf8
       (append_pstream (encode_two_byte_utf8 n) b) =
     NONE`,
  REWRITE_TAC
    [encode_two_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_ascii_utf8_def; apply_parser_token; case_pstream_def;
     byte_bit_or; bit_blast_conv `byte_bit (num_to_byte 192) 7`;
     case_option_def]);;

export_thm parser_ascii_utf8_encode_two_byte;;

let parser_ascii_utf8_encode_three_byte = prove
 (`!n b.
     apply_parser parser_ascii_utf8
       (append_pstream (encode_three_byte_utf8 n) b) =
     NONE`,
  REWRITE_TAC
    [encode_three_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_ascii_utf8_def; apply_parser_token; case_pstream_def;
     byte_bit_or; bit_blast_conv `byte_bit (num_to_byte 224) 7`;
     case_option_def]);;

export_thm parser_ascii_utf8_encode_three_byte;;

let parser_ascii_utf8_encode_four_byte = prove
 (`!n b.
     apply_parser parser_ascii_utf8
       (append_pstream (encode_four_byte_utf8 n) b) =
     NONE`,
  REWRITE_TAC
    [encode_four_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_ascii_utf8_def; apply_parser_token; case_pstream_def;
     byte_bit_or; bit_blast_conv `byte_bit (num_to_byte 240) 7`;
     case_option_def]);;

export_thm parser_ascii_utf8_encode_four_byte;;

let is_continuation_utf8_bit_bound = prove
 (`!n.
     is_continuation_utf8
       (byte_or (num_to_byte 128) (num_to_byte (bit_bound n 6)))`,
  GEN_TAC THEN
  SUBGOAL_THEN `128 = bit_shl 1 7` SUBST1_TAC THENL
  [REWRITE_TAC [one_bit_shl] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [is_continuation_utf8_def; byte_bit_or] THEN
  REWRITE_TAC
    [byte_bit_def; num_to_byte_to_num_bit_bound; bit_nth_bound; LT_REFL;
     bit_nth_shl; SUB_REFL; LE_REFL; byte_width_def; bit_nth_zero; bit_hd_one;
     SYM (NUM_REDUCE_CONV `SUC 7`); SUC_LT] THEN
  NUM_REDUCE_TAC);;

export_thm is_continuation_utf8_bit_bound;;

let add_continuation_utf8_bit_bound = prove
 (`!n m.
     add_continuation_utf8
       (byte_or (num_to_byte 128) (num_to_byte (bit_bound n 6))) m =
     SOME (bit_bound n 6 + bit_shl m 6)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [add_continuation_utf8_def; is_continuation_utf8_bit_bound; option_inj;
     EQ_ADD_RCANCEL; byte_and_def; byte_or_def; num_to_byte_to_num_bit_bound;
     bit_bound_and; bit_bound_or; bit_bound_bound] THEN
  SUBGOAL_THEN `bit_bound 63 byte_width = 2 EXP 6 - 1` SUBST1_TAC THENL
  [REWRITE_TAC
     [SYM (NUM_REDUCE_CONV `2 EXP 6 - 1`); bit_bound_id; bit_width_ones;
      byte_width_def] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC
    [bit_and_ones; bit_bound_or; bit_bound_bound_min; byte_width_def;
     NUM_REDUCE_CONV `MIN 8 6`; MIN_REFL] THEN
  SUBGOAL_THEN `128 = bit_shl 2 6` SUBST1_TAC THENL
  [REWRITE_TAC [bit_shl_def] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [bit_bound_shl; zero_bit_or]);;

export_thm add_continuation_utf8_bit_bound;;

let parser_multibyte_utf8_encode_two_byte = prove
 (`!n b.
     128 <= n /\ n < 2048 ==>
     apply_parser parser_multibyte_utf8
       (append_pstream (encode_two_byte_utf8 n) b) =
     SOME (n,b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (STRIP_ASSUME_TAC o
     REWRITE_RULE
       [GSYM bit_width_upper_bound; SYM (NUM_REDUCE_CONV `2 EXP 11`)]) THEN
  REWRITE_TAC
    [encode_two_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_multibyte_utf8_def; apply_parser_sequence; apply_parser_token;
     case_pstream_def; byte_bit_or;
     bit_blast_conv `byte_bit (num_to_byte 192) 6`;
     bit_blast_conv `byte_bit (num_to_byte 192) 5`] THEN
  SUBGOAL_THEN `byte_bit (num_to_byte (bit_shr n 6)) 5 <=> F` SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_bit_def; num_to_byte_to_num_bit_bound; bit_nth_bound;
      DE_MORGAN_THM; GSYM bit_nth_add; NUM_REDUCE_CONV `6 + 5`] THEN
   DISJ2_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `11`] bit_nth_width) THEN
   ASM_REWRITE_TAC [NOT_LT];
   ALL_TAC] THEN
  REWRITE_TAC
    [case_option_def; parser_two_byte_utf8_def; apply_parser_filter;
     parser_foldn_def] THEN
  SUBGOAL_THEN
    `byte_to_num
       (byte_and (byte_or (num_to_byte 192) (num_to_byte (bit_shr n 6)))
          (num_to_byte 31)) =
     bit_shr n 6` SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_and_def; byte_or_def; num_to_byte_to_num_bit_bound;
      bit_bound_and; bit_bound_or; bit_bound_bound] THEN
   SUBGOAL_THEN `bit_bound 31 byte_width = 2 EXP 5 - 1` SUBST1_TAC THENL
   [REWRITE_TAC
      [SYM (NUM_REDUCE_CONV `2 EXP 5 - 1`); bit_bound_id; bit_width_ones;
       byte_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC
     [bit_and_ones; bit_bound_or; bit_bound_bound_min; byte_width_def;
      NUM_REDUCE_CONV `MIN 8 5`] THEN
   SUBGOAL_THEN `192 = bit_shl 6 5` SUBST1_TAC THENL
   [REWRITE_TAC [bit_shl_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [bit_bound_shl; zero_bit_or; bit_bound_id] THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   ASM_REWRITE_TAC [NUM_REDUCE_CONV `5 + 6`];
   ALL_TAC] THEN
  REWRITE_TAC [apply_parser_fold; case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  ASM_REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def]);;

export_thm parser_multibyte_utf8_encode_two_byte;;

let parser_multibyte_utf8_encode_three_byte = prove
 (`!n b.
     2048 <= n /\ n < 65536 ==>
     apply_parser parser_multibyte_utf8
       (append_pstream (encode_three_byte_utf8 n) b) =
     SOME (n,b)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN
    (STRIP_ASSUME_TAC o
     REWRITE_RULE
       [GSYM bit_width_upper_bound; SYM (NUM_REDUCE_CONV `2 EXP 16`)]) THEN
  REWRITE_TAC
    [encode_three_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_multibyte_utf8_def; apply_parser_sequence; apply_parser_token;
     case_pstream_def; byte_bit_or;
     bit_blast_conv `byte_bit (num_to_byte 224) 6`;
     bit_blast_conv `byte_bit (num_to_byte 224) 5`;
     bit_blast_conv `byte_bit (num_to_byte 224) 4`] THEN
  SUBGOAL_THEN
    `byte_bit (num_to_byte (bit_shr (bit_shr n 6) 6)) 4 <=> F`
    SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_bit_def; num_to_byte_to_num_bit_bound; bit_nth_bound;
      GSYM bit_shr_add; NUM_REDUCE_CONV `12 + 4`;
      DE_MORGAN_THM; GSYM bit_nth_add; NUM_REDUCE_CONV `6 + 6`] THEN
   DISJ2_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `16`] bit_nth_width) THEN
   ASM_REWRITE_TAC [NOT_LT];
   ALL_TAC] THEN
  REWRITE_TAC
    [case_option_def; parser_three_byte_utf8_def; apply_parser_filter;
     parser_foldn_def] THEN
  SUBGOAL_THEN
    `byte_to_num
       (byte_and
          (byte_or (num_to_byte 224) (num_to_byte (bit_shr (bit_shr n 6) 6)))
          (num_to_byte 15)) =
     bit_shr (bit_shr n 6) 6` SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_and_def; byte_or_def; num_to_byte_to_num_bit_bound;
      bit_bound_and; bit_bound_or; bit_bound_bound] THEN
   SUBGOAL_THEN `bit_bound 15 byte_width = 2 EXP 4 - 1` SUBST1_TAC THENL
   [REWRITE_TAC
      [SYM (NUM_REDUCE_CONV `2 EXP 4 - 1`); bit_bound_id; bit_width_ones;
       byte_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC
     [bit_and_ones; bit_bound_or; bit_bound_bound_min; byte_width_def;
      NUM_REDUCE_CONV `MIN 8 4`] THEN
   SUBGOAL_THEN `224 = bit_shl 14 4` SUBST1_TAC THENL
   [REWRITE_TAC [bit_shl_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [bit_bound_shl; zero_bit_or; bit_bound_id] THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   ASM_REWRITE_TAC [NUM_REDUCE_CONV `(4 + 6) + 6`];
   ALL_TAC] THEN
  REWRITE_TAC [apply_parser_fold; case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def; SUB_REFL; NUM_REDUCE_CONV `1 = 0`;
     case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  ASM_REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def]);;

export_thm parser_multibyte_utf8_encode_three_byte;;

let parser_multibyte_utf8_encode_four_byte = prove
 (`!n b.
     65536 <= n /\ bit_width n <= 21 ==>
     apply_parser parser_multibyte_utf8
       (append_pstream (encode_four_byte_utf8 n) b) =
     SOME (n,b)`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC
    [encode_four_byte_utf8_def; LET_DEF; LET_END_DEF; append_pstream_def;
     parser_multibyte_utf8_def; apply_parser_sequence; apply_parser_token;
     case_pstream_def; byte_bit_or;
     bit_blast_conv `byte_bit (num_to_byte 240) 6`;
     bit_blast_conv `byte_bit (num_to_byte 240) 5`;
     bit_blast_conv `byte_bit (num_to_byte 240) 4`;
     bit_blast_conv `byte_bit (num_to_byte 240) 3`] THEN
  SUBGOAL_THEN
    `byte_bit (num_to_byte (bit_shr (bit_shr (bit_shr n 6) 6) 6)) 3 <=> F`
    SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_bit_def; num_to_byte_to_num_bit_bound; bit_nth_bound;
      GSYM bit_shr_add; NUM_REDUCE_CONV `6 + 6`;
      NUM_REDUCE_CONV `6 + 12`; NUM_REDUCE_CONV `18 + 3`;
      DE_MORGAN_THM; GSYM bit_nth_add] THEN
   DISJ2_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `21`] bit_nth_width) THEN
   ASM_REWRITE_TAC [NOT_LT];
   ALL_TAC] THEN
  REWRITE_TAC
    [case_option_def; parser_four_byte_utf8_def; apply_parser_filter;
     parser_foldn_def] THEN
  SUBGOAL_THEN
    `byte_to_num
       (byte_and
          (byte_or (num_to_byte 240)
             (num_to_byte (bit_shr (bit_shr (bit_shr n 6) 6) 6)))
          (num_to_byte 7)) =
     bit_shr (bit_shr (bit_shr n 6) 6) 6` SUBST1_TAC THENL
  [REWRITE_TAC
     [byte_and_def; byte_or_def; num_to_byte_to_num_bit_bound;
      bit_bound_and; bit_bound_or; bit_bound_bound] THEN
   SUBGOAL_THEN `bit_bound 7 byte_width = 2 EXP 3 - 1` SUBST1_TAC THENL
   [REWRITE_TAC
      [SYM (NUM_REDUCE_CONV `2 EXP 3 - 1`); bit_bound_id; bit_width_ones;
       byte_width_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC
     [bit_and_ones; bit_bound_or; bit_bound_bound_min; byte_width_def;
      NUM_REDUCE_CONV `MIN 8 3`] THEN
   SUBGOAL_THEN `240 = bit_shl 30 3` SUBST1_TAC THENL
   [REWRITE_TAC [bit_shl_def] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [bit_bound_shl; zero_bit_or; bit_bound_id] THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   MATCH_MP_TAC bit_width_shr_le THEN
   ASM_REWRITE_TAC [NUM_REDUCE_CONV `((3 + 6) + 6) + 6`];
   ALL_TAC] THEN
  REWRITE_TAC [apply_parser_fold; case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def; NUM_REDUCE_CONV `2 = 0`;
     NUM_REDUCE_CONV `2 - 1`; case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def; NUM_REDUCE_CONV `1 = 0`;
     NUM_REDUCE_CONV `1 - 1`; case_pstream_def] THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  ASM_REWRITE_TAC
    [add_continuation_utf8_bit_bound; bit_bound; map_option_def;
     case_option_def; case_sum_def]);;

export_thm parser_multibyte_utf8_encode_four_byte;;

let parser_unicode_utf8_inverse = prove
 (`parser_inverse parser_unicode_utf8 encode_unicode_utf8`,
  REWRITE_TAC [parser_inverse_def] THEN
  X_GEN_TAC `c : unicode` THEN
  X_GEN_TAC `b : byte pstream` THEN
  MP_TAC (SPEC `c : unicode` dest_unicode_cases) THEN
  STRIP_TAC THEN
  UNDISCH_THEN `c = mk_unicode n` SUBST_VAR_TAC THEN
  ASM_REWRITE_TAC
    [encode_unicode_utf8_def; LET_DEF; LET_END_DEF; parser_unicode_utf8_def;
     apply_parser_map_partial; parser_num_utf8_def; apply_parser_orelse] THEN
  COND_CASES_TAC THENL
  [MP_TAC
     (SPECL [`n : num`; `b : byte pstream`]
        parser_ascii_utf8_encode_ascii) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [case_option_def];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `apply_parser parser_ascii_utf8
       (append_pstream
        (if n < 2048 then encode_two_byte_utf8 n else
         if n < 65536 then encode_three_byte_utf8 n else
         encode_four_byte_utf8 n) b) =
     NONE` SUBST1_TAC THENL
  [REPEAT COND_CASES_TAC THENL
   [REWRITE_TAC [parser_ascii_utf8_encode_two_byte];
    REWRITE_TAC [parser_ascii_utf8_encode_three_byte];
    REWRITE_TAC [parser_ascii_utf8_encode_four_byte]];
   ALL_TAC] THEN
  REWRITE_TAC [case_option_def] THEN
  COND_CASES_TAC THENL
  [MP_TAC
     (SPECL [`n : num`; `b : byte pstream`]
        parser_multibyte_utf8_encode_two_byte) THEN
   ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [case_option_def];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [MP_TAC
     (SPECL [`n : num`; `b : byte pstream`]
        parser_multibyte_utf8_encode_three_byte) THEN
   ASM_REWRITE_TAC [GSYM NOT_LT] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [case_option_def];
   ALL_TAC] THEN
  MP_TAC
    (SPECL [`n : num`; `b : byte pstream`]
       parser_multibyte_utf8_encode_four_byte) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [ASM_REWRITE_TAC [GSYM NOT_LT];
    MATCH_MP_TAC is_unicode_bit_width THEN
    ASM_REWRITE_TAC []];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [case_option_def]);;

export_thm parser_unicode_utf8_inverse;;

(***
let parser_unicode_utf8_strong_inverse = prove
 (`parser_strong_inverse parser_unicode_utf8 encode_unicode_utf8`,
  REWRITE_TAC [parser_strong_inverse_def; parser_unicode_utf8_inverse] THEN
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `xs : byte pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `b : byte`
          (X_CHOOSE_THEN `zs : byte pstream` SUBST_VAR_TAC)))) THENL
  [ASM_REWRITE_TAC [apply_parser_def; option_distinct];
   ASM_REWRITE_TAC [apply_parser_def; option_distinct];
   ALL_TAC] THEN
  REWRITE_TAC
    [parser_unicode_utf8_def; apply_parser_map_partial; parser_num_utf8_def;
     apply_parser_orelse; parser_ascii_utf8_def; apply_parser_token;
     case_pstream_def] THEN
  REVERSE_TAC (ASM_CASES_TAC `byte_bit b 7`) THENL
  [ASM_REWRITE_TAC [case_option_def] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [encode_unicode_utf8_def; LET_DEF; LET_END_DEF] THEN
   MP_TAC (SPEC `byte_to_num b` dest_mk_unicode) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `byte_to_num b < 128`
     (SUBST1_TAC o EQT_INTRO) THENL
   [POP_ASSUM (K ALL_TAC) THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `byte_to_num (num_to_byte 128)` THEN
    REVERSE_TAC CONJ_TAC THENL
    [REWRITE_TAC [num_to_byte_to_num_bit_bound; bit_bound_le];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM byte_lt_def] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (SPEC `b : byte` byte_list_cases) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `b0 : bool`
        (X_CHOOSE_THEN `b1 : bool`
          (X_CHOOSE_THEN `b2 : bool`
            (X_CHOOSE_THEN `b3 : bool`
              (X_CHOOSE_THEN `b4 : bool`
                (X_CHOOSE_THEN `b5 : bool`
                  (X_CHOOSE_THEN `b6 : bool`
                    (X_CHOOSE_THEN `b7 : bool`
                       SUBST_VAR_TAC)))))))) THEN
    bit_blast_tac THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [encode_ascii_utf8_def; byte_to_num_to_byte; append_pstream_def];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [case_option_def; parser_multibyte_utf8_def; apply_parser_sequence;
     apply_parser_token; case_pstream_def] THEN
  REVERSE_TAC COND_CASES_TAC THENL
  [REWRITE_TAC [case_option_def; option_distinct];
   ALL_TAC] THEN
  REVERSE_TAC COND_CASES_TAC *** THENL
  [REWRITE_TAC
     [parser_two_byte_utf8_def; case_option_def; apply_parser_filter;
      parser_foldn_def; apply_parser_fold] THEN
   SUBGOAL_THEN
     `byte_to_num (byte_and b (num_to_byte 31)) =
      bit_bound (byte_to_num b) 5`
     SUBST1_TAC THENL
   [CHEAT_TAC;
    ALL_TAC] THEN
   MP_TAC (ISPEC `zs : byte pstream` pstream_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `b1 : byte`
           (X_CHOOSE_THEN `xs : byte pstream` SUBST_VAR_TAC)))) THENL
   [REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
    REWRITE_TAC [case_pstream_def; case_option_def; option_distinct];
    ALL_TAC] THEN
   REWRITE_TAC [case_pstream_def] THEN
   ONCE_REWRITE_TAC [parse_fold_def] THEN
   REWRITE_TAC [add_continuation_utf8_def] THEN
   SUBGOAL_THEN
     `byte_to_num (byte_and b1 (num_to_byte 63)) =
      bit_bound (byte_to_num b1) 6`
     SUBST1_TAC THENL
   [CHEAT_TAC;
    ALL_TAC] THEN
   REVERSE_TAC COND_CASES_TAC THENL
   [REWRITE_TAC [map_option_def; case_option_def; option_distinct];
    ALL_TAC] THEN
   REWRITE_TAC [map_option_def; case_option_def; case_sum_def] THEN
   REVERSE_TAC COND_CASES_TAC THENL
   [REWRITE_TAC [case_option_def; option_distinct];
    ALL_TAC] THEN
   REWRITE_TAC [case_option_def] THEN
   REVERSE_TAC COND_CASES_TAC THENL
   [REWRITE_TAC [case_option_def; option_distinct];
    ALL_TAC] THEN
   REWRITE_TAC [case_option_def; option_inj; PAIR_EQ]
   ***


  REWRITE_TAC [apply_parser_def] THEN
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
           is_plane_unicode x /\
           (is_plane_unicode x ==>
            is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z) ==>
           is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z` THENL
      [SIMP_TAC [];
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
      [REWRITE_TAC [is_plane_unicode_def] THEN
       bit_blast_tac;
       ALL_TAC] THEN
      REWRITE_TAC [is_unicode_def; position_unicode_tybij] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_unicode_tybij] th]) THEN
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
           is_plane_unicode x /\
           (is_plane_unicode x ==>
            is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z) ==>
           is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z` THENL
      [SIMP_TAC [];
       ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      CONJ_TAC THENL
      [REWRITE_TAC [is_plane_unicode_def] THEN
       bit_blast_tac;
       ALL_TAC] THEN
      REWRITE_TAC [is_unicode_def; position_unicode_tybij] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_unicode_tybij] th]) THEN
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
          is_plane_unicode x /\
          (is_plane_unicode x ==>
           is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z) ==>
          is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z` THENL
     [SIMP_TAC [];
      ALL_TAC] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     CONJ_TAC THENL
     [REWRITE_TAC [is_plane_unicode_def] THEN
      bit_blast_tac;
      ALL_TAC] THEN
     REWRITE_TAC [is_unicode_def; position_unicode_tybij] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_unicode_tybij] th]) THEN
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
        is_plane_unicode x /\
        (is_plane_unicode x ==>
         is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z) ==>
        is_unicode (mk_plane_unicode x, mk_position_unicode y) /\ z` THENL
   [SIMP_TAC [];
    ALL_TAC] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   CONJ_TAC THENL
   [REWRITE_TAC [is_plane_unicode_def] THEN
    bit_blast_tac;
    ALL_TAC] THEN
   REWRITE_TAC [is_unicode_def; position_unicode_tybij] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [REWRITE_RULE [plane_unicode_tybij] th]) THEN
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

let reencode_decode_utf8 = prove
  (`!b. reencode_utf8 (decode_utf8 b) = b`,
   GEN_TAC THEN
   MP_TAC (SPEC `encode cs` decode_length) THEN
   REWRITE_TAC [decode_encode; case_option_def]);;

export_thm encode_length;;
***)

let encode_unicode_utf8_src = prove
 (`encode_unicode_utf8 =
   \c.
     let n = dest_unicode c in
     if n < 128 then encode_ascii_utf8 n else
     if n < 2048 then encode_two_byte_utf8 n else
     if n < 65536 then encode_three_byte_utf8 n else
     encode_four_byte_utf8 n`,
  REWRITE_TAC [FUN_EQ_THM; encode_unicode_utf8_def]);;

export_thm encode_unicode_utf8_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for unicode characters.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "char-haskell-src";;

export_thm dest_plane_unicode_def;;  (* Haskell *)
export_thm dest_position_unicode_def;;  (* Haskell *)
export_thm is_unicode_src;;  (* Haskell *)
export_thm mk_dest_unicode;;  (* Haskell *)
export_thm plane_unicode_src;;  (* Haskell *)
export_thm position_unicode_src;;  (* Haskell *)
export_thm random_unicode_def;;  (* Haskell *)
export_thm encode_ascii_utf8_def;;  (* Haskell *)
export_thm encode_two_byte_utf8_def;;  (* Haskell *)
export_thm encode_three_byte_utf8_def;;  (* Haskell *)
export_thm encode_four_byte_utf8_def;;  (* Haskell *)
export_thm encode_unicode_utf8_src;;  (* Haskell *)
export_thm encode_utf8_def;;  (* Haskell *)
export_thm reencode_unicode_utf8_def;;  (* Haskell *)
export_thm reencode_utf8_def;;  (* Haskell *)
export_thm parser_ascii_utf8_def;;  (* Haskell *)
export_thm is_continuation_utf8_def;;  (* Haskell *)
export_thm add_continuation_utf8_def;;  (* Haskell *)
export_thm parser_two_byte_utf8_def;;  (* Haskell *)
export_thm parser_three_byte_utf8_def;;  (* Haskell *)
export_thm parser_four_byte_utf8_def;;  (* Haskell *)
export_thm parser_multibyte_utf8_def;;  (* Haskell *)
export_thm parser_num_utf8_def;;  (* Haskell *)
export_thm parser_unicode_utf8_def;;  (* Haskell *)
export_thm parser_utf8_def;;  (* Haskell *)
export_thm decode_utf8_def;;  (* Haskell *)

logfile_end ();;

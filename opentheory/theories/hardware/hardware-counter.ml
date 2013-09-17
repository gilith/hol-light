(* ========================================================================= *)
(* HARDWARE COUNTER DEVICES                                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware counter devices.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-counter-def";;

let event_counter_def = new_definition
  `!ld nb inc dn.
      event_counter ld nb inc dn <=>
      ?r sp cp sq cq sr cr dp dq sp0 sp1 cp0 cp1 cp2 sq0 sq1 cq0 cq1.
         width nb = r + 1 /\
         width sp = r + 1 /\
         width cp = r + 1 /\
         width sq = r + 1 /\
         width cq = r + 1 /\
         width sr = r + 1 /\
         width cr = r + 1
         /\
         wire sp 0 sp0 /\
         bsub sp 1 r sp1 /\
         wire sq 0 sq0 /\
         bsub sq 1 r sq1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1
         /\
         xor2 inc sp0 sq0 /\
         and2 inc sp0 cq0 /\
         badder2 sp1 cp1 sq1 cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb sq sr /\
         bcase1 ld (bground (r + 1)) cq cr /\
         case1 ld ground dq dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn dp`;;

export_thm event_counter_def;;

let counter_def = new_definition
  `!ld nb dn.
      counter ld nb dn <=>
      ?r sp cp sq cq sr cr dp dq nb0 nb1 cp0 cp1 cp2 cq0 cq1 cr0 cr1.
         width nb = r + 1 /\
         width sp = r /\
         width cp = r + 1 /\
         width sq = r /\
         width cq = r + 1 /\
         width sr = r /\
         width cr = r + 1
         /\
         wire nb 0 nb0 /\
         bsub nb 1 r nb1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1 /\
         wire cr 0 cr0 /\
         bsub cr 1 r cr1
         /\
         not cp0 cq0 /\
         badder2 sp cp1 sq cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb1 sq sr /\
         case1 ld nb0 cq0 cr0 /\
         bcase1 ld (bground r) cq1 cr1 /\
         case1 ld ground dq dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn dp`;;

export_thm counter_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware counter devices.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-counter-thm";;

let event_counter_signal = prove
 (`!n ld nb inc dn t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n = 2 EXP (width nb) /\
     event_counter ld nb inc dn ==>
     (signal dn (t + k) <=>
      n <= CARD { i | 0 < i /\ i + width nb <= k /\ signal inc (t + i) })`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [event_counter_def; GSYM RIGHT_EXISTS_AND_THM;
     GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
  [UNDISCH_TAC `bits_to_num (bsignal nb t) + n = 2 EXP (width nb)` THEN
   ASM_REWRITE_TAC [ADD_0] THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `bsignal nb t` bits_to_num_bound) THEN
   ASM_REWRITE_TAC [length_bsignal; LT_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?f. (\j. CARD { i | 0 < i /\ i <= j /\ signal inc (t + i) }) = f`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!j1 j2. j1 <= j2 ==> (f : cycle -> num) j1 <= f j2`
    STRIP_ASSUME_TAC THENL
  [POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC CARD_SUBSET THEN
   CONJ_TAC THENL
   [REWRITE_TAC [SUBSET; IN_ELIM] THEN
    X_GEN_TAC `i : cycle` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `j1 : cycle` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{ i : cycle | i <= j2 }` THEN
    REWRITE_TAC [FINITE_NUMSEG_LE; SUBSET; IN_ELIM] THEN
    REPEAT STRIP_TAC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `n <= CARD { i | 0 < i /\ i + width nb <= k /\ signal inc (t + i) } <=>
     width nb <= k /\ n <= f (k - width nb)`
    SUBST1_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [] THEN
   ASM_CASES_TAC `width nb <= k` THENL
   [POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LE_EXISTS]) THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [LE_ADD; ADD_SUB2] THEN
    REPEAT (AP_TERM_TAC ORELSE AP_THM_TAC ORELSE ABS_TAC) THEN
    CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
    REWRITE_TAC [LE_ADD_LCANCEL];
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LE; LT_EXISTS]) THEN
    POP_ASSUM (MP_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL_0] THEN
    ASM_REWRITE_TAC [ADD_SUC; NOT_SUC; EMPTY_GSPEC; CARD_EMPTY; LE_ZERO]];
   ALL_TAC] THEN
  STP_TAC
    `if f k < n then
       (bits_to_num (bsignal sr (t + k)) +
        2 * bits_to_num (bsignal cr (t + k)) + n =
        2 EXP (r + 1) + f k /\
        ~signal dn (t + k))
     else
       ?s.
         (minimal j. n <= f j) + s = k /\
         (if s <= r then
            (?srs crs crs0.
               bsub sr (s + 1) (r - s) srs /\
               bsub cr s ((r + 1) - s) crs /\
               wire cr s crs0 /\
               bits_to_num (bsignal srs (t + k)) +
               bits_to_num (bsignal crs (t + k)) =
               2 EXP (r - s) /\
               signal crs0 (t + k) /\
               ~signal dn (t + k))
          else
            signal dn (t + k))` THENL
  [COND_CASES_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (TAUT `!x y. (x ==> ~y) ==> ~(x /\ y)`) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
       REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD_SUB2; NOT_LE] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(f : cycle -> num) ((r + 1) + d)` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LE_ADDR];
    ALL_TAC] THEN
   POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [NOT_LT]) THEN
   STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `\j. n <= (f : cycle -> num) j` MINIMAL) THEN
   REWRITE_TAC [] THEN
   SUBGOAL_THEN
     `(?j. n <= (f : cycle -> num) j) <=> T`
     SUBST1_TAC THENL
   [REWRITE_TAC [] THEN
    EXISTS_TAC `k : cycle` THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   SPEC_TAC (`minimal j. n <= (f : cycle -> num) j`, `j : cycle`) THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   COND_CASES_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (TAUT `!x y. (x ==> ~y) ==> ~(x /\ y)`) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ONCE_REWRITE_TAC [GSYM (SPEC `s : num` LT_ADD_RCANCEL)] THEN
    POP_ASSUM
      (X_CHOOSE_THEN `m : num` SUBST1_TAC o
       REWRITE_RULE [LE_EXISTS]) THEN
    REWRITE_TAC [ADD_SUB2] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [LT_ADD_RCANCEL] THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC_LE];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_THEN `~(s : num <= r)`
      (X_CHOOSE_THEN `m : num` SUBST_VAR_TAC o
       REWRITE_RULE [NOT_LE; LT_EXISTS]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `r + SUC m = m + (r + 1)` SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD1; ADD_SUC; SUC_INJ] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD1] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADDR; ADD_SUB] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(f : cycle -> num) j` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [LE_ADD]];
   ALL_TAC] THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  INDUCT_TAC THENL
  [DISCH_THEN
     (STRIP_ASSUME_TAC o
      REWRITE_RULE [LE_REFL; ADD_0] o
      SPEC `0`) THEN
   SUBGOAL_THEN `(f : cycle -> num) 0 = 0` ASSUME_TAC THENL
   [POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LE_ZERO; LT_NZ] THEN
    PURE_REWRITE_TAC [TAUT `!x y. ~x /\ x /\ y <=> F`; GSYM EMPTY] THEN
    REWRITE_TAC [CARD_EMPTY];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [LT_NZ; ADD_0] THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `nb : bus`; `sq : bus`;
         `sr : bus`; `t : cycle`] bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `bground (r + 1)`; `cq : bus`;
         `cr : bus`; `t : cycle`] bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`; `ground`; `dq : wire`;
         `dn : wire`; `t : cycle`] case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [ground_signal; bground_bits_to_num; MULT_0; ZERO_ADD];
   ALL_TAC] THEN
  POP_ASSUM (fun th ->
    STRIP_TAC THEN
    MP_TAC th) THEN
  ANTS_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k : cycle` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  POP_ASSUM
    (STRIP_ASSUME_TAC o
     REWRITE_RULE [LE_REFL; NOT_SUC] o
     SPEC `SUC k`) THEN
  SUBGOAL_THEN
    `f (SUC k) = f k + if signal inc (t + SUC k) then 1 else 0`
    ASSUME_TAC THENL
  [POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD ({i | 0 < i /\ i <= k /\ signal inc (t + i)} UNION
            (if signal inc (t + SUC k) then {SUC k} else {}))` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION; IN_UNION; IN_ELIM] THEN
    X_GEN_TAC `i : cycle` THEN
    REWRITE_TAC [CONJUNCT2 LE; LEFT_OR_DISTRIB; RIGHT_OR_DISTRIB] THEN
    CONV_TAC (LAND_CONV (REWR_CONV DISJ_SYM)) THEN
    AP_TERM_TAC THEN
    ASM_CASES_TAC `i = SUC k` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     REWRITE_TAC [LT_NZ; NOT_SUC] THEN
     COND_CASES_TAC THEN
     REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY];
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `CARD {i | 0 < i /\ i <= k /\ signal inc (t + i)} +
      CARD (if signal inc (t + SUC k) then {SUC k} else {})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN
    REPEAT CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{ i : cycle | i <= k }` THEN
     REWRITE_TAC [FINITE_NUMSEG_LE; SUBSET; IN_ELIM] THEN
     REPEAT STRIP_TAC;
     COND_CASES_TAC THEN
     REWRITE_TAC [FINITE_INSERT; FINITE_EMPTY];
     REWRITE_TAC [DISJOINT; EXTENSION; IN_ELIM; NOT_IN_EMPTY; IN_INTER] THEN
     X_GEN_TAC `i : cycle` THEN
     COND_CASES_TAC THENL
     [REWRITE_TAC [IN_SING] THEN
      STRIP_TAC THEN
      POP_ASSUM SUBST_VAR_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [NOT_LE; SUC_LT];
      REWRITE_TAC [NOT_IN_EMPTY]]];
    ALL_TAC] THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   COND_CASES_TAC THEN
   REWRITE_TAC [CARD_SING; CARD_EMPTY];
   ALL_TAC] THEN
  MP_TAC (SPECL [`cr : bus`; `r : num`] wire_exists) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [LT_ADD; ONE; LT_0];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `cr2 : wire` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `signal dn (t + SUC k) <=>
     signal dn (t + k) \/ signal cr2 (t + k)`
    SUBST1_TAC THENL
  [MP_TAC
     (SPECL
        [`ld : wire`; `ground`; `dq : wire`;
         `dn : wire`; `t + SUC k`] case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
    (SPECL [`dp : wire`; `cp2 : wire`; `dq : wire`; `t + SUC k`]
       or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUC] THEN
   REWRITE_TAC [ADD1] THEN
   MP_TAC
     (SPECL
        [`dn : wire`; `dp : wire`; `t + k : cycle`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC delay_signal THEN
   MATCH_MP_TAC bdelay_wire THEN
   EXISTS_TAC `cr : bus` THEN
   EXISTS_TAC `cp : bus` THEN
   EXISTS_TAC `r : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  COND_CASES_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `~signal cr2 (t + k)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC
      (SPECL [`cr : bus`; `r : num`; `cr2 : wire`; `t + k : cycle`]
       wire_bits_to_num) THEN
    ASM_REWRITE_TAC [NOT_LE] THEN
    MP_TAC (REWRITE_RULE [NOT_SUC] (SPEC `SUC 1` LT_MULT_LCANCEL)) THEN
    DISCH_THEN (CONV_TAC o REWR_CONV o GSYM o REWRITE_RULE [GSYM TWO]) THEN
    REWRITE_TAC [GSYM EXP_SUC; ADD1] THEN
    CONV_TAC
     (REWR_CONV (GSYM (SPEC `(f : cycle -> num) k` LT_ADD_RCANCEL))) THEN
    FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 * bits_to_num (bsignal cr (t + k)) + n` THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal sr (t + SUC k)) +
      2 * bits_to_num (bsignal cr (t + SUC k)) =
      bits_to_num (bsignal sr (t + k)) +
      2 * bits_to_num (bsignal cr (t + k)) +
      (if signal inc (t + SUC k) then 1 else 0)`
     ASSUME_TAC THENL
   [MP_TAC
      (SPECL
         [`ld : wire`; `nb : bus`; `sq : bus`;
          `sr : bus`; `t + SUC k`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `bground (r + 1)`; `cq : bus`;
          `cr : bus`; `t + SUC k`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `bappend (bwire sq0) sq1 = sq`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     UNDISCH_THEN `width sq = r + 1`
       (SUBST1_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     CONJ_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    SUBGOAL_THEN `bappend (bwire cq0) cq1 = cq`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     UNDISCH_THEN `width cq = r + 1`
       (SUBST1_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     CONJ_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `(bit_to_num (signal sq0 (t + SUC k)) +
        2 * bit_to_num (signal cq0 (t + SUC k))) +
       2 * (bits_to_num (bsignal sq1 (t + SUC k)) +
            2 * bits_to_num (bsignal cq1 (t + SUC k)))` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LEFT_ADD_DISTRIB; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    MP_TAC (SPECL
              [`sp1 : bus`;
               `cp1 : bus`;
               `sq1 : bus`;
               `cq1 : bus`;
               `t + SUC k`]
              badder2_bits_to_num) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (SPECL
              [`inc : wire`;
               `sp0 : wire`;
               `sq0 : wire`;
               `t + SUC k`]
              xor2_signal) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPECL
              [`inc : wire`;
               `sp0 : wire`;
               `cq0 : wire`;
               `t + SUC k`]
              and2_signal) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `(if signal inc (t + SUC k) then 1 else 0) +
       bit_to_num (signal sp0 (t + SUC k)) +
       2 * (bits_to_num (bsignal sp1 (t + SUC k)) +
            bits_to_num (bsignal cp1 (t + SUC k)))` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
     BOOL_CASES_TAC `signal inc (t + SUC k)` THEN
     BOOL_CASES_TAC `signal sp0 (t + SUC k)` THEN
     REWRITE_TAC
       [bit_to_num_true; bit_to_num_false; ZERO_ADD; MULT_1; MULT_0;
        ADD_0] THEN
     REWRITE_TAC [TWO; ADD1];
     ALL_TAC] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MP_TAC (SPECL
              [`sr : bus`;
               `sp : bus`;
               `t + k : cycle`]
              bdelay_bsignal) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [GSYM ADD1; GSYM ADD_SUC] THEN
    SUBGOAL_THEN `bappend (bwire sp0) sp1 = sp`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     UNDISCH_THEN `width sp = r + 1`
       (SUBST1_TAC o ONCE_REWRITE_RULE [ADD_SYM]) THEN
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     CONJ_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
    AP_TERM_TAC THEN
    MP_TAC (SPECL
              [`cr : bus`;
               `cp : bus`;
               `t + k : cycle`]
              bdelay_bsignal) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `bappend cp1 (bwire cp2) = cp`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     UNDISCH_THEN `width cp = r + 1` SUBST1_TAC THEN
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     CONJ_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num] THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC
      [EQ_ADD_LCANCEL_0; ADD_SUC; ADD1; bwire_bsignal; bits_to_num_sing;
       bit_shl_eq_zero; bit_to_num_zero] THEN
    UNDISCH_TAC `~signal cr2 (t + k)` THEN
    MATCH_MP_TAC (TAUT `!x y. (y <=> x) ==> (~x ==> ~y)`) THEN
    MATCH_MP_TAC delay_signal THEN
    MATCH_MP_TAC bdelay_wire THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `cp : bus` THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [ADD_ASSOC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV ADD_SYM)))) THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   SUBGOAL_THEN `signal inc (t + SUC k)`
     (fun th ->
        POP_ASSUM MP_TAC THEN
        ASSUME_TAC th) THENL
   [POP_ASSUM MP_TAC THEN
    BOOL_CASES_TAC `signal inc (t + SUC k)` THEN
    ASM_REWRITE_TAC [ADD_0];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [NOT_LT] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN
     `(minimal j. n <= (f : cycle -> num) j) = SUC k`
     SUBST1_TAC THENL
   [MATCH_MP_TAC MINIMAL_EQ THEN
    ASM_REWRITE_TAC [LT_SUC_LE; NOT_LE] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `(f : cycle -> num) k` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `n = 1 + (f : cycle -> num) k`
     SUBST_VAR_TAC THENL
   [ONCE_REWRITE_TAC [ADD_SYM] THEN
    CONV_TAC (REWR_CONV (GSYM LE_ANTISYM)) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [GSYM ADD1; LE_SUC_LT];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [ADD_0; SUB_0; LE_0; ZERO_ADD] THEN
   SUBGOAL_THEN `?sr1. bsub sr 1 r sr1` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_exists THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    ASM_REWRITE_TAC [LE_REFL];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cr0. wire cr 0 cr0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_0];
    ALL_TAC] THEN
   EXISTS_TAC `sr1 : bus` THEN
   EXISTS_TAC `cr : bus` THEN
   EXISTS_TAC `cr0 : wire` THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPECL [`cr : bus`; `cr : bus`] bsub_all) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   SUBGOAL_THEN `signal sp0 (t + SUC k)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?sr0. wire sr 0 sr0` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC wire_exists THEN
     ASM_REWRITE_TAC [GSYM ADD1; LT_0];
     ALL_TAC] THEN
    STP_TAC `signal sr0 (t + k)` THENL
    [MATCH_MP_TAC (TAUT `!x y. (y <=> x) ==> (x ==> y)`) THEN
     REWRITE_TAC [ADD_SUC] THEN
     REWRITE_TAC [ADD1] THEN
     MATCH_MP_TAC delay_signal THEN
     MATCH_MP_TAC bdelay_wire THEN
     EXISTS_TAC `sr : bus` THEN
     EXISTS_TAC `sp : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    UNDISCH_TAC
      `bits_to_num (bsignal sr (t + k)) +
       2 * bits_to_num (bsignal cr (t + k)) +
       1 + f k =
       2 EXP (r + 1) + f k` THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV (GSYM SUC_INJ))) THEN
    REWRITE_TAC [ADD1; GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `1 + 1 = 2 * 1` SUBST1_TAC THENL
    [REWRITE_TAC [TWO; MULT_1; ADD1];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `bappend (bwire sr0) sr1 = sr`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     SUBGOAL_THEN `width sr = 1 + r` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_ACCEPT_TAC ADD_SYM;
      MATCH_MP_TAC bsub_add THEN
      REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC [GSYM bit_cons_def] THEN
    SUBGOAL_THEN `2 EXP (r + 1) + 1 = bit_cons T (2 EXP r)` SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD1; bit_cons_def; bit_to_num_true; EXP_SUC] THEN
     REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [bit_cons_inj] THEN
    STRIP_TAC;
    ALL_TAC] THEN
   REVERSE_TAC CONJ_TAC THENL
   [MP_TAC (SPECL [`ld : wire`;
                   `ground`;
                   `cq0 : wire`;
                   `cr0 : wire`;
                   `t + SUC k`]
                  case1_signal) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC bcase1_wire THEN
     EXISTS_TAC `bground (r + 1)` THEN
     EXISTS_TAC `cq : bus` THEN
     EXISTS_TAC `cr : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [bground_wire] THEN
     REWRITE_TAC [GSYM ADD1; LT_0];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL
              [`inc : wire`;
               `sp0 : wire`;
               `cq0 : wire`;
               `t + SUC k`]
              and2_signal) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?sr0. wire sr 0 sr0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_0];
    ALL_TAC] THEN
   STP_TAC
     `(signal sr0 (t + SUC k) <=> F) /\
      (bits_to_num (bsignal sr1 (t + SUC k)) +
       bits_to_num (bsignal cr (t + SUC k)) =
       2 EXP r)` THENL
   [STRIP_TAC;
    ALL_TAC] THEN
   PURE_REWRITE_TAC [GSYM bit_cons_inj] THEN
   REWRITE_TAC [bit_cons_def; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
   REWRITE_TAC [bit_to_num_false; ZERO_ADD; GSYM EXP_SUC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bits_to_num (bsignal sr (t + SUC k)) +
      2 * bits_to_num (bsignal cr (t + SUC k))` THEN
   REVERSE_TAC CONJ_TAC THENL
   [ASM_REWRITE_TAC [ADD_ASSOC] THEN
    FIRST_X_ASSUM
      (CONV_TAC o LAND_CONV o REWR_CONV o
       REWRITE_RULE [ADD_ASSOC; EQ_ADD_RCANCEL]) THEN
    REWRITE_TAC [ADD1];
    ALL_TAC] THEN
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   SUBGOAL_THEN `bappend (bwire sr0) sr1 = sr`
     (SUBST1_TAC o SYM) THENL
   [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
    SUBGOAL_THEN `width sr = 1 + r` SUBST1_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons] THEN
   REWRITE_TAC [bit_cons_def];
   ALL_TAC] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN `((f : cycle -> num) (SUC k) < n) <=> F` SUBST1_TAC THENL
  [REWRITE_TAC [NOT_LT] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `(f : cycle -> num) k` THEN
   CONJ_TAC THENL
   [ASM_REWRITE_TAC [GSYM NOT_LT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [SUC_LE]];
   ALL_TAC] THEN
  REWRITE_TAC [] THEN
  REVERSE_TAC COND_CASES_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `SUC s` THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_INJ] THEN
   STP_TAC `~(SUC s <= r)` THENL
   [DISCH_THEN (fun th -> REWRITE_TAC [th]);
    ALL_TAC] THEN
   REWRITE_TAC [NOT_LE] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `s : num` THEN
   REWRITE_TAC [SUC_LE] THEN
   ASM_REWRITE_TAC [GSYM NOT_LE];
   ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `SUC s` THEN
  ASM_REWRITE_TAC [ADD_SUC; SUC_INJ] THEN
  REVERSE_TAC COND_CASES_TAC THENL
  [STP_TAC `(cr2 : wire) = crs0` THENL
   [DISCH_THEN (fun th -> ASM_REWRITE_TAC [th]);
    ALL_TAC] THEN
   MATCH_MP_TAC wire_inj THEN
   EXISTS_TAC `cr : bus` THEN
   EXISTS_TAC `r : num` THEN
   ASM_REWRITE_TAC [] THEN
   STP_TAC `(r : num) = s` THENL
   [DISCH_THEN (fun th -> ASM_REWRITE_TAC [th]);
    ALL_TAC] THEN
   CONV_TAC (REWR_CONV (GSYM LE_ANTISYM)) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [GSYM NOT_LT; GSYM LE_SUC_LT];
   ALL_TAC] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
     REWRITE_RULE [LE_SUC_LT; LT_EXISTS]) THEN
  SUBGOAL_THEN `(s + SUC d) - SUC s = d` SUBST1_TAC THENL
  [REWRITE_TAC [ADD_SUC; GSYM SUC_ADD; ADD_SUB2];
   ALL_TAC] THEN
  SUBGOAL_THEN `((s + SUC d) + 1) - SUC s = SUC d` SUBST1_TAC THENL
  [REWRITE_TAC [GSYM ADD1; GSYM SUC_ADD; ADD_SUB2];
   ALL_TAC] THEN
  REPEAT (POP_ASSUM MP_TAC) THEN
  SUBGOAL_THEN `(s + SUC d) + 1 = s + SUC (SUC d)` SUBST1_TAC THENL
  [REWRITE_TAC [GSYM ADD1; ADD_SUC];
   ALL_TAC] THEN
  REWRITE_TAC [LE_ADD; ADD_SUB2; GSYM ADD1] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`cr : bus`;
                 `SUC s`;
                 `SUC d`]
                bsub_exists) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `crd : bus` ASSUME_TAC) THEN
  SUBGOAL_THEN `crs = bappend (bwire crs0) crd` ASSUME_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
   SUBGOAL_THEN `width crs = 1 + SUC d` SUBST1_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `s : num` THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `s : num`;
         `SUC (SUC d)`;
         `crs : bus`;
         `0`;
         `crs0 : wire`]
        bsub_wire) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [LT_0; ADD_0] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `s : num`;
         `SUC (SUC d)`;
         `crs : bus`;
         `1`;
         `SUC d`;
         `crd : bus`]
        bsub_bsub) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [ONE; ADD_SUC; SUC_ADD; ZERO_ADD; ADD_0; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `~signal cr2 (t + k)` ASSUME_TAC THENL
  [STRIP_TAC THEN
   MP_TAC (SPEC `2 EXP SUC d` LT_REFL) THEN
   REWRITE_TAC [] THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `bits_to_num (bsignal crs (t + k))` THEN
   REWRITE_TAC [LE_ADDR] THEN
   ASM_REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons] THEN
   REWRITE_TAC [bit_cons_def; bit_to_num_true; EXP_SUC] THEN
   REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD; LT_SUC_LE] THEN
   REWRITE_TAC [GSYM bit_shl_one; bit_shl_mono_le] THEN
   MATCH_MP_TAC wire_bits_to_num THEN
   EXISTS_TAC `cr2 : wire` THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `SUC s`;
         `SUC d`;
         `crd : bus`;
         `d : num`;
         `cr2 : wire`]
        bsub_wire) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [SUC_LT; SUC_ADD; GSYM ADD_SUC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `?srs0. wire sr (SUC s) srs0` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; LT_SUC; LT_SUC_LE; LE_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN `?srd. bsub sr (SUC (SUC s)) d srd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `srs = bappend (bwire srs0) srd` ASSUME_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
   SUBGOAL_THEN `width srs = 1 + d` SUBST1_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sr : bus` THEN
    EXISTS_TAC `SUC s : num` THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MP_TAC
     (SPECL
        [`sr : bus`;
         `SUC s`;
         `SUC d`;
         `srs : bus`;
         `0`;
         `srs0 : wire`]
        bsub_wire) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [LT_0; ADD_0] THEN
   MP_TAC
     (SPECL
        [`sr : bus`;
         `SUC s`;
         `SUC d`;
         `srs : bus`;
         `1`;
         `d : num`;
         `srd : bus`]
        bsub_bsub) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [ONE; ADD_SUC; SUC_ADD; ZERO_ADD; ADD_0; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `?crd0. wire cr (SUC s) crd0` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; LT_SUC; LT_SUC_LE; LE_ADD];
   ALL_TAC] THEN
  EXISTS_TAC `srd : bus` THEN
  EXISTS_TAC `crd : bus` THEN
  EXISTS_TAC `crd0 : wire` THEN
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `signal srs0 (t + k)` ASSUME_TAC THENL
  [UNDISCH_TAC
     `bits_to_num (bsignal srs (t + k)) +
      bits_to_num (bsignal crs (t + k)) =
      2 EXP SUC d` THEN
   ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC
     [EXP_SUC; bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def;
      bit_to_num_false; ZERO_ADD; GSYM ADD_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [GSYM bit_cons_def] THEN
   REWRITE_TAC [GSYM bit_cons_false; bit_cons_inj];
   ALL_TAC] THEN
  UNDISCH_TAC
    `bits_to_num (bsignal srs (t + k)) +
     bits_to_num (bsignal crs (t + k)) =
     2 EXP SUC d` THEN
  ASM_REWRITE_TAC [EXP_SUC; bappend_bwire_bsignal; bits_to_num_cons] THEN
  REWRITE_TAC
    [bit_cons_def; bit_to_num_true; ONE; SUC_ADD; ZERO_ADD; ADD_SUC] THEN
  SUBGOAL_THEN
    `!n. SUC (SUC n) = 2 * 1 + n`
    (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV) THENL
  [REWRITE_TAC [MULT_1] THEN
   REWRITE_TAC [TWO; ONE; SUC_ADD; ZERO_ADD];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL] THEN
  STRIP_TAC THENL
  [POP_ASSUM MP_TAC THEN
   REWRITE_TAC [TWO; NOT_SUC];
   ALL_TAC] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN `signal crd0 (SUC (t + k))` ASSUME_TAC THENL
  [SUBGOAL_THEN `?cqd0. wire cq (SUC s) cqd0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [ADD_SUC; LT_SUC; LT_SUC_LE; LE_ADD];
    ALL_TAC] THEN
   MP_TAC (SPECL [`ld : wire`;
                  `ground`;
                  `cqd0 : wire`;
                  `crd0 : wire`;
                  `SUC (t + k)`]
                 case1_signal) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC bcase1_wire THEN
    EXISTS_TAC `bground (s + SUC (SUC d))` THEN
    EXISTS_TAC `cq : bus` THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `SUC s` THEN
    ASM_REWRITE_TAC [bground_wire] THEN
    REWRITE_TAC [ADD_SUC; LT_SUC_LE; LE_SUC; LE_ADD];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [GSYM ADD_SUC] THEN
   SUBGOAL_THEN `?spd0. wire sp (SUC s) spd0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [ADD_SUC; LT_SUC; LT_SUC_LE; LE_ADD];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cpd0. wire cp s cpd0` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [LT_ADD; LT_0];
    ALL_TAC] THEN
   UNDISCH_TAC `badder2 sp1 cp1 sq1 cq1` THEN
   REWRITE_TAC [badder2_def] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`spd0 : wire`;
                  `cpd0 : wire`;
                  `cqd0 : wire`;
                  `SUC (t + k)`]
                 and2_signal) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC band2_wire THEN
    EXISTS_TAC `sp1 : bus` THEN
    EXISTS_TAC `cp1 : bus` THEN
    EXISTS_TAC `cq1 : bus` THEN
    EXISTS_TAC `s : num` THEN
    ASM_REWRITE_TAC [] THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`sp : bus`;
           `1`;
           `s + SUC d`;
           `sp1 : bus`;
           `s : num`;
           `spd0 : wire`]
          bsub_wire) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [LT_ADD; LT_0] THEN
     ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MP_TAC
       (SPECL
          [`cp : bus`;
           `0`;
           `s + SUC d`;
           `cp1 : bus`;
           `s : num`;
           `cpd0 : wire`]
          bsub_wire) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [LT_ADD; LT_0] THEN
     ASM_REWRITE_TAC [ZERO_ADD];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`cq : bus`;
          `1`;
          `s + SUC d`;
          `cq1 : bus`;
          `s : num`;
          `cqd0 : wire`]
         bsub_wire) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LT_ADD; LT_0] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_SUC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD1] THEN
   MP_TAC (SPECL [`srs0 : wire`;
                  `spd0 : wire`;
                  `t + k : cycle`]
                 delay_signal) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC bdelay_wire THEN
    EXISTS_TAC `sr : bus` THEN
    EXISTS_TAC `sp : bus` THEN
    EXISTS_TAC `SUC s : num` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`crs0 : wire`;
                  `cpd0 : wire`;
                  `t + k : cycle`]
                 delay_signal) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC bdelay_wire THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `cp : bus` THEN
    EXISTS_TAC `s : num` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `?crd1. bsub cr (SUC (SUC s)) d crd1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `crd = bappend (bwire crd0) crd1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
   SUBGOAL_THEN `width crd = 1 + d` SUBST1_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `SUC s : num` THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `SUC s`;
         `SUC d`;
         `crd : bus`;
         `0`;
         `crd0 : wire`]
        bsub_wire) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [LT_0; ADD_0] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `SUC s`;
         `SUC d`;
         `crd : bus`;
         `1`;
         `d : num`;
         `crd1 : bus`]
        bsub_bsub) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [ONE; ADD_SUC; SUC_ADD; ZERO_ADD; ADD_0; LE_REFL];
   ALL_TAC] THEN
  POP_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  ASM_REWRITE_TAC
    [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def;
     bit_to_num_true] THEN
  REWRITE_TAC [ONE; ADD_SUC; SUC_ADD; SUC_INJ; ZERO_ADD] THEN
  SUBGOAL_THEN `?sqd. bsub sq (SUC (SUC s)) d sqd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `?nbd. bsub nb (SUC (SUC s)) d nbd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  MP_TAC (SPECL [`ld : wire`;
                 `nbd : bus`;
                 `sqd : bus`;
                 `srd : bus`;
                 `SUC (t + k)`]
                bcase1_bsignal) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC bcase1_bsub THEN
   EXISTS_TAC `nb : bus` THEN
   EXISTS_TAC `sq : bus` THEN
   EXISTS_TAC `sr : bus` THEN
   EXISTS_TAC `SUC (SUC s)` THEN
   EXISTS_TAC `d : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [GSYM ADD_SUC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `?cqd. bsub cq (SUC (SUC s)) d cqd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  MP_TAC (SPECL [`ld : wire`;
                 `bground d`;
                 `cqd : bus`;
                 `crd1 : bus`;
                 `SUC (t + k)`]
                bcase1_bsignal) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC bcase1_bsub THEN
   EXISTS_TAC `bground (s + SUC (SUC d))` THEN
   EXISTS_TAC `cq : bus` THEN
   EXISTS_TAC `cr : bus` THEN
   EXISTS_TAC `SUC (SUC s)` THEN
   EXISTS_TAC `d : num` THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [bground_bsub; SUC_ADD; ADD_SUC; LE_REFL];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [] THEN
  SUBGOAL_THEN `?spd. bsub sp (SUC (SUC s)) d spd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `?cpd. bsub cp (SUC s) d cpd` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; SUC_LE];
   ALL_TAC] THEN
  MP_TAC
   (SPECL
      [`spd : bus`;
       `cpd : bus`;
       `sqd : bus`;
       `cqd : bus`;
       `SUC (t + k)`]
      badder2_bits_to_num) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC badder2_bsub THEN
   EXISTS_TAC `sp1 : bus` THEN
   EXISTS_TAC `cp1 : bus` THEN
   EXISTS_TAC `sq1 : bus` THEN
   EXISTS_TAC `cq1 : bus` THEN
   EXISTS_TAC `SUC s : num` THEN
   EXISTS_TAC `d : num` THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [MP_TAC
      (SPECL
         [`sp : bus`;
          `1`;
          `s + SUC d`;
          `sp1 : bus`;
          `SUC s : num`;
          `d : num`;
          `spd : bus`]
         bsub_bsub) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC
      (SPECL
         [`cp : bus`;
          `0`;
          `s + SUC d`;
          `cp1 : bus`;
          `SUC s : num`;
          `d : num`;
          `cpd : bus`]
         bsub_bsub) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MP_TAC
      (SPECL
         [`sq : bus`;
          `1`;
          `s + SUC d`;
          `sq1 : bus`;
          `SUC s : num`;
          `d : num`;
          `sqd : bus`]
         bsub_bsub) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`cq : bus`;
         `1`;
         `s + SUC d`;
         `cq1 : bus`;
         `SUC s : num`;
         `d : num`;
         `cqd : bus`]
        bsub_bsub) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUC; SUC_ADD; LE_REFL] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_SUC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [ADD1] THEN
  MP_TAC
    (SPECL
       [`srd : bus`;
        `spd : bus`;
        `t + k : cycle`]
       bdelay_bsignal) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC bdelay_bsub THEN
   EXISTS_TAC `sr : bus` THEN
   EXISTS_TAC `sp : bus` THEN
   EXISTS_TAC `SUC (SUC s) : num` THEN
   EXISTS_TAC `d : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [EQ_ADD_LCANCEL] THEN
  SUBGOAL_THEN `?crd2. bsub cr (SUC s) d crd2` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_ADD; SUC_LE];
   ALL_TAC] THEN
  SUBGOAL_THEN `crd = bappend crd2 (bwire cr2)` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC EQ_SYM THEN
   CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
   SUBGOAL_THEN `width crd = d + 1` SUBST1_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `SUC s : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `SUC s`;
         `SUC d`;
         `crd : bus`;
         `d : num`;
         `cr2 : wire`]
        bsub_wire) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [SUC_LT; SUC_ADD; GSYM ADD_SUC] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `SUC s`;
         `SUC d`;
         `crd : bus`;
         `0`;
         `d : num`;
         `crd2 : bus`]
        bsub_bsub) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [ZERO_ADD; ADD_0; SUC_LE];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; bwire_bits_to_num; bit_to_num_false;
     zero_bit_shl; ADD_0] THEN
  MP_TAC
    (SPECL
       [`crd2 : bus`;
        `cpd : bus`;
        `t + k : cycle`]
       bdelay_bsignal) THEN
  ANTS_TAC THENL
  [MATCH_MP_TAC bdelay_bsub THEN
   EXISTS_TAC `cr : bus` THEN
   EXISTS_TAC `cp : bus` THEN
   EXISTS_TAC `SUC s : num` THEN
   EXISTS_TAC `d : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  REFL_TAC);;

export_thm event_counter_signal;;

(***
let counter_signal = prove
 (`!n ld nb dn t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n + 1 = 2 EXP (width nb) + width nb /\
     counter ld nb dn ==>
     (signal dn (t + k) <=> n <= k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`n + width nb : num`;
        `ld : wire`;
        `nb : bus`;
        `power`;
        `dn : wire`;
        `t : cycle`;
        `k : cycle`]
       event_counter_signal) THEN
  REVERSE_TAC ANTS_TAC THENL
  [DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [power_signal] THEN
   AP_TERM_TAC THEN
   

(***
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL
  [STRIP_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [bits_to_num_bsignal_bound
length_bsignal
width_def
***)

  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [counter_def; GSYM RIGHT_EXISTS_AND_THM;
     GSYM LEFT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`cr : bus`; `r : num`] wire_exists) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `cr2 : wire` ASSUME_TAC) THEN
  UNDISCH_TAC `!i. i <= k ==> (signal ld (t + i) <=> i = 0)` THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  STP_TAC
    `(!i. i < n ==> ~signal cr2 i) /\ signal cr2 n`

  SUBGOAL_THEN
     `!i.
        i < n ==>
        (bit_cons (~signal cr0 (t + i))
           (bits_to_num (bsignal sr (t + i)) +
            bits_to_num (bsignal cr (t + i))) + n) =
        2 EXP (width nb) + width nb + i` ASSUME_TAC THENL
  [SUBGOAL_THEN `bappend (mk_bus [cr0]) cr1 = cr`
     (SUBST1_TAC o SYM) THENL
   [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
    SUBGOAL_THEN `width cr = 1 + r` SUBST1_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     MATCH_MP_TAC bsub_add THEN
     REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
     ASM_REWRITE_TAC []];
    ALL_TAC] THEN
   REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT_NZ; ADD_0] THEN
    UNDISCH_THEN
      `bits_to_num (bsignal nb t) + n + 1 = 2 EXP width nb + width nb`
      (SUBST1_TAC o SYM) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [ADD_0; LE_0] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `bground r`; `cq1 : bus`;
          `cr1 : bus`; `t : cycle`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [bits_to_num_bsignal_bground; bit_cons_zero] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(bits_to_num (bsignal nb t) + 1) + n` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    SUBGOAL_THEN `bappend (mk_bus [nb0]) nb1 = nb`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     SUBGOAL_THEN `width nb = 1 + r` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_ACCEPT_TAC ADD_SYM;
      MATCH_MP_TAC bsub_add THEN
      REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb1 : bus`; `sq : bus`;
          `sr : bus`; `t : cycle`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb0 : wire`; `cq0 : wire`;
          `cr0 : wire`; `t : cycle`] case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    BOOL_CASES_TAC `signal nb0 t` THEN
    REWRITE_TAC
      [bit_cons_def; ADD_ASSOC; LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL;
       bit_to_num_def; ZERO_ADD; MULT_1; MULT_0; ADD_0] THEN
    NUM_REDUCE_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC [ADD_SUC] THEN
   FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
   [REWRITE_TAC [GSYM LE_SUC_LT] THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM SUC_ADD))) THEN
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   REWRITE_TAC [NOT_SUC]
ADD_0; LE_0] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `bground r`; `cq1 : bus`;
          `cr1 : bus`; `t : cycle`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [bits_to_num_bsignal_bground; bit_cons_zero] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(bits_to_num (bsignal nb t) + 1) + n` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    SUBGOAL_THEN `bappend (mk_bus [nb0]) nb1 = nb`
      (SUBST1_TAC o SYM) THENL
    [CONV_TAC (REWR_CONV (GSYM bsub_all)) THEN
     SUBGOAL_THEN `width nb = 1 + r` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      MATCH_ACCEPT_TAC ADD_SYM;
      MATCH_MP_TAC bsub_add THEN
      REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
      ASM_REWRITE_TAC []];
     ALL_TAC] THEN
    REWRITE_TAC [bsignal_append; bsignal_wire; APPEND; bits_to_num_cons] THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb1 : bus`; `sq : bus`;
          `sr : bus`; `t : cycle`] bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`; `nb0 : wire`; `cq0 : wire`;
          `cr0 : wire`; `t : cycle`] case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    BOOL_CASES_TAC `signal nb0 t` THEN
    REWRITE_TAC
      [bit_cons_def; ADD_ASSOC; LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL;
       bit_to_num_def; ZERO_ADD; MULT_1; MULT_0; ADD_0] THEN
    NUM_REDUCE_TAC;

  GEN_TAC THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  SPEC_TAC (`nb : bus`, `nb : bus`) THEN
  SPEC_TAC (`n : num`, `n : num`) THEN
  SPEC_TAC (`r : num`, `r : num`) THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [width_zero] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [ZERO_ADD; bsignal_nil; bits_to_num_nil; width_nil; EXP_0; ADD_0]
   ASM_REWRITE_TAC []
bsignal_nil; bits_to_num_nil] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [width_suc; GSYM IMP_IMP] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xh : wire`
      (X_CHOOSE_THEN `xt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `yh : wire`
      (X_CHOOSE_THEN `yt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zh : wire`
      (X_CHOOSE_THEN `zt : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `sh : wire`
      (X_CHOOSE_THEN `st : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ch : wire`
      (X_CHOOSE_THEN `ct : bus`
        (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))) THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [bsignal_cons; bits_to_num_cons; bus_tybij; bit_cons_def] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
     ((2 * bits_to_num (bsignal xt t)) +
      (2 * bits_to_num (bsignal yt t)) +
      (2 * bits_to_num (bsignal zt t)))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   CONV_TAC (LAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM)))) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal sh t) +
      2 * bit_to_num (signal ch t)) +
     ((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t))))` THEN
  CONJ_TAC THENL
  [POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(bit_to_num (signal xh t) +
      bit_to_num (signal yh t) +
      bit_to_num (signal zh t)) +
     ((2 * bits_to_num (bsignal st t)) +
      (2 * (2 * bits_to_num (bsignal ct t))))` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EQ_ADD_LCANCEL; GSYM LEFT_ADD_DISTRIB] THEN
   AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MATCH_MP_TAC o REWRITE_RULE [IMP_IMP]) THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [wire_suc];
   REWRITE_TAC [EQ_ADD_RCANCEL] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   POP_ASSUM_LIST (K ALL_TAC) THEN
   REWRITE_TAC [wire_zero] THEN
   DISCH_THEN
     (ASSUME_TAC o
      REWRITE_RULE [] o
      SPECL
        [`xh : wire`; `yh : wire`; `zh : wire`;
         `sh : wire`; `ch : wire`]) THEN
   MATCH_MP_TAC adder3 THEN
   ASM_REWRITE_TAC []]);;

export_thm counter_signal;;
***)

logfile_end ();;

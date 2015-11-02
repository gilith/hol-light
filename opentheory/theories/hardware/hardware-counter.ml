(* ========================================================================= *)
(* HARDWARE COUNTER DEVICES                                                  *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware counter devices.                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-counter-def";;

let bpipe_def = new_definition
  `!w x.
     bpipe w x <=>
     ?r xp x0 x1 x2.
       width x = r + 1 /\
       width xp = r
       /\
       wire x 0 x0 /\
       bsub x 0 r x1 /\
       bsub x 1 r x2
       /\
       connect w x0 /\
       bconnect xp x2
       /\
       bdelay x1 xp`;;

export_thm bpipe_def;;

let pipe_def = new_definition
  `!w d wd.
     pipe w d wd <=>
     ?x x0.
       width x = d + 1
       /\
       wire x d x0
       /\
       bpipe w x /\
       connect x0 wd`;;

export_thm pipe_def;;

let event_counter_def = new_definition
  `!ld nb inc dn.
      event_counter ld nb inc dn <=>
      ?r sp cp sq cq sr cr dp dq dr sp0 sp1 cp0 cp1 cp2 sq0 sq1 cq0 cq1.
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
         or2 dp cp2 dq /\
         bcase1 ld nb sq sr /\
         bcase1 ld (bground (r + 1)) cq cr /\
         case1 ld ground dq dr /\
         connect dr dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dr dp`;;

export_thm event_counter_def;;

let counter_def = new_definition
  `!ld nb dn.
      counter ld nb dn <=>
      ?r sp cp sq cq sr cr dp dq dr nb0 nb1 cp0 cp1 cp2 cq0 cq1 cr0 cr1.
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
         or2 dp cp2 dq /\
         bcase1 ld nb1 sq sr /\
         case1 ld nb0 cq0 cr0 /\
         bcase1 ld (bground r) cq1 cr1 /\
         case1 ld ground dq dr /\
         connect dr dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dr dp`;;

export_thm counter_def;;

let counter_pulse_def = new_definition
  `!ld nb dn.
      counter_pulse ld nb dn <=>
      ?ds. counter ld nb ds /\ pulse ds dn`;;

export_thm counter_pulse_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware counter devices.                                   *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-counter-thm";;

let bpipe_signal = prove
 (`!w x i xi t.
     bpipe w x /\
     wire x i xi ==>
     signal xi (t + i) = signal w t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bpipe_def] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC (`xi : wire`, `xi : wire`) THEN
  SPEC_TAC (`i : num`, `i : num`) THEN
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD_0] THEN
   MP_TAC
     (SPECL
        [`x : bus`;
         `0`;
         `xi : wire`;
         `x0 : wire`]
        wire_inj) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   MP_TAC
     (SPECL
       [`w : wire`;
        `x0 : wire`;
        `t : cycle`]
       connect_signal) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `i < (r : num)` STRIP_ASSUME_TAC THENL
  [MP_TAC (SPECL [`x : bus`; `SUC i`; `xi : wire`] wire_bound) THEN
   ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
   ALL_TAC] THEN
  MP_TAC
   (SPECL
      [`x : bus`;
       `1`;
       `r : num`;
       `x2 : bus`;
       `i : num`;
       `xi : wire`]
      bsub_wire) THEN
  ASM_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] (GSYM ADD1)] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?xpi. wire xp i xpi` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`xp : bus`;
        `x2 : bus`;
        `i : num`;
        `xpi : wire`;
        `xi : wire`]
       bconnect_wire) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`xpi : wire`;
       `xi : wire`;
       `t + SUC i : cycle`]
      connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `?xis. wire x i xis` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; LT_SUC_LE] THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `xis : wire`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [ADD_SUC] THEN
  REWRITE_TAC [ADD1] THEN
  MATCH_MP_TAC delay_signal THEN
  MATCH_MP_TAC bdelay_wire THEN
  EXISTS_TAC `x1 : bus` THEN
  EXISTS_TAC `xp : bus` THEN
  EXISTS_TAC `i : num` THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
   (SPECL
      [`x : bus`;
       `0`;
       `r : num`;
       `x1 : bus`;
       `i : num`;
       `xis : wire`]
      bsub_wire) THEN
   ASM_REWRITE_TAC [ZERO_ADD]);;

export_thm bpipe_signal;;

let pipe_signal = prove
 (`!w d wd t. pipe w d wd ==> signal wd (t + d) = signal w t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pipe_def] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
      [`x0 : wire`;
       `wd : wire`;
       `t + d : cycle`]
      connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC bpipe_signal THEN
  EXISTS_TAC `x : bus` THEN
  ASM_REWRITE_TAC []);;

export_thm pipe_signal;;

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
  MP_TAC
    (SPECL
       [`dr : wire`;
        `dn : wire`;
        `t + k : cycle`]
       connect_signal) THEN
  UNDISCH_THEN `connect dr dn` (fun th -> REWRITE_TAC [th]) THEN
  DISCH_THEN SUBST1_TAC THEN
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
        ~signal dr (t + k))
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
               ~signal dr (t + k))
          else
            signal dr (t + k))` THENL
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
         `dr : wire`; `t : cycle`] case1_signal) THEN
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
    `signal dr (t + SUC k) <=>
     signal dr (t + k) \/ signal cr2 (t + k)`
    SUBST1_TAC THENL
  [MP_TAC
     (SPECL
        [`ld : wire`; `ground`; `dq : wire`;
         `dr : wire`; `t + SUC k`] case1_signal) THEN
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
        [`dr : wire`; `dp : wire`; `t + k : cycle`]
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

let counter_signal = prove
 (`!n ld nb dn t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n + 2 = 2 EXP (width nb) + width nb /\
     counter ld nb dn ==>
     (signal dn (t + k) <=> n < k)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `k = 0` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   REWRITE_TAC [LT_ZERO; ADD_0; LE_ZERO] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [counter_def] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`dr : wire`;
         `dn : wire`;
         `t : cycle`]
        connect_signal) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `ground`;
         `dq : wire`;
         `dr : wire`;
         `t : cycle`]
        case1_signal) THEN
   ASM_REWRITE_TAC [ground_signal];
   ALL_TAC] THEN
  SUBGOAL_THEN `n + 2 = SUC (SUC n)` SUBST1_TAC THENL
  [REWRITE_TAC [TWO; ONE; ADD_SUC; ADD_0];
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM LT_SUC))) THEN
  SUBGOAL_THEN
    `width nb <= SUC n`
    (X_CHOOSE_THEN `m : num` MP_TAC o
     ONCE_REWRITE_RULE [ADD_SYM] o
     REWRITE_RULE [LE_EXISTS]) THENL
  [CONV_TAC (REWR_CONV (GSYM (SPEC `2 EXP (width nb)` LE_ADD_LCANCEL))) THEN
   FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [GSYM ADD1; ADD_SUC; LE_SUC_LT; LT_ADD_RCANCEL; LT_SUC] THEN
   MP_TAC (SPEC `bsignal nb t` bits_to_num_bound) THEN
   REWRITE_TAC [length_bsignal];
   ALL_TAC] THEN
  DISCH_THEN (fun th ->
    REPEAT (POP_ASSUM MP_TAC) THEN
    SUBST1_TAC th) THEN
  REWRITE_TAC [GSYM SUC_ADD; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
  REWRITE_TAC [ADD1] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [GSYM ADD1; LT_SUC_LE] THEN
  SUBGOAL_THEN
    `?f : cycle -> cycle.
       f 0 = 0 /\
       !u. f (SUC u) = SUC (f u) + (if signal ld u then 1 else 0)`
    STRIP_ASSUME_TAC THENL
  [MP_TAC
     (ISPECL
        [`0`;
         `\fu u. SUC fu + (if signal ld u then 1 else 0)`]
        num_RECURSION) THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!u1 u2. (f : cycle -> cycle) u1 <= f u2 <=> u1 <= u2`
    STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC [MONO_SIMPLIFY; SUC_ADD; LT_SUC_LE; LE_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!u1 u2. (f : cycle -> cycle) u1 = f u2 <=> u1 = u2`
    STRIP_ASSUME_TAC THENL
  [ASM_REWRITE_TAC [GSYM LE_ANTISYM];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?g : cycle -> cycle # cycle.
       g 0 = (0,0) /\
       !u j k.
         g u = (j,k) <=>
         f t + u = f (t + j) + k /\
         signal ld (t + j) /\
         (!i. SUC i < k ==> ~signal ld ((t + j) + SUC i))`
    STRIP_ASSUME_TAC THENL
  [EXISTS_TAC
     `\u.
        let mi = (minimal i. ?j. f t + u = f (t + j) + i /\
                  signal ld (t + j)) in
        ((@j. f t + u = f (t + j) + mi), mi)` THEN
   REWRITE_TAC [ADD_0] THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `(minimal i. ?j. f t = f (t + j) + i /\ signal ld (t + j)) = 0`
      SUBST1_TAC THENL
    [MATCH_MP_TAC MINIMAL_EQ THEN
     REWRITE_TAC [LT_ZERO; ADD_0] THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [ADD_0] THEN
     UNDISCH_THEN
       `!i. i <= k ==> (signal ld (t + i) <=> i = 0)`
       (MP_TAC o SPEC `0`) THEN
     REWRITE_TAC [LE_0; ADD_0];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ; ADD_0] THEN
    MATCH_MP_TAC SELECT_UNIQUE THEN
    X_GEN_TAC `j : cycle` THEN
    REWRITE_TAC [] THEN
    CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
    MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_0;
    ALL_TAC] THEN
   GEN_TAC THEN
   GEN_TAC THEN
   X_GEN_TAC `p : cycle` THEN
   SUBGOAL_THEN
     `?i j. (f : cycle -> cycle) t + u = f (t + j) + i /\ signal ld (t + j)`
     (MP_TAC o CONV_RULE (REWR_CONV MINIMAL)) THENL
   [EXISTS_TAC `u : cycle` THEN
    EXISTS_TAC `0` THEN
    UNDISCH_THEN
      `!i. i <= k ==> (signal ld (t + i) <=> i = 0)`
      (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [ADD_0; LE_0];
    ALL_TAC] THEN
   SPEC_TAC
     (`minimal i. ?j.
         (f : cycle -> cycle) t + u = f (t + j) + i /\ signal ld (t + j)`,
      `n : cycle`) THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
   X_GEN_TAC `q : cycle` THEN
   DISCH_THEN
     (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `mj : cycle` STRIP_ASSUME_TAC)
        MP_TAC) THEN
   UNDISCH_THEN
     `(f : cycle -> cycle) t + u = f (t + mj) + q`
     SUBST1_TAC THEN
   DISCH_THEN
     (STRIP_ASSUME_TAC o
      REWRITE_RULE
        [NOT_EXISTS_THM; GSYM RIGHT_FORALL_IMP_THM; IMP_IMP;
         TAUT `!x y. ~(x /\ y) <=> x ==> ~y`]) THEN
   ASM_REWRITE_TAC [EQ_ADD_RCANCEL; EQ_ADD_LCANCEL] THEN
   SUBGOAL_THEN
     `(@j : cycle. mj = j) = mj`
     SUBST1_TAC THENL
   [MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC [] THEN
    GEN_TAC THEN
    MATCH_ACCEPT_TAC EQ_SYM_EQ;
    ALL_TAC] THEN
   EQ_TAC THENL
   [DISCH_THEN (CONJUNCTS_THEN SUBST_VAR_TAC) THEN
    ASM_REWRITE_TAC [] THEN
    GEN_TAC THEN
    STRIP_TAC THEN
    POP_ASSUM
      (X_CHOOSE_THEN `d : num` SUBST_VAR_TAC o
       REWRITE_RULE [LT_EXISTS]) THEN
    POP_ASSUM
      (STRIP_ASSUME_TAC o
       REWRITE_RULE [GSYM ADD_SUC] o
       ONCE_REWRITE_RULE [GSYM SUC_ADD] o
       REWRITE_RULE [ADD_SUC; LT_SUC_LE; ADD_ASSOC]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `d : cycle` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LE_ADDR];
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    POP_ASSUM MP_TAC THEN
    SPEC_TAC (`i : cycle`, `i : cycle`) THEN
    INDUCT_TAC THENL
    [DISCH_THEN (K ALL_TAC) THEN
     ASM_REWRITE_TAC [ADD_SUC; ADD_0; GSYM ADD1];
     ALL_TAC] THEN
    DISCH_THEN (fun th -> POP_ASSUM MP_TAC THEN STRIP_ASSUME_TAC th) THEN
    ANTS_TAC THENL
    [X_GEN_TAC `q : num` THEN
     X_GEN_TAC `p : num` THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     EXISTS_TAC `SUC q` THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [ADD_SUC; SUC_ADD; LE_SUC; SUC_INJ] THEN
     STRIP_TAC THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    STRIP_TAC THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV ADD_SUC))) THEN
    ASM_REWRITE_TAC [] THEN
    STP_TAC `~signal ld ((t + j) + SUC i)` THENL
    [STRIP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SUC)) THEN
     ASM_REWRITE_TAC [ADD_0; SUC_INJ; ADD_ASSOC];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `SUC d` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [LE_SUC_LT; LT_ADDR; LT_0];
     ONCE_REWRITE_TAC [ADD_SUC] THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [SUC_ADD]];
    ALL_TAC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`p : cycle`; `j : cycle`]) THEN
   ASM_REWRITE_TAC [NOT_LT] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `d : cycle` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   SUBGOAL_THEN `(j : cycle) <= mj`
     (X_CHOOSE_THEN `dj : cycle` SUBST_VAR_TAC o
      REWRITE_RULE [LE_EXISTS]) THENL
   [MP_TAC
      (SPECL
         [`(f : cycle -> cycle) (t + j) + q`; `d : cycle`]
         LE_ADD) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    FIRST_X_ASSUM (CONV_TAC o LAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
    ASM_REWRITE_TAC [LE_ADD_RCANCEL; LE_ADD_LCANCEL];
    ALL_TAC] THEN
   UNDISCH_THEN
     `(f : cycle -> cycle) (t + j + dj) + q = f (t + j) + q + d`
     (MP_TAC o
      REWRITE_RULE [GSYM ADD_ASSOC] o
      REWRITE_RULE [ADD_ASSOC; EQ_ADD_RCANCEL] o
      CONV_RULE (RAND_CONV (RAND_CONV (REWR_CONV ADD_SYM)))) THEN
   MP_TAC (SPEC `dj : cycle` num_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
        SUBST_VAR_TAC
        (X_CHOOSE_THEN `ds : cycle` SUBST_VAR_TAC)) THENL
   [ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    REWRITE_TAC [ADD_0; EQ_ADD_LCANCEL_0];
    ALL_TAC] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `ds : cycle`) THEN
   REVERSE_TAC ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `d : cycle` THEN
   REWRITE_TAC [LE_ADDR] THEN
   SUBGOAL_THEN
     `(f : cycle -> cycle) (t + j + SUC ds) <= f (t + j) + d`
     MP_TAC THENL
   [ASM_REWRITE_TAC [LE_REFL];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   UNDISCH_THEN `signal ld (t + j + SUC ds)` (K ALL_TAC) THEN
   SPEC_TAC (`d : cycle`, `d : cycle`) THEN
   SPEC_TAC (`ds : cycle`, `i : cycle`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    ASM_REWRITE_TAC [ADD_SUC; ADD_0; SUC_ADD] THEN
    REWRITE_TAC [GSYM ADD_SUC; LE_ADD_LCANCEL] THEN
    REWRITE_TAC [LE_SUC_LT; ONE];
    ALL_TAC] THEN
   GEN_TAC THEN
   SUBGOAL_THEN
     `t + j + SUC (SUC i) = SUC (t + j + SUC i)`
     SUBST1_TAC THENL
   [REWRITE_TAC [ADD_SUC];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `d : cycle` num_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
        SUBST_VAR_TAC
        (X_CHOOSE_THEN `ds : cycle` SUBST_VAR_TAC)) THENL
   [REWRITE_TAC [LT_ZERO; ADD_0; SUC_ADD; LE_SUC_LT; NOT_LT] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(f : cycle -> cycle) (t + j + SUC i)` THEN
    ASM_REWRITE_TAC [LE_ADD; ADD_ASSOC];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [ADD_SUC; SUC_ADD; LT_SUC] THEN
   REWRITE_TAC [LE_SUC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC
     `(f : cycle -> cycle) (t + j + SUC i) +
      (if signal ld (t + j + SUC i) then 1 else 0)` THEN
   ASM_REWRITE_TAC [LE_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!h. ?gw. !u. signal gw u = UNCURRY h ((g : num -> num # num) u)`
    (X_CHOOSE_THEN `gw : (cycle -> cycle -> bool) -> wire` STRIP_ASSUME_TAC o
     CONV_RULE (REWR_CONV SKOLEM_THM)) THENL
  [GEN_TAC THEN
   EXISTS_TAC
     `mk_wire
        (stream (\u. UNCURRY h ((g : num -> num # num) u)))` THEN
   GEN_TAC THEN
   REWRITE_TAC [signal_def; wire_tybij; stream_snth];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= k + 1 ==> (g : cycle -> cycle # cycle) i = (0,i)`
    STRIP_ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [ADD_0] THEN
   CONJ_TAC THENL
   [UNDISCH_THEN
      `!i. i <= k ==> (signal ld (t + i) <=> i = 0)`
      (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [LE_0; ADD_0];
    X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    UNDISCH_THEN
      `!i. i <= k ==> (signal ld (t + i) <=> i = 0)`
      (MP_TAC o SPEC `SUC j`) THEN
    ASM_REWRITE_TAC [NOT_SUC; LE_SUC_LT] THEN
    REVERSE_TAC ANTS_TAC THENL
    [REWRITE_TAC [];
     ALL_TAC] THEN
    CONV_TAC (REWR_CONV (GSYM LT_SUC)) THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `i : cycle` THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [ADD1]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?ld'. (gw : (num -> num -> bool) -> wire) (\j k. k = 0) = ld'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?dn'.
       (gw : (num -> num -> bool) -> wire)
       (\j k. 1 < k /\ signal dn (t + j + (k - 1))) = dn'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?nb'.
       width nb' = width nb /\
       (!u.
          bsignal nb' u =
          UNCURRY (\j k. bsignal nb (t + j))
            ((g : cycle -> cycle # cycle) u)) /\
       blift2
         (\nbi nbi'.
            nbi' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. signal nbi (t + j))) nb nb'`
    STRIP_ASSUME_TAC THENL
  [MP_TAC
     (SPEC `\nbi nbi'.
               nbi' = (gw : (cycle -> cycle -> bool) -> wire)
                      (\j k. signal nbi (t + j))` blift2_exists) THEN
   REWRITE_TAC [EXISTS_REFL] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `nb' : bus` STRIP_ASSUME_TAC o
      SPEC `nb : bus`) THEN
   EXISTS_TAC `nb' : bus` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC blift2_width_out THEN
    EXISTS_TAC
      `\nbi nbi'.
          nbi' = (gw : (cycle -> cycle -> bool) -> wire)
                 (\j k. signal nbi (t + j))` THEN
    EXISTS_TAC `nb : bus` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [bsignal_def] THEN
   SUBGOAL_THEN
     `dest_bus nb' =
      MAP (\nbi. (gw : (cycle -> cycle -> bool) -> wire)
                 (\j k. signal nbi (t + j))) (dest_bus nb)`
     SUBST1_TAC THENL
   [POP_ASSUM MP_TAC THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    SPEC_TAC (`nb' : bus`, `nb' : bus`) THEN
    SPEC_TAC (`nb : bus`, `nb : bus`) THEN
    MATCH_MP_TAC blift2_induct THEN
    REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THENL
    [REWRITE_TAC [bnil_def; bus_tybij; MAP_NIL];
     ASM_REWRITE_TAC
       [bappend_def; bwire_def; bus_tybij; APPEND_SING; MAP_CONS]];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM MAP_o; o_DEF] THEN
   MP_TAC (ISPEC `(g : cycle -> cycle # cycle) u` PAIR_SURJECTIVE) THEN
   DISCH_THEN
    (X_CHOOSE_THEN `gj : cycle`
      (X_CHOOSE_THEN `gk : cycle` SUBST1_TAC)) THEN
   REWRITE_TAC [UNCURRY_DEF];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`m + 1 : num`;
        `ld' : wire`;
        `nb' : bus`;
        `power`;
        `dn' : wire`;
        `0`;
        `k + 1 : cycle`]
       event_counter_signal) THEN
  REVERSE_TAC ANTS_TAC THENL
  [UNDISCH_THEN
     `!i. i <= k + 1 ==> (g : cycle -> cycle # cycle) i = (0,i)`
     (STRIP_ASSUME_TAC o REWRITE_RULE [LE_REFL] o SPEC `k + 1`) THEN
   UNDISCH_THEN
     `(gw : (num -> num -> bool) -> wire)
      (\j k. 1 < k /\ signal dn (t + j + (k - 1))) = dn'`
     SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [ZERO_ADD; UNCURRY_DEF; LT_ADDR; ADD_SUB; LT_NZ] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [power_signal; GSYM ADD1; NOT_SUC; GSYM LE_SUC_LT] THEN
   SUBGOAL_THEN
     `{i | ~(i = 0) /\ i + width nb <= SUC k} = {SUC i | i + width nb <= k}`
     SUBST1_TAC THENL
   [REWRITE_TAC [EXTENSION] THEN
    X_GEN_TAC `x : num` THEN
    REWRITE_TAC [IN_ELIM] THEN
    REWRITE_TAC [IN_ELIM_THM] THEN
    DISJ_CASES_THEN2
      SUBST_VAR_TAC
      (X_CHOOSE_THEN `xs : num` SUBST_VAR_TAC)
      (SPEC `x : num` num_CASES) THENL
    [REWRITE_TAC [NOT_SUC];
     REWRITE_TAC [NOT_SUC; SUC_ADD; LE_SUC; SUC_INJ; UNWIND_THM1]];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_CASES_TAC `k < width nb` THENL
   [POP_ASSUM
      (X_CHOOSE_THEN `d : num` SUBST1_TAC o
       REWRITE_RULE [LT_EXISTS]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL_0] THEN
    REWRITE_TAC [SUC_ADD; NOT_SUC; EMPTY_GSPEC; CARD_EMPTY; LE_ZERO];
    ALL_TAC] THEN
   POP_ASSUM
     (X_CHOOSE_THEN `d : num` SUBST1_TAC o
      REWRITE_RULE [LE_EXISTS; NOT_LT]) THEN
   REWRITE_TAC [LE_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM LE_SUC))) THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `CARD (IMAGE SUC { i | i <= d })` THEN
   CONJ_TAC THENL
   [AP_TERM_TAC THEN
    REWRITE_TAC [EXTENSION] THEN
    X_GEN_TAC `x : num` THEN
    REWRITE_TAC [IN_IMAGE; IN_ELIM] THEN
    REWRITE_TAC [IN_ELIM_THM];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `CARD { i : num | i <= d }` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN
    REWRITE_TAC [SUC_INJ; FINITE_NUMSEG_LE] THEN
    REPEAT STRIP_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [CARD_NUMSEG_LE; ADD1];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT STRIP_TAC THEN
   UNDISCH_THEN
     `(gw : (num -> num -> bool) -> wire) (\j k. k = 0) = ld'`
     SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   UNDISCH_THEN
     `!i. i <= k + 1 ==> (g : cycle -> cycle # cycle) i = (0,i)`
     (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [ASM_REWRITE_TAC [UNCURRY_DEF; ADD_0];
   ALL_TAC] THEN
  POP_ASSUM_LIST
    (let discard asm = free_in `k : cycle` asm or free_in `m : num` asm in
     let process th = if discard (concl th) then ALL_TAC else ASSUME_TAC th in
     EVERY o map process o rev) THEN
  UNDISCH_TAC `counter ld nb dn` THEN
  REWRITE_TAC [counter_def; event_counter_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `?sr0'. (gw : (cycle -> cycle -> bool) -> wire)
            (\j k. if k = 0 then signal cr0 (t + j)
                   else ~signal cr0 (t + j + (k - 1))) = sr0'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sr1'.
       blift2
         (\sri sri'.
            sri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. if k = 0 then signal sri (t + j)
                          else signal sri (t + j + (k - 1)))) sr sr1'`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC (REWRITE_RULE [GSYM RIGHT_FORALL_IMP_THM] blift2_exists) THEN
   X_GEN_TAC `sri : wire` THEN
   REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC EXISTS_REFL;
   ALL_TAC] THEN
  SUBGOAL_THEN `width sr1' = r` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC blift2_width_out THEN
   EXISTS_TAC
     `\sri sri'.
        sri' = (gw : (cycle -> cycle -> bool) -> wire)
               (\j k. if k = 0 then signal sri (t + j)
                      else signal sri (t + j + (k - 1)))` THEN
   EXISTS_TAC `sr : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sr'. bappend (bwire sr0') sr1' = sr'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN `width sr' = r + 1` STRIP_ASSUME_TAC THENL
  [ONCE_REWRITE_TAC [ADD_SYM] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [bappend_width; bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN `wire sr' 0 sr0'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  SUBGOAL_THEN `bsub sr' 1 r sr1'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MP_TAC (SPECL [`bwire sr0'`; `sr1' : bus`; `sr1' : bus`] bsub_suffix) THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?cr'.
       blift2
         (\cri cri'.
            cri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))) cr cr'`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC (REWRITE_RULE [GSYM RIGHT_FORALL_IMP_THM] blift2_exists) THEN
   X_GEN_TAC `cri : wire` THEN
   REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC EXISTS_REFL;
   ALL_TAC] THEN
  SUBGOAL_THEN `width cr' = r + 1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC blift2_width_out THEN
   EXISTS_TAC
     `\cri cri'.
        cri' = (gw : (cycle -> cycle -> bool) -> wire)
               (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))` THEN
   EXISTS_TAC `cr : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?cr2'. wire cr' r cr2'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sp'. bdelay sr' sp'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC bdelay_exists;
   ALL_TAC] THEN
  SUBGOAL_THEN `width sp' = r + 1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bdelay_width_out THEN
   EXISTS_TAC `sr' : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?sp0'. wire sp' 0 sp0'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; LT_NZ; NOT_SUC];
   ALL_TAC] THEN
  SUBGOAL_THEN `?sp1'. bsub sp' 1 r sp1'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN `width sp1' = r` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `sp' : bus` THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?cp'. bdelay cr' cp'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC bdelay_exists;
   ALL_TAC] THEN
  SUBGOAL_THEN `width cp' = r + 1` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bdelay_width_out THEN
   EXISTS_TAC `cr' : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?cp0'. wire cp' 0 cp0'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; LT_NZ; NOT_SUC];
   ALL_TAC] THEN
  SUBGOAL_THEN `?cp1'. bsub cp' 0 r cp1'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_exists THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM ADD1; SUC_LE];
   ALL_TAC] THEN
  SUBGOAL_THEN `width cp1' = r` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `cp' : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `?cp2'. wire cp' r cp2'` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?dp'. delay dn' dp'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC delay_exists;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sq0'. not sp0' sq0'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC not_exists;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?cq0'. connect sp0' cq0'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC connect_exists;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sq1' cq1'. badder2 sp1' cp1' sq1' cq1'`
    STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC badder2_exists THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width sq1' = r` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC badder2_width_out1 THEN
   EXISTS_TAC `sp1' : bus` THEN
   EXISTS_TAC `cp1' : bus` THEN
   EXISTS_TAC `cq1' : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width cq1' = r` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC badder2_width_out2 THEN
   EXISTS_TAC `sp1' : bus` THEN
   EXISTS_TAC `cp1' : bus` THEN
   EXISTS_TAC `sq1' : bus` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?sq'. bappend (bwire sq0') sq1' = sq'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN `width sq' = r + 1` STRIP_ASSUME_TAC THENL
  [ONCE_REWRITE_TAC [ADD_SYM] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [bappend_width; bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN `wire sq' 0 sq0'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  SUBGOAL_THEN `bsub sq' 1 r sq1'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MP_TAC (SPECL [`bwire sq0'`; `sq1' : bus`; `sq1' : bus`] bsub_suffix) THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?cq'. bappend (bwire cq0') cq1' = cq'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  SUBGOAL_THEN `width cq' = r + 1` STRIP_ASSUME_TAC THENL
  [ONCE_REWRITE_TAC [ADD_SYM] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [bappend_width; bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN `wire cq' 0 cq0'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [wire_zero];
   ALL_TAC] THEN
  SUBGOAL_THEN `bsub cq' 1 r cq1'` STRIP_ASSUME_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MP_TAC (SPECL [`bwire cq0'`; `cq1' : bus`; `cq1' : bus`] bsub_suffix) THEN
   ASM_REWRITE_TAC [bwire_width];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `?dq'. or2 dp' cp2' dq'`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC or2_exists;
   ALL_TAC] THEN
  EXISTS_TAC `r : num` THEN
  EXISTS_TAC `sp' : bus` THEN
  EXISTS_TAC `cp' : bus` THEN
  EXISTS_TAC `sq' : bus` THEN
  EXISTS_TAC `cq' : bus` THEN
  EXISTS_TAC `sr' : bus` THEN
  EXISTS_TAC `cr' : bus` THEN
  EXISTS_TAC `dp' : wire` THEN
  EXISTS_TAC `dq' : wire` THEN
  EXISTS_TAC `dn' : wire` THEN
  EXISTS_TAC `sp0' : wire` THEN
  EXISTS_TAC `sp1' : bus` THEN
  EXISTS_TAC `cp0' : wire` THEN
  EXISTS_TAC `cp1' : bus` THEN
  EXISTS_TAC `cp2' : wire` THEN
  EXISTS_TAC `sq0' : wire` THEN
  EXISTS_TAC `sq1' : bus` THEN
  EXISTS_TAC `cq0' : wire` THEN
  EXISTS_TAC `cq1' : bus` THEN
  ASM_REWRITE_TAC [connect_refl] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC xor2_left_power THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC and2_left_power THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!u j k.
       (g : cycle -> cycle # cycle) u = (j, SUC k) ==>
       ?us. u = SUC us /\ g us = (j,k)`
    STRIP_ASSUME_TAC THENL
  [REPEAT GEN_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MP_TAC (SPEC `u : num` num_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
        SUBST_VAR_TAC
        (X_CHOOSE_THEN `us : num` SUBST_VAR_TAC)) THENL
   [REWRITE_TAC [ADD_0; NOT_SUC] THEN
    STRIP_TAC THEN
    UNDISCH_THEN
      `!u1 u2. (f : cycle -> cycle) u1 <= f u2 <=> u1 <= u2`
      (MP_TAC o SPECL [`t : cycle`; `t + j : cycle`]) THEN
    ASM_REWRITE_TAC [LE_ADD; NOT_LE; LT_ADD; LT_NZ; NOT_SUC];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [ADD_SUC; SUC_INJ; LT_SUC; UNWIND_THM1] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LT_TRANS THEN
   EXISTS_TAC `SUC i` THEN
   ASM_REWRITE_TAC [SUC_LT];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bcase1_def; blift3_def] THEN
   EXISTS_TAC `r + 1` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `i : num` THEN
   X_GEN_TAC `nbi' : wire` THEN
   X_GEN_TAC `sqi' : wire` THEN
   X_GEN_TAC `sri' : wire` THEN
   STRIP_TAC THEN
   REWRITE_TAC [case1_def] THEN
   X_GEN_TAC `u : cycle` THEN
   MP_TAC (ISPEC `(g : cycle -> cycle # cycle) u` PAIR_SURJECTIVE) THEN
   DISCH_THEN
    (X_CHOOSE_THEN `j : cycle`
      (X_CHOOSE_THEN `k : cycle` STRIP_ASSUME_TAC)) THEN
   FIND_ASSUM
     (SUBST1_TAC o SYM)
     `(gw : (num -> num -> bool) -> wire) (\j k. k = 0) = ld'` THEN
   ASM_REWRITE_TAC [UNCURRY_DEF] THEN
   COND_CASES_TAC THENL
   [MP_TAC (SPEC `i : num` num_CASES) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2
        SUBST_VAR_TAC
        (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC)) THENL
    [SUBGOAL_THEN `sri' = (sr0' : wire)` SUBST_VAR_TAC THENL
     [MATCH_MP_TAC wire_inj THEN
      EXISTS_TAC `sr' : bus` THEN
      EXISTS_TAC `0` THEN
      ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     FIND_ASSUM
       (SUBST1_TAC o SYM)
       `(gw : (cycle -> cycle -> bool) -> wire)
        (\j k. if k = 0 then signal cr0 (t + j)
               else ~signal cr0 (t + j + (k - 1))) = sr0'` THEN
     MP_TAC
       (SPECL
          [`\nbi nbi'.
              nbi' = (gw : (cycle -> cycle -> bool) -> wire)
                     (\j k. signal nbi (t + j))`;
           `nb : bus`;
           `nb' : bus`;
           `0`;
           `nb0 : wire`;
           `nbi' : wire`]
          blift2_wire) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     ASM_REWRITE_TAC [UNCURRY_DEF] THEN
     MP_TAC
       (SPECL
          [`ld : wire`;
           `nb0 : wire`;
           `cq0 : wire`;
           `cr0 : wire`;
           `t + j: cycle`]
          case1_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     UNDISCH_TAC `(g : cycle -> cycle # cycle) u = (j,k)` THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `(is : num) < r` STRIP_ASSUME_TAC THENL
    [MP_TAC (SPECL [`nb' : bus`; `SUC is`; `nbi' : wire`] wire_bound) THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [GSYM ADD1; LT_SUC];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
        [`sr' : bus`;
         `1`;
         `r : num`;
         `sr1' : bus`;
         `is : num`;
         `sri' : wire`]
        bsub_wire) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?sri. wire sr is sri` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC wire_exists THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `?nbi. wire nb (SUC is) nbi` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC wire_exists THEN
     ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`\sri sri'.
             sri' = (gw : (cycle -> cycle -> bool) -> wire)
                    (\j k. if k = 0 then signal sri (t + j)
                           else signal sri (t + j + (k - 1)))`;
          `sr : bus`;
          `sr1' : bus`;
          `is : num`;
          `sri : wire`;
          `sri' : wire`]
         blift2_wire) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL
         [`\nbi nbi'.
              nbi' = (gw : (cycle -> cycle -> bool) -> wire)
                     (\j k. signal nbi (t + j))`;
          `nb : bus`;
          `nb' : bus`;
          `SUC is`;
          `nbi : wire`;
          `nbi' : wire`]
         blift2_wire) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [UNCURRY_DEF] THEN
    SUBGOAL_THEN `?sqi. wire sq is sqi` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC wire_exists THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
        [`nb : bus`;
         `1`;
         `r : num`;
         `nb1 : bus`;
         `is : num`;
         `nbi : wire`]
        bsub_wire) THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `nb1 : bus`;
          `sq : bus`;
          `sr : bus`;
          `is : num`;
          `nbi : wire`;
          `sqi : wire`;
          `sri : wire`]
         bcase1_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `nbi : wire`;
          `sqi : wire`;
          `sri : wire`;
          `t + j : cycle`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(g : cycle -> cycle # cycle) u = (j,k)` THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPEC `k : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `ks : cycle` SUBST_VAR_TAC) THEN
   MP_TAC (SPEC `i : num` num_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC)) THENL
   [SUBGOAL_THEN `sri' = (sr0' : wire)` SUBST_VAR_TAC THENL
    [MATCH_MP_TAC wire_inj THEN
     EXISTS_TAC `sr' : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    SUBGOAL_THEN `sqi' = (sq0' : wire)` SUBST_VAR_TAC THENL
    [MATCH_MP_TAC wire_inj THEN
     EXISTS_TAC `sq' : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`sp0' : wire`;
          `sq0' : wire`;
          `u : cycle`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM
      (MP_TAC o SPECL [`u : cycle`; `j : cycle`; `ks : cycle`]) THEN
    ANTS_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC
      (SPECL [`sr' : bus`; `sp' : bus`; `0`;
              `sr0' : wire`; `sp0' : wire`] bdelay_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL [`sr0' : wire`; `sp0' : wire`; `us : cycle`] delay_signal) THEN
    ASM_REWRITE_TAC [GSYM ADD1] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIND_ASSUM
      (SUBST1_TAC o SYM)
      `(gw : (cycle -> cycle -> bool) -> wire)
       (\j k. if k = 0 then signal cr0 (t + j)
              else ~signal cr0 (t + j + (k - 1))) = sr0'` THEN
    ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [ADD_0];
     ALL_TAC] THEN
    MP_TAC (SPEC `ks : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `kss : cycle` SUBST_VAR_TAC) THEN
    REWRITE_TAC [SUC_SUB1] THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `nb0 : wire`;
          `cq0 : wire`;
          `cr0 : wire`;
          `t + j + SUC kss`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `signal ld (t + j + SUC kss) <=> F` SUBST1_TAC THENL
    [UNDISCH_TAC
       `(g : cycle -> cycle # cycle) (SUC us) = (j, SUC (SUC kss))` THEN
     ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [SUC_LT];
     ALL_TAC] THEN
    REWRITE_TAC [ADD_SUC] THEN
    MP_TAC
      (SPECL
         [`cp0 : wire`;
          `cq0 : wire`;
          `SUC (t + j + kss)`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC
      (SPECL [`cr : bus`; `cp : bus`; `0`;
              `cr0 : wire`; `cp0 : wire`] bdelay_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
        [`cr0 : wire`; `cp0 : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
    ASM_REWRITE_TAC [GSYM ADD1];
    ALL_TAC] THEN
   SUBGOAL_THEN `(is : num) < r` STRIP_ASSUME_TAC THENL
   [MP_TAC (SPECL [`nb' : bus`; `SUC is`; `nbi' : wire`] wire_bound) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   SUBGOAL_THEN `?spi'. wire sp' (SUC is) spi'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cpi'. wire cp' is cpi'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sq' : bus`;
         `1`;
         `r : num`;
         `sq1' : bus`;
         `is : num`;
         `sqi' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp' : bus`;
         `1`;
         `r : num`;
         `sp1' : bus`;
         `is : num`;
         `spi' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`cp' : bus`;
         `0`;
         `r : num`;
         `cp1' : bus`;
         `is : num`;
         `cpi' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp1' : bus`; `cp1' : bus`; `sq1' : bus`; `cq1' : bus`]
        badder2_def) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp1' : bus`;
         `cp1' : bus`;
         `sq1' : bus`;
         `is : num`;
         `spi' : wire`;
         `cpi' : wire`;
         `sqi' : wire`]
        bxor2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`spi' : wire`;
         `cpi' : wire`;
         `sqi' : wire`;
         `u : cycle`]
        xor2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM
     (MP_TAC o SPECL [`u : cycle`; `j : cycle`; `ks : cycle`]) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   SUBGOAL_THEN `?cri'. wire cr' is cri'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL [`sr' : bus`; `sp' : bus`; `SUC is`;
             `sri' : wire`; `spi' : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL [`sri' : wire`; `spi' : wire`; `us : cycle`] delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`cr' : bus`; `cp' : bus`; `is : num`;
             `cri' : wire`; `cpi' : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL [`cri' : wire`; `cpi' : wire`; `us : cycle`] delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
       [`sr' : bus`;
        `1`;
        `r : num`;
        `sr1' : bus`;
        `is : num`;
        `sri' : wire`]
       bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `?sri. wire sr is sri` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`\sri sri'.
            sri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. if k = 0 then signal sri (t + j)
                          else signal sri (t + j + (k - 1)))`;
         `sr : bus`;
         `sr1' : bus`;
         `is : num`;
         `sri : wire`;
         `sri' : wire`]
        blift2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
   SUBGOAL_THEN `?cri. wire cr is cri` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`\cri cri'.
            cri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
         `cr : bus`;
         `cr' : bus`;
         `is : num`;
         `cri : wire`;
         `cri' : wire`]
        blift2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [ADD_0];
    ALL_TAC] THEN
   MP_TAC (SPEC `ks : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `kss : cycle` SUBST_VAR_TAC) THEN
   REWRITE_TAC [SUC_SUB1] THEN
   SUBGOAL_THEN `?nbi. wire nb (SUC is) nbi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   SUBGOAL_THEN `?sqi. wire sq is sqi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
       [`nb : bus`;
        `1`;
        `r : num`;
        `nb1 : bus`;
        `is : num`;
        `nbi : wire`]
       bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `nb1 : bus`;
         `sq : bus`;
         `sr : bus`;
         `is : num`;
         `nbi : wire`;
         `sqi : wire`;
         `sri : wire`]
        bcase1_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `nbi : wire`;
         `sqi : wire`;
         `sri : wire`;
         `t + j + SUC kss`]
        case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `signal ld (t + j + SUC kss) <=> F` SUBST1_TAC THENL
   [UNDISCH_TAC
      `(g : cycle -> cycle # cycle) (SUC us) = (j, SUC (SUC kss))` THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [SUC_LT];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_SUC] THEN
   SUBGOAL_THEN `?spi. wire sp is spi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cpi. wire cp is cpi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`cp : bus`;
         `0`;
         `r : num`;
         `cp1 : bus`;
         `is : num`;
         `cpi : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp : bus`; `cp1 : bus`; `sq : bus`; `cq1 : bus`]
        badder2_def) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp : bus`;
         `cp1 : bus`;
         `sq : bus`;
         `is : num`;
         `spi : wire`;
         `cpi : wire`;
         `sqi : wire`]
        bxor2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`spi : wire`;
         `cpi : wire`;
         `sqi : wire`;
         `SUC (t + j + kss) : cycle`]
        xor2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`sr : bus`; `sp : bus`; `is : num`;
             `sri : wire`; `spi : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sri : wire`; `spi : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`cr : bus`; `cp : bus`; `is : num`;
             `cri : wire`; `cpi : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`cri : wire`; `cpi : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bcase1_def; blift3_def] THEN
   EXISTS_TAC `r + 1` THEN
   ASM_REWRITE_TAC [bground_width; bground_wire] THEN
   X_GEN_TAC `i : num` THEN
   X_GEN_TAC `gnd : wire` THEN
   X_GEN_TAC `cqi' : wire` THEN
   X_GEN_TAC `cri' : wire` THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [case1_def] THEN
   X_GEN_TAC `u : cycle` THEN
   MP_TAC (ISPEC `(g : cycle -> cycle # cycle) u` PAIR_SURJECTIVE) THEN
   DISCH_THEN
    (X_CHOOSE_THEN `j : cycle`
      (X_CHOOSE_THEN `k : cycle` STRIP_ASSUME_TAC)) THEN
   FIND_ASSUM
     (SUBST1_TAC o SYM)
     `(gw : (num -> num -> bool) -> wire) (\j k. k = 0) = ld'` THEN
   ASM_REWRITE_TAC [UNCURRY_DEF] THEN
   COND_CASES_TAC THENL
   [SUBGOAL_THEN `?cri. wire cr i cri` STRIP_ASSUME_TAC THENL
    [MATCH_MP_TAC wire_exists THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`\cri cri'.
             cri' = (gw : (cycle -> cycle -> bool) -> wire)
                    (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
          `cr : bus`;
          `cr' : bus`;
          `i : num`;
          `cri : wire`;
          `cri' : wire`]
         blift2_wire) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [UNCURRY_DEF; ground_signal];
    ALL_TAC] THEN
   MP_TAC (SPEC `k : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `ks : cycle` SUBST_VAR_TAC) THEN
   MP_TAC (SPEC `i : num` num_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC)) THENL
   [SUBGOAL_THEN `cqi' = (cq0' : wire)` SUBST_VAR_TAC THENL
    [MATCH_MP_TAC wire_inj THEN
     EXISTS_TAC `cq' : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`sp0' : wire`;
          `cq0' : wire`;
          `u : cycle`]
         connect_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM
      (MP_TAC o SPECL [`u : cycle`; `j : cycle`; `ks : cycle`]) THEN
    ANTS_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC
      (SPECL [`sr' : bus`; `sp' : bus`; `0`;
              `sr0' : wire`; `sp0' : wire`] bdelay_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL [`sr0' : wire`; `sp0' : wire`; `us : cycle`] delay_signal) THEN
    ASM_REWRITE_TAC [GSYM ADD1] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIND_ASSUM
      (SUBST1_TAC o SYM)
      `(gw : (cycle -> cycle -> bool) -> wire)
       (\j k. if k = 0 then signal cr0 (t + j)
              else ~signal cr0 (t + j + (k - 1))) = sr0'` THEN
    ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
    MP_TAC
      (SPECL
         [`\cri cri'.
             cri' = (gw : (cycle -> cycle -> bool) -> wire)
                    (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
          `cr : bus`;
          `cr' : bus`;
          `0 : num`;
          `cr0 : wire`;
          `cri' : wire`]
         blift2_wire) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [ADD_0];
     ALL_TAC] THEN
    MP_TAC (SPEC `ks : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `kss : cycle` SUBST_VAR_TAC) THEN
    REWRITE_TAC [SUC_SUB1] THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `nb0 : wire`;
          `cq0 : wire`;
          `cr0 : wire`;
          `t + j + SUC kss`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `signal ld (t + j + SUC kss) <=> F` SUBST1_TAC THENL
    [UNDISCH_TAC
       `(g : cycle -> cycle # cycle) (SUC us) = (j, SUC (SUC kss))` THEN
     ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [SUC_LT];
     ALL_TAC] THEN
    REWRITE_TAC [ADD_SUC] THEN
    MP_TAC
      (SPECL
         [`cp0 : wire`;
          `cq0 : wire`;
          `SUC (t + j + kss)`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    AP_TERM_TAC THEN
    MP_TAC
      (SPECL [`cr : bus`; `cp : bus`; `0`;
              `cr0 : wire`; `cp0 : wire`] bdelay_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
        [`cr0 : wire`; `cp0 : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
    ASM_REWRITE_TAC [GSYM ADD1];
    ALL_TAC] THEN
   UNDISCH_THEN
     `SUC is < r + 1`
     (STRIP_ASSUME_TAC o REWRITE_RULE [GSYM ADD1; LT_SUC]) THEN
   SUBGOAL_THEN `?spi'. wire sp' (SUC is) spi'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cpis'. wire cp' is cpis'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`cq' : bus`;
         `1`;
         `r : num`;
         `cq1' : bus`;
         `is : num`;
         `cqi' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp' : bus`;
         `1`;
         `r : num`;
         `sp1' : bus`;
         `is : num`;
         `spi' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`cp' : bus`;
         `0`;
         `r : num`;
         `cp1' : bus`;
         `is : num`;
         `cpis' : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp1' : bus`; `cp1' : bus`; `sq1' : bus`; `cq1' : bus`]
        badder2_def) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp1' : bus`;
         `cp1' : bus`;
         `cq1' : bus`;
         `is : num`;
         `spi' : wire`;
         `cpis' : wire`;
         `cqi' : wire`]
        band2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`spi' : wire`;
         `cpis' : wire`;
         `cqi' : wire`;
         `u : cycle`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM
     (MP_TAC o SPECL [`u : cycle`; `j : cycle`; `ks : cycle`]) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   SUBGOAL_THEN `?sri'. wire sr' (SUC is) sri'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL [`sr' : bus`; `sp' : bus`; `SUC is`;
             `sri' : wire`; `spi' : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL [`sri' : wire`; `spi' : wire`; `us : cycle`] delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN `?cris'. wire cr' is cris'` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL [`cr' : bus`; `cp' : bus`; `is : num`;
             `cris' : wire`; `cpis' : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL [`cris' : wire`; `cpis' : wire`; `us : cycle`] delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
       [`sr' : bus`;
        `1`;
        `r : num`;
        `sr1' : bus`;
        `is : num`;
        `sri' : wire`]
       bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `?sri. wire sr is sri` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`\sri sri'.
            sri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. if k = 0 then signal sri (t + j)
                          else signal sri (t + j + (k - 1)))`;
         `sr : bus`;
         `sr1' : bus`;
         `is : num`;
         `sri : wire`;
         `sri' : wire`]
        blift2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF] THEN
   SUBGOAL_THEN `?cris. wire cr is cris` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`\cri cri'.
            cri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
         `cr : bus`;
         `cr' : bus`;
         `is : num`;
         `cris : wire`;
         `cris' : wire`]
        blift2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF] THEN
   SUBGOAL_THEN `?cri. wire cr (SUC is) cri` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`\cri cri'.
            cri' = (gw : (cycle -> cycle -> bool) -> wire)
                   (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
         `cr : bus`;
         `cr' : bus`;
         `SUC is`;
         `cri : wire`;
         `cri' : wire`]
        blift2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [UNCURRY_DEF; NOT_SUC; SUC_SUB1] THEN
   MP_TAC
     (SPECL
        [`cr : bus`;
         `1`;
         `r : num`;
         `cr1 : bus`;
         `is : num`;
         `cri : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `?cqi. wire cq (SUC is) cqi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [GSYM ADD1; LT_SUC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`cq : bus`;
         `1`;
         `r : num`;
         `cq1 : bus`;
         `is : num`;
         `cqi : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [] THEN
   ASM_REWRITE_TAC [ONE; SUC_ADD; ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `bground r`;
         `cq1 : bus`;
         `cr1 : bus`;
         `is : num`;
         `ground`;
         `cqi : wire`;
         `cri : wire`]
        bcase1_wire) THEN
   ASM_REWRITE_TAC [bground_wire] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `ground`;
         `cqi : wire`;
         `cri : wire`;
         `t + j + ks : cycle`]
        case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_CASES_TAC `ks = 0` THENL
   [UNDISCH_TAC `(g : cycle -> cycle # cycle) us = (j,ks)` THEN
    ASM_REWRITE_TAC [ADD_0] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [ground_signal];
    ALL_TAC] THEN
   MP_TAC (SPEC `ks : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `kss : cycle` SUBST_VAR_TAC) THEN
   REWRITE_TAC [GSYM ONE; SUC_SUB1] THEN
   SUBGOAL_THEN `signal ld (t + j + SUC kss) <=> F` SUBST1_TAC THENL
   [UNDISCH_TAC
      `(g : cycle -> cycle # cycle) (SUC us) = (j, SUC (SUC kss))` THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [SUC_LT];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_SUC] THEN
   SUBGOAL_THEN `?spi. wire sp is spi` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `?cpis. wire cp is cpis` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC wire_exists THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LT_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`cp : bus`;
         `0`;
         `r : num`;
         `cp1 : bus`;
         `is : num`;
         `cpis : wire`]
        bsub_wire) THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp : bus`; `cp1 : bus`; `sq : bus`; `cq1 : bus`]
        badder2_def) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sp : bus`;
         `cp1 : bus`;
         `cq1 : bus`;
         `is : num`;
         `spi : wire`;
         `cpis : wire`;
         `cqi : wire`]
        band2_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`spi : wire`;
         `cpis : wire`;
         `cqi : wire`;
         `SUC (t + j + kss) : cycle`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`sr : bus`; `sp : bus`; `is : num`;
             `sri : wire`; `spi : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`sri : wire`; `spi : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL [`cr : bus`; `cp : bus`; `is : num`;
             `cris : wire`; `cpis : wire`] bdelay_wire) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`cris : wire`; `cpis : wire`; `t + j + kss : cycle`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD1] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [case1_def] THEN
  X_GEN_TAC `u : cycle` THEN
  MP_TAC (ISPEC `(g : cycle -> cycle # cycle) u` PAIR_SURJECTIVE) THEN
  DISCH_THEN
   (X_CHOOSE_THEN `j : cycle`
     (X_CHOOSE_THEN `k : cycle` STRIP_ASSUME_TAC)) THEN
  FIND_ASSUM
    (SUBST1_TAC o SYM)
    `(gw : (num -> num -> bool) -> wire)
     (\j k. 1 < k /\ signal dn (t + j + (k - 1))) = dn'` THEN
  FIND_ASSUM
    (SUBST1_TAC o SYM)
    `(gw : (num -> num -> bool) -> wire) (\j k. k = 0) = ld'` THEN
  ASM_REWRITE_TAC [UNCURRY_DEF; ground_signal] THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  MP_TAC (SPEC `k : num` num_CASES) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `ks : cycle` SUBST_VAR_TAC) THEN
  REWRITE_TAC [SUC_SUB1] THEN
  REWRITE_TAC [ONE; LT_SUC; LT_NZ] THEN
  MP_TAC
   (SPECL [`dp' : wire`; `cp2' : wire`; `dq' : wire`; `u : cycle`]
     or2_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL [`u : cycle`; `j : cycle`; `ks : cycle`]) THEN
  ANTS_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`dn' : wire`; `dp' : wire`; `us : cycle`] delay_signal) THEN
  ASM_REWRITE_TAC [ADD1] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL [`cr' : bus`; `cp' : bus`; `r : num`;
            `cr2' : wire`; `cp2' : wire`] bdelay_wire) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`cr2' : wire`; `cp2' : wire`; `us : cycle`] delay_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIND_ASSUM
    (SUBST1_TAC o SYM)
    `(gw : (num -> num -> bool) -> wire)
     (\j k. 1 < k /\ signal dn (t + j + (k - 1))) = dn'` THEN
  ASM_REWRITE_TAC [UNCURRY_DEF] THEN
  SUBGOAL_THEN `?cr2. wire cr r cr2` STRIP_ASSUME_TAC THENL
  [MATCH_MP_TAC wire_exists THEN
   ASM_REWRITE_TAC [GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`\cri cri'.
           cri' = (gw : (cycle -> cycle -> bool) -> wire)
                  (\j k. ~(k = 0) /\ signal cri (t + (j + (k - 1))))`;
        `cr : bus`;
        `cr' : bus`;
        `r : num`;
        `cr2 : wire`;
        `cr2' : wire`]
       blift2_wire) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC [UNCURRY_DEF] THEN
  ASM_CASES_TAC `ks = 0` THENL
  [ASM_REWRITE_TAC [LT_ZERO];
   ALL_TAC] THEN
  MP_TAC (SPEC `ks : num` num_CASES) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `kss : cycle` SUBST_VAR_TAC) THEN
  REWRITE_TAC [SUC_SUB1] THEN
  REWRITE_TAC [ONE; LT_SUC; LT_NZ] THEN
  MP_TAC
   (SPECL [`dr : wire`; `dn : wire`; `t + j + SUC kss`]
     connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
   (SPECL [`ld : wire`; `ground`; `dq : wire`; `dr : wire`; `t + j + SUC kss`]
     case1_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `signal ld (t + j + SUC kss) <=> F` SUBST1_TAC THENL
  [UNDISCH_TAC
     `(g : cycle -> cycle # cycle) (SUC us) = (j, SUC (SUC kss))` THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [SUC_LT];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_SUC] THEN
  MP_TAC
   (SPECL [`dp : wire`; `cp2 : wire`; `dq : wire`; `SUC (t + j + kss)`]
     or2_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`dr : wire`; `dp : wire`; `t + j + kss : cycle`]
       delay_signal) THEN
  ASM_REWRITE_TAC [ADD1] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL [`cr : bus`; `cp : bus`; `r : num`;
            `cr2 : wire`; `cp2 : wire`] bdelay_wire) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`cr2 : wire`; `cp2 : wire`; `t + j + kss : cycle`]
       delay_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC
   (SPECL [`dr : wire`; `dn : wire`; `t + j + kss : cycle`]
     connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REVERSE_TAC (ASM_CASES_TAC `kss = 0`) THENL
  [ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  ASM_REWRITE_TAC [ADD_0] THEN
  MP_TAC
   (SPECL [`ld : wire`; `ground`; `dq : wire`; `dr : wire`; `t + j : cycle`]
     case1_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `signal ld (t + j) <=> T` SUBST1_TAC THENL
  [UNDISCH_TAC `(g : cycle -> cycle # cycle) us = (j, SUC 0)` THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [ground_signal]);;

export_thm counter_signal;;

let counter_signal_load = prove
 (`!ld nb dn t.
     signal ld t /\
     counter ld nb dn ==>
     ~signal dn t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [counter_def] THEN
  STRIP_TAC THEN
  MP_TAC
   (SPECL [`dr : wire`; `dn : wire`; `t : cycle`]
     connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
   (SPECL [`ld : wire`; `ground`; `dq : wire`; `dr : wire`; `t : cycle`]
     case1_signal) THEN
  ASM_REWRITE_TAC [ground_signal]);;

export_thm counter_signal_load;;

let counter_pulse_signal_load = prove
 (`!ld nb dn t.
     signal ld t /\
     counter_pulse ld nb dn ==>
     ~signal dn t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [counter_pulse_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC
   (SPECL [`ds : wire`; `dn : wire`; `t : cycle`]
     pulse_signal_false) THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC
   (SPECL [`ld : wire`; `nb : bus`; `ds : wire`; `t : cycle`]
     counter_signal_load) THEN
  ASM_REWRITE_TAC []);;

export_thm counter_pulse_signal_load;;

let counter_pulse_signal = prove
 (`!n ld nb dn t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal nb t) + n + 2 = 2 EXP (width nb) + width nb /\
     counter_pulse ld nb dn ==>
     (signal dn (t + k) <=> k = n + 1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `k = 0` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [ADD_0; GSYM ADD1; NOT_SUC] THEN
   MATCH_MP_TAC
     (SPECL
        [`ld : wire`;
         `nb : bus`;
         `dn : wire`;
         `t : cycle`]
        counter_pulse_signal_load) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
   ASM_REWRITE_TAC [ADD_0; LE_REFL];
   ALL_TAC] THEN
  MP_TAC (SPEC `k : cycle` num_CASES) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN (X_CHOOSE_THEN `ks : cycle` SUBST_VAR_TAC) THEN
  REWRITE_TAC [ADD1; EQ_ADD_RCANCEL] THEN
  UNDISCH_THEN
    `counter_pulse ld nb dn`
    (STRIP_ASSUME_TAC o REWRITE_RULE [counter_pulse_def]) THEN
  MP_TAC
    (SPECL
       [`ds : wire`;
        `dn : wire`;
        `t + ks : cycle`]
       pulse_signal) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `ld : wire`;
        `nb : bus`;
        `ds : wire`;
        `t : cycle`;
        `ks : cycle`]
       counter_signal) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `ks : cycle` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `ld : wire`;
        `nb : bus`;
        `ds : wire`;
        `t : cycle`;
        `SUC ks : cycle`]
       counter_signal) THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [ADD1] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [NOT_LT; GSYM ADD1; LT_SUC_LE; LE_ANTISYM]);;

export_thm counter_pulse_signal;;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-counter-tools.ml";;

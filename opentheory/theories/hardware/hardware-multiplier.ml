(* ========================================================================= *)
(* HARDWARE MULTIPLIER DEVICES                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-def";;

(* -------------------------------------- *)
(*       r+2 r+1  r  r-1  ...  2   1   0  *)
(* -------------------------------------- *)
(*  xs =  -   -   p   p   ...  p   p   bp *)
(*  xc =  -   o   o   o   ...  o   o   -  *)
(*  sq =  -   -   p   p   ...  p   p   bp *)
(*  cq =  -   o   p   p   ...  p   p   -  *)
(* -------------------------------------- *)
(*  ps =  -   -   o   o   ...  o   o   -  *)
(*  pc =  -   o   o   o   ...  o   o   -  *)
(* -------------------------------------- *)
(*  b  =  -   -   -   -   ...  -   -   X  *)
(*  s  =  -   X   X   X   ...  X   X   -  *)
(*  c  =  X   X   X   X   ...  X   -   -  *)
(* -------------------------------------- *)

let sum_carry_mult_def = new_definition
  `!ld w xs xc b s c.
     sum_carry_mult ld w xs xc b s c <=>
     ?r sp cp sq cq xos xoc ps pc
      s0 s1 c0 c1 sq0 sq1 cq0 cq1 xos0 xos1 xoc0 xoc1 pc0 pc1 pc2 pc3.
       width xs = r + 1 /\
       width xc = r + 1 /\
       width s = r + 1 /\
       width c = r + 1 /\
       width sp = r + 1 /\
       width cp = r + 1 /\
       width sq = r + 1 /\
       width cq = r + 1 /\
       width xos = r + 1 /\
       width xoc = r + 1 /\
       width ps = r /\
       width pc = r + 1
       /\
       bsub s 0 r s0 /\
       wire s r s1 /\
       bsub c 0 r c0 /\
       wire c r c1 /\
       wire sq 0 sq0 /\
       bsub sq 1 r sq1 /\
       bsub cq 0 r cq0 /\
       wire cq r cq1 /\
       wire xos 0 xos0 /\
       bsub xos 1 r xos1 /\
       bsub xoc 0 r xoc0 /\
       wire xoc r xoc1 /\
       wire pc 0 pc0 /\
       bsub pc 0 r pc1 /\
       bsub pc 1 r pc2 /\
       wire pc r pc3
       /\
       bcase1 ld (bground (r + 1)) sp sq /\
       bcase1 ld (bground (r + 1)) cp cq /\
       bcase1 w xs (bground (r + 1)) xos /\
       bcase1 w xc (bground (r + 1)) xoc /\
       adder2 sq0 xos0 b pc0 /\
       badder3 sq1 cq0 xos1 ps pc2 /\
       badder3 xoc0 ps pc1 s0 c0 /\
       adder3 xoc1 cq1 pc3 s1 c1 /\
       bdelay s sp /\
       bdelay c cp`;;

export_thm sum_carry_mult_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-thm";;

let sum_carry_mult_bits_to_num = prove
 (`!n x ld w xs xc b s c t k.
     (!i.
        i <= k ==>
        (signal ld (t + i) <=> i = 0) /\
        (signal w (t + i) <=> bit_nth n i) /\
        (bit_nth n i ==>
         bits_to_num (bsignal xs (t + i)) +
         2 * bits_to_num (bsignal xc (t + i)) = x)) /\
     sum_carry_mult ld w xs xc b s c ==>
     bit_cons (signal b (t + k))
       (bits_to_num (bsignal s (t + k)) +
        2 * bits_to_num (bsignal c (t + k))) =
     bit_shr (x * bit_bound n (k + 1)) k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sum_carry_mult_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!u.
       bit_cons (signal b u)
         (bits_to_num (bsignal s u) + 2 * bits_to_num (bsignal c u)) =
       (bits_to_num (bsignal xos u) + 2 * bits_to_num (bsignal xoc u)) +
       (bits_to_num (bsignal sq u) + 2 * bits_to_num (bsignal cq u))`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_THEN
     `!i.
        i <= k ==>
        (signal ld (t + i) <=> i = 0) /\
        (signal w (t + i) <=> bit_nth n i) /\
        (bit_nth n i ==>
         bits_to_num (bsignal xs (t + i)) +
         2 * bits_to_num (bsignal xc (t + i)) = x)`
     (K ALL_TAC) THEN
   X_GEN_TAC `t : cycle` THEN
   SUBGOAL_THEN `bappend s0 (bwire s1) = s` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   SUBGOAL_THEN `bappend c0 (bwire c1) = c` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bits_to_num] THEN
   SUBGOAL_THEN `width s0 = r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `s : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width c0 = r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `c : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [bwire_bits_to_num] THEN
   SUBGOAL_THEN
     `(bits_to_num (bsignal s0 t) + bit_shl (bit_to_num (signal s1 t)) r) +
      2 * (bits_to_num (bsignal c0 t) + bit_shl (bit_to_num (signal c1 t)) r) =
      (bits_to_num (bsignal s0 t) + 2 * bits_to_num (bsignal c0 t)) +
      bit_shl (bit_to_num (signal s1 t) + 2 * bit_to_num (signal c1 t)) r`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC
      [add_bit_shl; GSYM bit_cons_false; GSYM bit_shl_suc;
       GSYM bit_shl_suc'; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`xoc0 : bus`;
         `ps : bus`;
         `pc1 : bus`;
         `s0 : bus`;
         `c0 : bus`;
         `t : cycle`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`xoc1 : wire`;
         `cq1 : wire`;
         `pc3 : wire`;
         `s1 : wire`;
         `c1 : wire`;
         `t : cycle`]
        adder3_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `(bits_to_num (bsignal xoc0 t) +
       bits_to_num (bsignal ps t) +
       bits_to_num (bsignal pc1 t)) +
      bit_shl
        (bit_to_num (signal xoc1 t) +
         bit_to_num (signal cq1 t) +
         bit_to_num (signal pc3 t))
        r =
      (bits_to_num (bsignal xoc0 t) +
       bit_shl (bit_to_num (signal xoc1 t)) r) +
      bits_to_num (bsignal ps t) +
      (bits_to_num (bsignal pc1 t) +
       bit_shl (bit_to_num (signal pc3 t)) r) +
      bit_shl (bit_to_num (signal cq1 t)) r`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; add_bit_shl] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal xoc0 t) +
      bit_shl (bit_to_num (signal xoc1 t)) r =
      bits_to_num (bsignal xoc t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend xoc0 (bwire xoc1) = xoc` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num; bwire_bits_to_num] THEN
    SUBGOAL_THEN `width xoc0 = r` SUBST1_TAC THENL
    [MATCH_MP_TAC bsub_width THEN
     EXISTS_TAC `xoc : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal pc1 t) +
      bit_shl (bit_to_num (signal pc3 t)) r =
      bits_to_num (bsignal pc t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend pc1 (bwire pc3) = pc` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num; bwire_bits_to_num] THEN
    SUBGOAL_THEN `width pc1 = r` SUBST1_TAC THENL
    [MATCH_MP_TAC bsub_width THEN
     EXISTS_TAC `pc : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal pc t) =
      bit_to_num (signal pc0 t) + 2 * bits_to_num (bsignal pc2 t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend (bwire pc0) pc2 = pc` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal xoc t) +
      bits_to_num (bsignal ps t) +
      (bit_to_num (signal pc0 t) + 2 * bits_to_num (bsignal pc2 t)) +
      bit_shl (bit_to_num (signal cq1 t)) r =
      bit_to_num (signal pc0 t) +
      bits_to_num (bsignal xoc t) +
      (bits_to_num (bsignal ps t) + 2 * bits_to_num (bsignal pc2 t)) +
      bit_shl (bit_to_num (signal cq1 t)) r`
     SUBST1_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sq1 : bus`;
         `cq0 : bus`;
         `xos1 : bus`;
         `ps : bus`;
         `pc2 : bus`;
         `t : cycle`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `bit_to_num (signal pc0 t) +
      bits_to_num (bsignal xoc t) +
      (bits_to_num (bsignal sq1 t) +
       bits_to_num (bsignal cq0 t) +
       bits_to_num (bsignal xos1 t)) +
      bit_shl (bit_to_num (signal cq1 t)) r =
      bit_to_num (signal pc0 t) +
      bits_to_num (bsignal xoc t) +
      (bits_to_num (bsignal sq1 t) +
       bits_to_num (bsignal xos1 t)) +
      (bits_to_num (bsignal cq0 t) + bit_shl (bit_to_num (signal cq1 t)) r)`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bits_to_num (bsignal cq0 t) +
      bit_shl (bit_to_num (signal cq1 t)) r =
      bits_to_num (bsignal cq t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend cq0 (bwire cq1) = cq` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num; bwire_bits_to_num] THEN
    SUBGOAL_THEN `width cq0 = r` SUBST1_TAC THENL
    [MATCH_MP_TAC bsub_width THEN
     EXISTS_TAC `cq : bus` THEN
     EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [bit_cons_def; LEFT_ADD_DISTRIB; ADD_ASSOC] THEN
   MP_TAC
     (SPECL
        [`sq0 : wire`;
         `xos0 : wire`;
         `b : wire`;
         `pc0 : wire`;
         `t : cycle`]
        adder2_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `((((bit_to_num (signal sq0 t) + bit_to_num (signal xos0 t)) +
         2 * bits_to_num (bsignal xoc t)) +
        2 * bits_to_num (bsignal sq1 t)) +
       2 * bits_to_num (bsignal xos1 t)) +
      2 * bits_to_num (bsignal cq t) =
      ((bit_to_num (signal xos0 t) + 2 * bits_to_num (bsignal xos1 t)) +
       2 * bits_to_num (bsignal xoc t)) +
      ((bit_to_num (signal sq0 t) + 2 * bits_to_num (bsignal sq1 t)) +
       2 * bits_to_num (bsignal cq t))`
     SUBST1_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bit_to_num (signal xos0 t) + 2 * bits_to_num (bsignal xos1 t) =
      bits_to_num (bsignal xos t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend (bwire xos0) xos1 = xos` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bit_to_num (signal sq0 t) + 2 * bits_to_num (bsignal sq1 t) =
      bits_to_num (bsignal sq t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend (bwire sq0) sq1 = sq` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     ONCE_REWRITE_TAC [ADD_SYM] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  UNDISCH_TAC
    `!i.
       i <= k ==>
       (signal ld (t + i) <=> i = 0) /\
       (signal w (t + i) <=> bit_nth n i) /\
       (bit_nth n i ==>
        bits_to_num (bsignal xs (t + i)) +
        2 * bits_to_num (bsignal xc (t + i)) = x)` THEN
  SPEC_TAC (`k : cycle`, `k : cycle`) THEN
  INDUCT_TAC THENL
  [DISCH_THEN (MP_TAC o SPEC `0`) THEN
   REWRITE_TAC
     [LE_REFL; ADD_0; ZERO_ADD; bit_shr_zero; bit_bound_one;
      bit_nth_zero] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (SUBST1_TAC o SPEC `t : cycle`) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `bground (r + 1)`;
         `sp : bus`;
         `sq : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `bground (r + 1)`;
         `cp : bus`;
         `cq : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [bground_bits_to_num; MULT_0; ADD_0] THEN
   MP_TAC
     (SPECL
        [`w : wire`;
         `xs : bus`;
         `bground (r + 1)`;
         `xos : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`w : wire`;
         `xc : bus`;
         `bground (r + 1)`;
         `xoc : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN
   ASM_REWRITE_TAC
     [bit_to_num_true; MULT_1; bit_to_num_false; MULT_0;
      bground_bits_to_num; ADD_0];
   ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
  [GEN_TAC THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `k : cycle` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `SUC k`) THEN
  REWRITE_TAC [LE_REFL; NOT_SUC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (SUBST1_TAC o SPEC `t + SUC k`) THEN
  MP_TAC
    (SPECL
       [`ld : wire`;
        `bground (r + 1)`;
        `sp : bus`;
        `sq : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`ld : wire`;
        `bground (r + 1)`;
        `cp : bus`;
        `cq : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`;
        `xs : bus`;
        `bground (r + 1)`;
        `xos : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`w : wire`;
        `xc : bus`;
        `bground (r + 1)`;
        `xoc : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`s : bus`;
        `sp : bus`;
        `t + k : cycle`]
       (REWRITE_RULE [GSYM ADD1] bdelay_bsignal)) THEN
  ASM_REWRITE_TAC [ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`c : bus`;
        `cp : bus`;
        `t + k : cycle`]
       (REWRITE_RULE [GSYM ADD1] bdelay_bsignal)) THEN
  ASM_REWRITE_TAC [ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `(bits_to_num
       (if bit_nth n (SUC k)
        then bsignal xs (SUC (t + k))
        else bsignal (bground (r + 1)) (SUC (t + k))) +
      2 * bits_to_num
            (if bit_nth n (SUC k)
             then bsignal xc (SUC (t + k))
             else bsignal (bground (r + 1)) (SUC (t + k)))) =
     (if bit_nth n (SUC k) then x else 0)`
    SUBST1_TAC THENL
  [POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN
   ASM_REWRITE_TAC [GSYM ADD_SUC; bground_bits_to_num; MULT_0; ADD_0];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  (CONV_TAC o LAND_CONV o REWR_CONV o GSYM)
    (SPEC `signal b (t + k)` bit_tl_cons) THEN
  SUBGOAL_THEN
    `bit_cons (signal b (t + k))
       ((if bit_nth n (SUC k) then x else 0) +
        bits_to_num (bsignal s (t + k)) +
        2 * bits_to_num (bsignal c (t + k))) =
     bit_cons F (if bit_nth n (SUC k) then x else 0) +
     bit_cons (signal b (t + k))
       (bits_to_num (bsignal s (t + k)) +
        2 * bits_to_num (bsignal c (t + k)))`
    SUBST1_TAC THENL
  [REWRITE_TAC [bit_cons_false] THEN
   REWRITE_TAC [bit_cons_def; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM_LIST (K ALL_TAC) THEN
  REWRITE_TAC [GSYM ADD1; bit_shr_suc] THEN
  AP_TERM_TAC THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [bit_bound_suc'])) THEN
  REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
  REVERSE_TAC COND_CASES_TAC THENL
  [REWRITE_TAC
     [bit_cons_def; bit_to_num_false; zero_bit_shl; ZERO_ADD; ADD_0; MULT_0];
   ALL_TAC] THEN
  REWRITE_TAC [bit_to_num_true; GSYM mult_bit_shl; MULT_1] THEN
  REWRITE_TAC [bit_shl_suc'; add_bit_shr] THEN
  MATCH_ACCEPT_TAC ADD_SYM);;

export_thm sum_carry_mult_bits_to_num;;

(***
let sum_carry_mult_bits_to_num = prove
 (`!x y ld xs xc ys yc zs zc t k.
     
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t) = n /\
     sum_carry_bit ld s c w ==>
     signal w (t + k) = bit_nth n k`,

 (`!n x ld w xs xc b s c t k.
     (!i.
        i <= k ==>
        (signal ld (t + i) <=> i = 0) /\
        (signal w (t + i) = bit_nth n i) /\
        bits_to_num (bsignal xs (t + i)) +
        2 * bits_to_num (bsignal xc (t + i)) = x) /\
     sum_carry_mult ld w xs xc b s c ==>
     bit_cons (signal b (t + k))
       (bits_to_num (bsignal s (t + k)) +
        2 * bits_to_num (bsignal c (t + k))) =
     bit_shr (x * bit_bound n (k + 1)) k`,
  REPEAT GEN_TAC THEN
***)

logfile_end ();;

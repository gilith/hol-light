(* ========================================================================= *)
(* HARDWARE MULTIPLIER DEVICES                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-multiplier-def";;

(* --------------------------------------- *)
(*        r+2 r+1  r  r-1  ...  2   1   0  *)
(* --------------------------------------- *)
(*  yos =  -   -   p   p   ...  p   p   bp *)
(*  yoc =  -   o   o   o   ...  o   o   -  *)
(*  sq  =  -   -   p   p   ...  p   p   bp *)
(*  cq  =  -   o   p   p   ...  p   p   -  *)
(* --------------------------------------- *)
(*  ps  =  -   -   o   o   ...  o   o   -  *)
(*  pc  =  -   o   o   o   ...  o   o   -  *)
(* --------------------------------------- *)
(*  sr  =  -   X   X   X   ...  X   X   -  *)
(*  cr  =  X   X   X   X   ...  X   -   -  *)
(* --------------------------------------- *)
(*  zb  =  -   -   -   -   ...  -   -   X  *)
(*  zs  =  -   X   X   X   ...  X   X   -  *)
(*  zc  =  X   X   X   X   ...  X   -   -  *)
(* --------------------------------------- *)

let bmult_def = new_definition
  `!ld xb ys yc zb zs zc.
     bmult ld xb ys yc zb zs zc <=>
     ?r sp sq sr cp cq cr yos yoc ps pc
      sq0 sq1 sr0 sr1 cq0 cq1 cr0 cr1 yos0 yos1 yoc0 yoc1 pc0 pc1 pc2 pc3.
       width ys = r + 1 /\
       width yc = r + 1 /\
       width zs = r + 1 /\
       width zc = r + 1 /\
       width sp = r + 1 /\
       width sq = r + 1 /\
       width sr = r + 1 /\
       width cp = r + 1 /\
       width cq = r + 1 /\
       width cr = r + 1 /\
       width yos = r + 1 /\
       width yoc = r + 1 /\
       width ps = r /\
       width pc = r + 1
       /\
       wire sq 0 sq0 /\
       bsub sq 1 r sq1 /\
       bsub sr 0 r sr0 /\
       wire sr r sr1 /\
       bsub cq 0 r cq0 /\
       wire cq r cq1 /\
       bsub cr 0 r cr0 /\
       wire cr r cr1 /\
       wire yos 0 yos0 /\
       bsub yos 1 r yos1 /\
       bsub yoc 0 r yoc0 /\
       wire yoc r yoc1 /\
       wire pc 0 pc0 /\
       bsub pc 0 r pc1 /\
       bsub pc 1 r pc2 /\
       wire pc r pc3
       /\
       bcase1 ld (bground (r + 1)) sp sq /\
       bcase1 ld (bground (r + 1)) cp cq /\
       bcase1 xb ys (bground (r + 1)) yos /\
       bcase1 xb yc (bground (r + 1)) yoc /\
       adder2 sq0 yos0 zb pc0 /\
       badder3 sq1 cq0 yos1 ps pc2 /\
       badder3 yoc0 ps pc1 sr0 cr0 /\
       adder3 yoc1 cq1 pc3 sr1 cr1 /\
       bconnect sr zs /\
       bconnect cr zc
       /\
       bdelay sr sp /\
       bdelay cr cp`;;

export_thm bmult_def;;

let scmult_def = new_definition
  `!ld xs xc d ys yc zb zs zc.
     scmult ld xs xc d ys yc zb zs zc <=>
     ?xb ldd xbd.
       scshiftr ld xs xc xb /\
       pipe ld d ldd /\
       pipe xb d xbd /\
       bmult ldd xbd ys yc zb zs zc`;;

export_thm scmult_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

export_theory "hardware-multiplier-thm";;

let bmult_width = prove
 (`!ld xb ys yc zb zs zc.
     bmult ld xb ys yc zb zs zc ==>
     ?r.
       width ys = r + 1 /\
       width yc = r + 1 /\
       width zs = r + 1 /\
       width zc = r + 1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmult_def] THEN
  STRIP_TAC THEN
  EXISTS_TAC `r : num` THEN
  ASM_REWRITE_TAC []);;

export_thm bmult_width;;

let bmult_bits_to_num = prove
 (`!x y ld xb ys yc zb zs zc t k.
     (!i.
        i <= k ==>
        (signal ld (t + i) <=> i = 0) /\
        (signal xb (t + i) <=> bit_nth x i) /\
        (bit_nth x i ==>
         bits_to_num (bsignal ys (t + i)) +
         2 * bits_to_num (bsignal yc (t + i)) = y)) /\
     bmult ld xb ys yc zb zs zc ==>
     bit_cons (signal zb (t + k))
       (bits_to_num (bsignal zs (t + k)) +
        2 * bits_to_num (bsignal zc (t + k))) =
     bit_shr (bit_bound x (k + 1) * y) k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [bmult_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`sr : bus`;
        `zs : bus`;
        `t + k : cycle`]
       bconnect_bsignal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`cr : bus`;
        `zc : bus`;
        `t + k : cycle`]
       bconnect_bsignal) THEN
  FIRST_X_ASSUM (fun th -> ANTS_TAC THENL [ACCEPT_TAC th; ALL_TAC]) THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `!u.
       bit_cons (signal zb u)
         (bits_to_num (bsignal sr u) + 2 * bits_to_num (bsignal cr u)) =
       (bits_to_num (bsignal yos u) + 2 * bits_to_num (bsignal yoc u)) +
       (bits_to_num (bsignal sq u) + 2 * bits_to_num (bsignal cq u))`
    STRIP_ASSUME_TAC THENL
  [UNDISCH_THEN
     `!i.
        i <= k ==>
        (signal ld (t + i) <=> i = 0) /\
        (signal xb (t + i) <=> bit_nth x i) /\
        (bit_nth x i ==>
         bits_to_num (bsignal ys (t + i)) +
         2 * bits_to_num (bsignal yc (t + i)) = y)`
     (K ALL_TAC) THEN
   X_GEN_TAC `t : cycle` THEN
   SUBGOAL_THEN `bappend sr0 (bwire sr1) = sr` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   SUBGOAL_THEN `bappend cr0 (bwire cr1) = cr` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bits_to_num] THEN
   SUBGOAL_THEN `width sr0 = r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sr : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width cr0 = r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `cr : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [bwire_bits_to_num] THEN
   SUBGOAL_THEN
     `(bits_to_num (bsignal sr0 t) + bit_shl (bit_to_num (signal sr1 t)) r) +
      2 * (bits_to_num (bsignal cr0 t) + bit_shl (bit_to_num (signal cr1 t)) r) =
      (bits_to_num (bsignal sr0 t) + 2 * bits_to_num (bsignal cr0 t)) +
      bit_shl (bit_to_num (signal sr1 t) + 2 * bit_to_num (signal cr1 t)) r`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; LEFT_ADD_DISTRIB] THEN
    REWRITE_TAC
      [add_bit_shl; GSYM bit_cons_false; GSYM bit_shl_suc;
       GSYM bit_shl_suc'; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`yoc0 : bus`;
         `ps : bus`;
         `pc1 : bus`;
         `sr0 : bus`;
         `cr0 : bus`;
         `t : cycle`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`yoc1 : wire`;
         `cq1 : wire`;
         `pc3 : wire`;
         `sr1 : wire`;
         `cr1 : wire`;
         `t : cycle`]
        adder3_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `(bits_to_num (bsignal yoc0 t) +
       bits_to_num (bsignal ps t) +
       bits_to_num (bsignal pc1 t)) +
      bit_shl
        (bit_to_num (signal yoc1 t) +
         bit_to_num (signal cq1 t) +
         bit_to_num (signal pc3 t))
        r =
      (bits_to_num (bsignal yoc0 t) +
       bit_shl (bit_to_num (signal yoc1 t)) r) +
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
     `bits_to_num (bsignal yoc0 t) +
      bit_shl (bit_to_num (signal yoc1 t)) r =
      bits_to_num (bsignal yoc t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend yoc0 (bwire yoc1) = yoc` (SUBST1_TAC o SYM) THENL
    [ASM_REWRITE_TAC [GSYM bsub_all] THEN
     MATCH_MP_TAC bsub_add THEN
     ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
     ALL_TAC] THEN
    REWRITE_TAC [bappend_bits_to_num; bwire_bits_to_num] THEN
    SUBGOAL_THEN `width yoc0 = r` SUBST1_TAC THENL
    [MATCH_MP_TAC bsub_width THEN
     EXISTS_TAC `yoc : bus` THEN
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
     `bits_to_num (bsignal yoc t) +
      bits_to_num (bsignal ps t) +
      (bit_to_num (signal pc0 t) + 2 * bits_to_num (bsignal pc2 t)) +
      bit_shl (bit_to_num (signal cq1 t)) r =
      bit_to_num (signal pc0 t) +
      bits_to_num (bsignal yoc t) +
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
         `yos1 : bus`;
         `ps : bus`;
         `pc2 : bus`;
         `t : cycle`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `bit_to_num (signal pc0 t) +
      bits_to_num (bsignal yoc t) +
      (bits_to_num (bsignal sq1 t) +
       bits_to_num (bsignal cq0 t) +
       bits_to_num (bsignal yos1 t)) +
      bit_shl (bit_to_num (signal cq1 t)) r =
      bit_to_num (signal pc0 t) +
      bits_to_num (bsignal yoc t) +
      (bits_to_num (bsignal sq1 t) +
       bits_to_num (bsignal yos1 t)) +
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
         `yos0 : wire`;
         `zb : wire`;
         `pc0 : wire`;
         `t : cycle`]
        adder2_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `((((bit_to_num (signal sq0 t) + bit_to_num (signal yos0 t)) +
         2 * bits_to_num (bsignal yoc t)) +
        2 * bits_to_num (bsignal sq1 t)) +
       2 * bits_to_num (bsignal yos1 t)) +
      2 * bits_to_num (bsignal cq t) =
      ((bit_to_num (signal yos0 t) + 2 * bits_to_num (bsignal yos1 t)) +
       2 * bits_to_num (bsignal yoc t)) +
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
     `bit_to_num (signal yos0 t) + 2 * bits_to_num (bsignal yos1 t) =
      bits_to_num (bsignal yos t)`
     SUBST1_TAC THENL
   [SUBGOAL_THEN `bappend (bwire yos0) yos1 = yos` (SUBST1_TAC o SYM) THENL
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
       (signal xb (t + i) <=> bit_nth x i) /\
       (bit_nth x i ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y)` THEN
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
        [`xb : wire`;
         `ys : bus`;
         `bground (r + 1)`;
         `yos : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`xb : wire`;
         `yc : bus`;
         `bground (r + 1)`;
         `yoc : bus`;
         `t : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN
   ASM_REWRITE_TAC
     [bit_to_num_true; ONE_MULT; bit_to_num_false; ZERO_MULT;
      bground_bits_to_num; ADD_0; MULT_0];
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
       [`xb : wire`;
        `ys : bus`;
        `bground (r + 1)`;
        `yos : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`xb : wire`;
        `yc : bus`;
        `bground (r + 1)`;
        `yoc : bus`;
        `t + SUC k : cycle`]
       bcase1_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`sr : bus`;
        `sp : bus`;
        `t + k : cycle`]
       (REWRITE_RULE [GSYM ADD1] bdelay_bsignal)) THEN
  ASM_REWRITE_TAC [ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`cr : bus`;
        `cp : bus`;
        `t + k : cycle`]
       (REWRITE_RULE [GSYM ADD1] bdelay_bsignal)) THEN
  ASM_REWRITE_TAC [ADD_SUC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
    `(bits_to_num
       (if bit_nth x (SUC k)
        then bsignal ys (SUC (t + k))
        else bsignal (bground (r + 1)) (SUC (t + k))) +
      2 * bits_to_num
            (if bit_nth x (SUC k)
             then bsignal yc (SUC (t + k))
             else bsignal (bground (r + 1)) (SUC (t + k)))) =
     (if bit_nth x (SUC k) then y else 0)`
    SUBST1_TAC THENL
  [POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THEN
   ASM_REWRITE_TAC [GSYM ADD_SUC; bground_bits_to_num; MULT_0; ADD_0];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  (CONV_TAC o LAND_CONV o REWR_CONV o GSYM)
    (SPEC `signal zb (t + k)` bit_tl_cons) THEN
  SUBGOAL_THEN
    `bit_cons (signal zb (t + k))
       ((if bit_nth x (SUC k) then y else 0) +
        bits_to_num (bsignal sr (t + k)) +
        2 * bits_to_num (bsignal cr (t + k))) =
     bit_cons F (if bit_nth x (SUC k) then y else 0) +
     bit_cons (signal zb (t + k))
       (bits_to_num (bsignal sr (t + k)) +
        2 * bits_to_num (bsignal cr (t + k)))`
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
  (CONV_TAC o RAND_CONV o ONCE_REWRITE_CONV)
    [ONCE_REWRITE_RULE [ADD_SYM] bit_bound_suc'] THEN
  REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
  REVERSE_TAC COND_CASES_TAC THENL
  [REWRITE_TAC
     [bit_cons_zero; bit_to_num_false; zero_bit_shl;
      ZERO_ADD; ADD_0; ZERO_MULT];
   ALL_TAC] THEN
  REWRITE_TAC
    [bit_to_num_true; ONE_MULT;
     GSYM (ONCE_REWRITE_RULE [MULT_SYM] mult_bit_shl)] THEN
  REWRITE_TAC [bit_shl_suc'; ONCE_REWRITE_RULE [ADD_SYM] add_bit_shr]);;

export_thm bmult_bits_to_num;;

let scmult_bits_to_num = prove
 (`!x y ld xs xc d ys yc zb zs zc t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        i <= d + k /\ d <= i /\ i <= width xs + d + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     scmult ld xs xc d ys yc zb zs zc ==>
     bit_cons (signal zb (t + d + k))
       (bits_to_num (bsignal zs (t + d + k)) +
        2 * bits_to_num (bsignal zc (t + d + k))) =
     bit_shr (bit_bound x (k + 1) * y) k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [scmult_def] THEN
  STRIP_TAC THEN
  REWRITE_TAC [ADD_ASSOC] THEN
  MATCH_MP_TAC bmult_bits_to_num THEN
  EXISTS_TAC `ldd : wire` THEN
  EXISTS_TAC `xbd : wire` THEN
  EXISTS_TAC `ys : bus` THEN
  EXISTS_TAC `yc : bus` THEN
  ASM_REWRITE_TAC [] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [CONV_TAC
    (ONCE_DEPTH_CONV
      (REWR_CONV (GSYM ADD_ASSOC) THENC
       RAND_CONV (REWR_CONV ADD_SYM) THENC
       REWR_CONV ADD_ASSOC)) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `d : cycle`;
         `ldd : wire`;
         `t + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [CONV_TAC
    (ONCE_DEPTH_CONV
      (REWR_CONV (GSYM ADD_ASSOC) THENC
       RAND_CONV (REWR_CONV ADD_SYM) THENC
       REWR_CONV ADD_ASSOC)) THEN
   MP_TAC
     (SPECL
        [`xb : wire`;
         `d : cycle`;
         `xbd : wire`;
         `t + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC scshiftr_signal THEN
   EXISTS_TAC `ld : wire` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `j : cycle` THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `i : cycle` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  STRIP_TAC THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [LE_ADD; LE_ADD_LCANCEL] THEN
  CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
  REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
  CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
  REWRITE_TAC [GSYM LT_SUC_LE; ONE; ADD_SUC; ADD_0] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `bit_width x` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC bit_nth_width THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `MAX (bit_width (bits_to_num (bsignal xs t)))
         (bit_width (2 * bits_to_num (bsignal xc t))) + 1` THEN
  REWRITE_TAC [bit_width_add] THEN
  REWRITE_TAC [GSYM ADD1; LE_SUC; MAX_LE] THEN
  MP_TAC
    (SPECL
       [`ld : wire`;
        `xs : bus`;
        `xc : bus`;
        `xb : wire`]
     scshiftr_width) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (bsignal xs t)` THEN
   REWRITE_TAC [bit_width_bits_to_num] THEN
   ASM_REWRITE_TAC [length_bsignal; SUC_LE];
   REWRITE_TAC [GSYM bit_shl_one] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `bit_width (bits_to_num (bsignal xc t)) + 1` THEN
   REWRITE_TAC [bit_width_shl_le] THEN
   REWRITE_TAC [ADD1; LE_ADD_RCANCEL] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `LENGTH (bsignal xc t)` THEN
   REWRITE_TAC [bit_width_bits_to_num] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL]]);;

export_thm scmult_bits_to_num;;

(* ------------------------------------------------------------------------- *)
(* Proof tools.                                                              *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/hardware/hardware-multiplier-tools.ml";;

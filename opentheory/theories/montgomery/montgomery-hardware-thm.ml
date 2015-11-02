(* ========================================================================= *)
(* CORRECTNESS OF THE MONTGOMERY MULTIPLICATION CIRCUIT                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "montgomery-hardware-thm";;

(* ------------------------------------------------------------------------- *)
(* Correctness of the Montgomery multiplication circuit.                     *)
(* ------------------------------------------------------------------------- *)

let montgomery_mult_reduce_bit_width = prove
 (`!n r k x y ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc t.
     width xs = r /\
     ~(n = 0) /\
     bit_width n <= r /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     montgomery_mult_reduce ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc ==>
     bit_width x <= r + 2 /\
     bit_width y <= r + 2 /\
     bit_width (x * y) <= (r + 2) + (r + 2) /\
     bit_width (montgomery_reduce n (2 EXP (r + 2)) k (x * y)) <= r + 2`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `r : num` THEN
  X_GEN_TAC `k : num` THEN
  X_GEN_TAC `x : num` THEN
  X_GEN_TAC `y : num` THEN
  X_GEN_TAC `ld : wire` THEN
  X_GEN_TAC `xs : bus` THEN
  X_GEN_TAC `xc : bus` THEN
  X_GEN_TAC `d0 : cycle` THEN
  X_GEN_TAC `ys : bus` THEN
  X_GEN_TAC `yc : bus` THEN
  X_GEN_TAC `d1 : cycle` THEN
  X_GEN_TAC `ks : bus` THEN
  X_GEN_TAC `kc : bus` THEN
  X_GEN_TAC `d2 : cycle` THEN
  X_GEN_TAC `ns : bus` THEN
  X_GEN_TAC `nc : bus` THEN
  X_GEN_TAC `zs : bus` THEN
  X_GEN_TAC `zc : bus` THEN
  X_GEN_TAC `t : cycle` THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [montgomery_mult_reduce_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `rs : num` STRIP_ASSUME_TAC) THEN
  UNDISCH_THEN `width xs = r` MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `x < 2 EXP r + 2 EXP (r + 1)`
    ASSUME_TAC THENL
  [UNDISCH_THEN
     `bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x`
     (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC
     `2 EXP (LENGTH (bsignal xs t)) +
      2 * bits_to_num (bsignal xc t)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT_ADD_RCANCEL; bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [GSYM ADD1; EXP_SUC; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (LENGTH (bsignal xc t))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `y < 2 EXP r + 2 EXP (r + 1)`
    ASSUME_TAC THENL
  [UNDISCH_THEN
     `!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y`
     (MP_TAC o SPEC `d0 : cycle`) THEN
   ASM_REWRITE_TAC [LE_REFL; LE_ADD] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC
     `2 EXP (LENGTH (bsignal ys (t + d0))) +
      2 * bits_to_num (bsignal yc (t + d0))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT_ADD_RCANCEL; bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [GSYM ADD1; EXP_SUC; LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP (LENGTH (bsignal yc (t + d0)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bits_to_num_bound];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [length_bsignal; LE_REFL];
   ALL_TAC] THEN
  MATCH_MP_TAC (TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_width_upper_bound] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP r + 2 EXP (r + 1)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `2 * 2 EXP r + 2 EXP (r + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [MULT_2; GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD1; GSYM EXP_SUC; GSYM MULT_2; TWO; ADD_SUC; LE_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC (TAUT `!a b. a /\ (a ==> b) ==> a /\ b`) THEN
  CONJ_TAC THENL
  [REWRITE_TAC [bit_width_upper_bound] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `2 EXP r + 2 EXP (r + 1)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `2 * 2 EXP r + 2 EXP (r + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [MULT_2; GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD1; GSYM EXP_SUC; GSYM MULT_2; TWO; ADD_SUC; LE_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `bit_width x + bit_width y` THEN
   REWRITE_TAC [bit_width_mult] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `(r + 2) + bit_width y` THEN
   ASM_REWRITE_TAC [LE_ADD_LCANCEL; LE_ADD_RCANCEL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC (SPEC `r : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `qs : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [ADD_EQ_0; TWO; NOT_SUC];
   ALL_TAC] THEN
  MP_TAC (SPEC `qs : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `q : num` SUBST_VAR_TAC)) THENL
  [REWRITE_TAC [ADD_EQ_0; ADD_SUC; TWO; NOT_SUC; SUC_INJ; ONE];
   ALL_TAC] THEN
  DISCH_THEN (K ALL_TAC) THEN
  REWRITE_TAC [GSYM ADD1] THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC [TWO; GSYM ADD1; ADD_SUC] THEN
  REWRITE_TAC [GSYM TWO; bit_width_upper_bound] THEN
  MATCH_MP_TAC LTE_TRANS THEN
  EXISTS_TAC `(2 EXP q + 2 EXP SUC (SUC (SUC q))) + n` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EXP_EQ_0; TWO; NOT_SUC];
    ALL_TAC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `(2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))) * y` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_MULT_RCANCEL] THEN
    DISJ1_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC
     `(2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))) *
      (2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q)))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LE_MULT_LCANCEL] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC
     [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; GSYM EXP_ADD; ADD_SUC; SUC_ADD;
      GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
   REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC; LE_REFL];
   ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(2 EXP q + 2 EXP SUC (SUC (SUC q))) + 2 EXP SUC (SUC q)` THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LE_ADD_LCANCEL] THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   ASM_REWRITE_TAC [GSYM bit_width_upper_bound];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `2 EXP q + 2 EXP q + 2 EXP SUC (SUC q) + 2 EXP SUC (SUC (SUC q))` THEN
  REWRITE_TAC [LE_ADDR] THEN
  REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
    `2 EXP SUC q +
     (2 EXP SUC q + 2 EXP SUC (SUC q)) + 2 EXP SUC (SUC (SUC q))` THEN
  REWRITE_TAC [LE_ADDR] THEN
  REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC; LE_REFL]);;

export_thm montgomery_mult_reduce_bit_width;;

let montgomery_mult_reduce_bits_to_num = prove
 (`!n r s k x y ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc t.
     width xs = r /\
     ~(n = 0) /\
     bit_width n <= r /\
     2 EXP (r + 2) * s = k * n + 1 /\
     (!i. i <= d1 + d2 + r + 1 ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     (!i.
        d0 + d1 <= i /\ i <= d0 + d1 + r + 1 ==>
        bits_to_num (bsignal ks (t + i)) +
        2 * bits_to_num (bsignal kc (t + i)) = k) /\
     (!i.
        d0 + d1 + d2 <= i /\ i <= d0 + d1 + d2 + r + 1 ==>
        bits_to_num (bsignal ns (t + i)) +
        2 * bits_to_num (bsignal nc (t + i)) = n) /\
     montgomery_mult_reduce ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc ==>
     bits_to_num (bsignal zs (t + d0 + d1 + d2 + r + 2)) +
     2 * bits_to_num (bsignal zc (t + d0 + d1 + d2 + r + 2)) =
     montgomery_reduce n (2 EXP (r + 2)) k (x * y)`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `r : num` THEN
  X_GEN_TAC `s : num` THEN
  X_GEN_TAC `k : num` THEN
  X_GEN_TAC `x : num` THEN
  X_GEN_TAC `y : num` THEN
  X_GEN_TAC `ld : wire` THEN
  X_GEN_TAC `xs : bus` THEN
  X_GEN_TAC `xc : bus` THEN
  X_GEN_TAC `d0 : cycle` THEN
  X_GEN_TAC `ys : bus` THEN
  X_GEN_TAC `yc : bus` THEN
  X_GEN_TAC `d1 : cycle` THEN
  X_GEN_TAC `ks : bus` THEN
  X_GEN_TAC `kc : bus` THEN
  X_GEN_TAC `d2 : cycle` THEN
  X_GEN_TAC `ns : bus` THEN
  X_GEN_TAC `nc : bus` THEN
  X_GEN_TAC `zs : bus` THEN
  X_GEN_TAC `zc : bus` THEN
  X_GEN_TAC `t : cycle` THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `r : num`;
        `k : num`;
        `x : num`;
        `y : num`;
        `ld : wire`;
        `xs : bus`;
        `xc : bus`;
        `d0 : cycle`;
        `ys : bus`;
        `yc : bus`;
        `d1 : cycle`;
        `ks : bus`;
        `kc : bus`;
        `d2 : cycle`;
        `ns : bus`;
        `nc : bus`;
        `zs : bus`;
        `zc : bus`;
        `t : cycle`]
       montgomery_mult_reduce_bit_width) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (fun th -> STRIP_TAC THEN MP_TAC th) THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  REWRITE_TAC [montgomery_mult_reduce_def] THEN
  DISCH_THEN (X_CHOOSE_THEN `rs : num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
    `!i.
       i <= d1 + d2 + r + 1 ==>
       bit_cons (signal pb (t + d0 + i))
         (bits_to_num (bsignal ps (t + d0 + i)) +
          2 * bits_to_num (bsignal pc (t + d0 + i))) =
       bit_shr (bit_bound x (i + 1) * y) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC scmult_bits_to_num THEN
   EXISTS_TAC `ld : wire` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `ys : bus` THEN
   EXISTS_TAC `yc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`j : cycle`;
          `i : cycle`;
          `d1 + d2 + r + 1 : cycle`]
         LE_TRANS) THEN
    ASM_REWRITE_TAC [];
    X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + d0 + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [LE_REFL]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= d1 + d2 + r + 1 ==> signal pb (t + d0 + i) = bit_nth (x * y) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal pb (t + d0 + i))
           (bits_to_num (bsignal ps (t + d0 + i)) +
            2 * bits_to_num (bsignal pc (t + d0 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `bit_nth (bit_bound (bit_bound x (i + 1) * y) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= d1 + d2 + r + 1 ==>
       bits_to_num (bsignal ps (t + d0 + i)) +
       2 * bits_to_num (bsignal pc (t + d0 + i)) =
       bit_shr (bit_bound x (i + 1) * y) (i + 1)`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_tl
        (bit_cons (signal pb (t + d0 + i))
          (bits_to_num (bsignal ps (t + d0 + i)) +
           2 * bits_to_num (bsignal pc (t + d0 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_tl_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM ADD1; bit_shr_suc];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= d2 + r + 1 ==> (signal ld1 (t + d0 + d1 + i) <=> i = 0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + i : cycle) = (t + i) + (d0 + d1)`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `d0 + d1 : cycle`;
         `ld1 : wire`;
         `t + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `d2 + r + 1` THEN
   ASM_REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= d2 + r + 1 ==>
       signal pb1 (t + d0 + d1 + i) = bit_nth (x * y) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + i : cycle) = (t + d0 + i) + d1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`pb : wire`;
         `pbp : bus`;
         `d1 : cycle`;
         `pb1 : wire`;
         `t + d0 + i : cycle`]
      bpipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `d2 + r + 1` THEN
   ASM_REWRITE_TAC [LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bit_cons (signal qb (t + d0 + d1 + i))
         (bits_to_num (bsignal qs (t + d0 + d1 + i)) +
          2 * bits_to_num (bsignal qc (t + d0 + d1 + i))) =
       bit_shr (bit_bound (x * y) (i + 1) * k) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MATCH_MP_TAC bmult_bits_to_num THEN
   EXISTS_TAC `ld1 : wire` THEN
   EXISTS_TAC `pb1 : wire` THEN
   EXISTS_TAC `ks : bus` THEN
   EXISTS_TAC `kc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `j : cycle` THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`j : cycle`; `i : cycle`; `r + 1 : cycle`]
        LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r + 1` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD; LE_ADD_LCANCEL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= r + 1 ==> signal qb (t + d0 + d1 + i) = bit_nth (x * y * k) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal qb (t + d0 + d1 + i))
           (bits_to_num (bsignal qs (t + d0 + d1 + i)) +
            2 * bits_to_num (bsignal qc (t + d0 + d1 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_nth (bit_bound (bit_bound (x * y) (i + 1) * k) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; MULT_ASSOC; GSYM ADD1; SUC_LT];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= r + 1 ==> (signal ld2 (t + d0 + d1 + d2 + i) <=> i = 0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + d2 + i : cycle) = (t + d0 + d1 + i) + d2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`ld1 : wire`;
         `d2 : cycle`;
         `ld2 : wire`;
         `t + d0 + d1 + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `r + 1` THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       signal qb2 (t + d0 + d1 + d2 + i) = bit_nth (x * y * k) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + d2 + i : cycle) = (t + d0 + d1 + i) + d2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`qb : wire`;
         `d2 : cycle`;
         `qb2 : wire`;
         `t + d0 + d1 + i : cycle`]
      pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bit_cons (signal vb (t + d0 + d1 + d2 + i))
         (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
          2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))) =
       bit_shr (bit_bound (x * y * k) (i + 1) * n) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MATCH_MP_TAC bmult_bits_to_num THEN
   EXISTS_TAC `ld2 : wire` THEN
   EXISTS_TAC `qb2 : wire` THEN
   EXISTS_TAC `ns : bus` THEN
   EXISTS_TAC `nc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   X_GEN_TAC `j : cycle` THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`j : cycle`; `i : cycle`; `r + 1 : cycle`] LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_THEN `j <= (i : cycle)` (K ALL_TAC) THEN
   UNDISCH_THEN `i <= (r + 1 : cycle)` (K ALL_TAC) THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD; LE_ADD_LCANCEL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
       2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i)) =
       bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1)`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_tl
        (bit_cons (signal vb (t + d0 + d1 + d2 + i))
          (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
           2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_tl_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM ADD1; bit_shr_suc];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       signal vb (t + d0 + d1 + d2 + i) =
       bit_nth (x * y * k * n) i`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_hd
        (bit_cons (signal vb (t + d0 + d1 + d2 + i))
           (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
            2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))))` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_hd_cons];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_nth_def] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_nth (bit_bound (bit_bound (x * y * k) (i + 1) * n) (i + 1)) i` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT];
    ALL_TAC] THEN
   ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
   REWRITE_TAC [bit_bound_bound] THEN
   REWRITE_TAC [bit_bound_mult] THEN
   REWRITE_TAC [bit_nth_bound; GSYM ADD1; SUC_LT; MULT_ASSOC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       (signal vt (t + d0 + d1 + d2 + i) <=>
        ~(bit_bound (x * y * k * n) (i + 1) = 0))`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MP_TAC
     (SPECL
        [`ld2 : wire`;
         `vb : wire`;
         `vt : wire`;
         `t + d0 + d1 + d2 : cycle`;
         `i : cycle`]
        sticky_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   ANTS_TAC THENL
   [X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `i : cycle` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM zero_bit_nth_eq; bit_nth_bound; NOT_FORALL_THM] THEN
   REWRITE_TAC [GSYM ADD1; LT_SUC_LE] THEN
   SUBGOAL_THEN
     `(?j. j <= i /\ signal vb (t + d0 + d1 + d2 + j)) <=>
      (?j. j <= i /\ bit_nth (x * y * k * n) j)`
     ACCEPT_TAC THEN
   AP_TERM_TAC THEN
   ABS_TAC THEN
   REVERSE_TAC (ASM_CASES_TAC `j <= (i : cycle)`) THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `i : cycle` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i.
       i <= r + 1 ==>
       bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + i + 1)) +
       bit_shl
         (bits_to_num (bsignal ps (t + d0 + d1 + d2 + i)) +
          2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + i)))
         (d1 + d2) +
       (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
        2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))) +
       bit_to_num (signal vt (t + d0 + d1 + d2 + i)) =
       bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (i + 1) +
       bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1) +
       bit_to_num (~(bit_bound (x * y * k * n) (i + 1) = 0))`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_bound (bit_shr (x * y) (i + 1)) (d1 + d2) +
      bit_shl
        (bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (d1 + d2 + i + 1))
        (d1 + d2) +
      bit_shr (bit_bound (x * y * k) (i + 1) * n) (i + 1) +
      bit_to_num (~(bit_bound (x * y * k * n) (i + 1) = 0))` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    MP_TAC
      (SPECL
         [`bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (i + 1)`;
          `d1 + d2 : num`]
         bit_bound) THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [GSYM bit_shr_add; GSYM bit_shr_bound_add] THEN
    SUBGOAL_THEN
      `(i + 1) + (d1 + d2) = d1 + d2 + i + 1`
      SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    REWRITE_TAC [EQ_ADD_RCANCEL; GSYM ADD_ASSOC] THEN
    ONCE_REWRITE_TAC [GSYM bit_bound_mult] THEN
    REWRITE_TAC [bit_bound_bound];
    ALL_TAC] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN
     `!i.
        i <= d1 + d2 + r + 1 ==>
        bits_to_num (bsignal ps (t + d0 + i)) +
        2 * bits_to_num (bsignal pc (t + d0 + i)) =
        bit_shr (bit_bound x (i + 1) * y) (i + 1)`
     (MP_TAC o SPEC `d1 + d2 + i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN `width pbp0 = d1 + d2` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `pbp : bus` THEN
    EXISTS_TAC `1` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width pbp1 = d1 + d2` ASSUME_TAC THENL
   [MATCH_MP_TAC brev_width_out THEN
    EXISTS_TAC `pbp0 : bus` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
       [`bit_shr (x * y) (i + 1)`;
        `pbp1 : bus`;
        `t + d0 + d1 + d2 + i + 1 : cycle`]
       bit_nth_wire_bits_to_num) THEN
   ANTS_TAC THENL
   [X_GEN_TAC `j : num` THEN
    X_GEN_TAC `pbj : wire` THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
         [`pbp0 : bus`;
          `pbp1 : bus`;
          `j : num`;
          `pbj : wire`]
         brev_wire_out) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `jr : num` STRIP_ASSUME_TAC) THEN
    MP_TAC
      (SPECL
        [`pbp : bus`;
         `1`;
         `d1 + d2 : num`;
         `pbp0 : bus`;
         `jr : num`;
         `pbj : wire`]
        bsub_wire) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC
      (SPECL
        [`pb : wire`;
         `pbp : bus`;
         `1 + jr : num`;
         `pbj : wire`;
         `t + d0 + j + i + 1 : cycle`]
        bpipe_signal) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `(t + d0 + j + i + 1) + 1 + jr = t + d0 + d1 + d2 + i + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     REWRITE_TAC [ADD_ASSOC] THEN
     UNDISCH_THEN `jr + j + 1 = d1 + d2` (SUBST1_TAC o SYM) THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
     CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [GSYM bit_nth_add] THEN
    SUBGOAL_THEN
      `(i + 1) + j = j + i + 1`
      SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [];
     ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `d1 + d2 + i : num` THEN
    ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    UNDISCH_THEN `jr + j + 1 = d1 + d2` (SUBST1_TAC o SYM) THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN
     `!i.
        i <= r + 1 ==>
        (signal vt (t + d0 + d1 + d2 + i) <=>
         ~(bit_bound (x * y * k * n) (i + 1) = 0))`
     (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  DISCH_THEN (MP_TAC o SPEC `r + 1`) THEN
  ASM_REWRITE_TAC [LE_REFL; GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  SUBGOAL_THEN
    `bit_bound x (d1 + d2 + r + 2) = x`
    SUBST1_TAC THENL
  [REWRITE_TAC [bit_bound_id] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `r + 2` THEN
   ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADDR];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `r + 2 : num`;
        `s : num`;
        `k : num`;
        `x * y : num`]
       montgomery_reduce_bits) THEN
  ASM_REWRITE_TAC [GSYM MULT_ASSOC] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `!a b.
       bit_shl a (d1 + d2 + rs + 4) + b =
       montgomery_reduce n (2 EXP (r + 2)) k (x * y) <=>
       a = 0 /\ b = montgomery_reduce n (2 EXP (r + 2)) k (x * y)`
    MP_TAC THENL
  [REPEAT GEN_TAC THEN
   SUBGOAL_THEN `d1 + d2 + rs + 4 = (d1 + d2 + rs + 2) + 2` SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 2`];
    ALL_TAC] THEN
   UNDISCH_TAC `width xs = r` THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REVERSE_TAC EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [zero_bit_shl; ZERO_ADD];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC (TAUT `!x y. (x ==> y) /\ x ==> x /\ y`) THEN
   CONJ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [zero_bit_shl; ZERO_ADD];
    ALL_TAC] THEN
   UNDISCH_THEN
     `bit_width (montgomery_reduce n (2 EXP (r + 2)) k (x * y)) <= r + 2`
     (MP_TAC o SYM o REWRITE_RULE [GSYM bit_bound_id]) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   MP_TAC (SPECL [`bit_shl a (r + 2) + b`; `r + 2`] bit_bound) THEN
   DISCH_THEN (CONV_TAC o LAND_CONV o LAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC
     [EQ_ADD_LCANCEL_0; add_bit_shl; ADD_EQ_0; bit_shl_eq_zero;
      ONCE_REWRITE_RULE [ADD_SYM] add_bit_shr] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  SPEC_TAC (`montgomery_reduce n (2 EXP (r + 2)) k (x * y)`, `m : num`) THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `width ps0 = rs + 4` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ps : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC] THEN
  MP_TAC
    (SPECL
       [`ps : bus`;
        `0`;
        `rs + 4`;
        `ps0 : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [bsub_zero; ZERO_ADD; LE_0] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d : num`
       (X_CHOOSE_THEN `ps2 : bus`
          (X_CHOOSE_THEN `ps1 : bus`
             STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [bnil_bappend] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; GSYM bit_shl_add; add_bit_shl; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 4 + d1 + d2 = d1 + d2 + rs + 4` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1))) (d1 + d2) +
     bit_shl (bits_to_num (bsignal ps1 (t + d0 + d1 + d2 + r + 1)))
      (d1 + d2 + rs + 4) +
     bit_shl (2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1)) +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     bit_shl (bits_to_num (bsignal ps1 (t + d0 + d1 + d2 + r + 1)))
      (d1 + d2 + rs + 4) +
     bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1))) (d1 + d2) +
     bit_shl (2 * bits_to_num (bsignal pc (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1)) +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC
    [GSYM bit_shl_one; ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `width pc0 = rs + 3` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `pc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`pc : bus`;
        `0`;
        `rs + 3`;
        `pc0 : bus`]
       bsub_bappend_exists) THEN
  ASM_REWRITE_TAC [bsub_zero; ZERO_ADD; LE_0] THEN
  DISCH_THEN
    (X_CHOOSE_THEN `d : num`
       (X_CHOOSE_THEN `pc2 : bus`
          (X_CHOOSE_THEN `pc1 : bus`
             STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [bnil_bappend] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; GSYM bit_shl_add; add_bit_shl; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 3 + d1 + d2 + 1 = d1 + d2 + rs + 4` SUBST1_TAC THENL
  [REWRITE_TAC [GSYM (NUM_REDUCE_CONV `3 + 1`); ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bit_shl (bits_to_num (bsignal pc1 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + rs + 4) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     bit_shl (bits_to_num (bsignal pc1 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + rs + 4) +
     bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC
    [GSYM bit_shl_one; ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 +
     bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) =
     (bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
      bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
        (d1 + d2)) +
     bit_shl (bits_to_num (bsignal pc0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal vs (t + d0 + d1 + d2 + r + 1)) +
     (bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) +
      bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1)`
    SUBST1_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal pbp1 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ps0 (t + d0 + d1 + d2 + r + 1)))
       (d1 + d2) =
     bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `bappend sa0 sa2 = sa` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `d1 + d2 + rs + 4 = (d1 + d2) + (rs + 4)` SUBST1_TAC THENL
    [REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bits_to_num] THEN
   MP_TAC
     (SPECL
        [`pbp1 : bus`;
         `sa0 : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bconnect_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`ps0 : bus`;
         `sa2 : bus`;
         `t + d0 + d1 + d2 + r + 1`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   AP_TERM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `sa : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`pc0 : bus`;
        `sb : bus`;
        `t + d0 + d1 + d2 + r + 1`]
       bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`vs : bus`;
        `sc : bus`;
        `t + d0 + d1 + d2 + r + 1`]
       bdelay_bsignal) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `bit_to_num (signal vt (t + d0 + d1 + d2 + r + 1)) +
     bit_shl (bits_to_num (bsignal vc (t + d0 + d1 + d2 + r + 1))) 1 =
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN `bappend (bwire sd0) sd2 = sd` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `d1 + d2 + rs + 2 = 1 + (d1 + d2 + rs + 1)` SUBST1_TAC THENL
    [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   REWRITE_TAC [bappend_bwire_bsignal; bits_to_num_cons; bit_cons_def] THEN
   MP_TAC
     (SPECL
        [`vt : wire`;
         `sd0 : wire`;
         `t + d0 + d1 + d2 + r + 1`]
        delay_signal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MP_TAC
     (SPECL
        [`vc : bus`;
         `sd2 : bus`;
         `t + d0 + d1 + d2 + r + 1`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [bit_shl_one];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal sb (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2)) =
     bit_shl (bits_to_num (bsignal sb (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal sa (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
     bits_to_num (bsignal sd (t + d0 + d1 + d2 + r + 2)) =
     bits_to_num (bsignal ms (t + d0 + d1 + d2 + r + 2)) +
     2 * bits_to_num (bsignal mc (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [SUBGOAL_THEN
     `bappend sa1
        (bappend (bwire sa3) (bappend (bwire sa4) (bwire sa5))) = sa`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 4 = (d1 + d2 + rs + 1) + 1 + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 3`;
        NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def;
       NUM_REDUCE_CONV `1 + 1`; NUM_REDUCE_CONV `1 + 2`];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend sd1 (bwire sd3) = sd`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 2 = (d1 + d2 + rs + 1) + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend ms1 (bappend (bwire ms2) (bwire ms3)) = ms`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 3 = (d1 + d2 + rs + 1) + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend mc1 (bappend (bwire mc3) (bwire mc4)) = mc`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN
      `d1 + d2 + rs + 3 = (d1 + d2 + rs + 1) + 1 + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   REWRITE_TAC
     [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
      bwire_bits_to_num; GSYM bit_shl_one] THEN
   SUBGOAL_THEN `width sa1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sa : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width sd1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `sd : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width ms1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `ms : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   SUBGOAL_THEN `width mc1 = d1 + d2 + rs + 1` ASSUME_TAC THENL
   [MATCH_MP_TAC bsub_width THEN
    EXISTS_TAC `mc : bus` THEN
    EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`] THEN
   SUBGOAL_THEN `1 + d1 + d2 + rs + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
   [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   SUBGOAL_THEN `1 + d1 + d2 + rs + 2 = d1 + d2 + rs + 3` SUBST1_TAC THENL
   [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `(bits_to_num (bsignal sa1 (t + d0 + d1 + d2 + r + 2)) +
       bits_to_num (bsignal sc (t + d0 + d1 + d2 + r + 2)) +
       bits_to_num (bsignal sd1 (t + d0 + d1 + d2 + r + 2))) +
      bit_shl (bit_to_num (signal sa3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal sa4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal sa5 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3) +
      bit_shl (bit_to_num (signal sd3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC)) THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sa1 : bus`;
         `sc : bus`;
         `sd1 : bus`;
         `ms1 : bus`;
         `mc1 : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        badder3_bits_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [GSYM bit_shl_one; GSYM ADD_ASSOC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bits_to_num (bsignal ms1 (t + d0 + d1 + d2 + r + 2)) +
      bit_shl (bits_to_num (bsignal mc1 (t + d0 + d1 + d2 + r + 2))) 1 +
      bit_shl (bit_to_num (signal ms2 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_shl
        (bit_to_num (signal sa3 (t + d0 + d1 + d2 + r + 2)) +
         bit_to_num (signal sd3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal sa4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal sa5 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sa3 : wire`;
         `sd3 : wire`;
         `ms2 : wire`;
         `mc3 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        adder2_bit_to_num) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_shl
        (bit_to_num (signal ms2 (t + d0 + d1 + d2 + r + 2)) +
         2 * bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 1) +
      bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 2) +
      bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
        (d1 + d2 + rs + 3)` THEN
   REVERSE_TAC CONJ_TAC THENL
   [REWRITE_TAC [add_bit_shl; GSYM bit_shl_one; GSYM bit_shl_add] THEN
    SUBGOAL_THEN `1 + d1 + d2 + rs + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
    [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MP_TAC
     (SPECL
        [`sa4 : wire`;
         `ms3 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        connect_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`sa5 : wire`;
         `mc4 : wire`;
         `t + d0 + d1 + d2 + r + 2`]
        connect_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend sb0 (bappend (bwire sb1) (bwire sb2)) = sb`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `rs + 3 = (rs + 1) + 1 + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC
      [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC
     [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `width sb0 = rs + 1` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `sb : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bappend ms0 (bappend ms4 (bwire ms3)) = ms`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2 + 1) + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  POP_ASSUM (K ALL_TAC) THEN
  SUBGOAL_THEN `width ms0 = d1 + d2 + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ms : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width ms4 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `ms : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `bappend mc0 (bappend mc2 (bappend (bwire mc3) (bwire mc4))) = mc`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2) + (rs + 1) + 1 + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC
      [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`;
       NUM_REDUCE_CONV `1 + 2`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one] THEN
  SUBGOAL_THEN `width mc0 = d1 + d2` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `mc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width mc2 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `mc : bus` THEN
   EXISTS_TAC `d1 + d2 : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN
    `rs + 1 + d1 + d2 + 1 = d1 + d2 + rs + 2`
    SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `1 + d1 + d2 + rs + 2 = d1 + d2 + rs + 3`
    SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_shl (bits_to_num (bsignal sb0 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal sb1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bits_to_num (bsignal ms0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal ms4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bits_to_num (bsignal mc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal mc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) =
     bits_to_num (bsignal ms0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal mc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl
       (bits_to_num (bsignal sb0 (t + d0 + d1 + d2 + r + 2)) +
        bits_to_num (bsignal ms4 (t + d0 + d1 + d2 + r + 2)) +
        bits_to_num (bsignal mc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl
       (bit_to_num (signal sb1 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal ms3 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc3 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl
       (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3)`
    SUBST1_TAC THENL
  [REWRITE_TAC [add_bit_shl; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ms0 : bus`;
        `zs0 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`mc0 : bus`;
        `zc0 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`sb0 : bus`;
        `ms4 : bus`;
        `mc2 : bus`;
        `zs1 : bus`;
        `zc2 : bus`;
        `t + d0 + d1 + d2 + r + 2`]
       badder3_bits_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`sb1 : wire`;
        `ms3 : wire`;
        `mc3 : wire`;
        `zs2 : wire`;
        `mw : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       adder3_bit_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC
    [add_bit_shl; GSYM bit_shl_one; GSYM ADD_ASSOC;
     ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     NUM_REDUCE_CONV `1 + 1`; NUM_REDUCE_CONV `2 + 1`] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal zs0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal zc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal zs1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bits_to_num (bsignal zc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 2) +
     bit_shl (bit_to_num (signal zs2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bit_shl (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) +
     bit_shl (bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3) =
     bits_to_num (bsignal zs0 (t + d0 + d1 + d2 + r + 2)) +
     bit_shl (bits_to_num (bsignal zs1 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 1) +
     bit_shl (bit_to_num (signal zs2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 2) +
     bit_shl (bits_to_num (bsignal zc0 (t + d0 + d1 + d2 + r + 2))) 1 +
     bit_shl (bits_to_num (bsignal zc2 (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + 2) +
     bit_shl
       (bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)) +
        bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)))
       (d1 + d2 + rs + 3)`
    SUBST1_TAC THENL
  [REWRITE_TAC [add_bit_shl; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_to_num (signal sb2 (t + d0 + d1 + d2 + r + 2)) +
     bit_to_num (signal mc4 (t + d0 + d1 + d2 + r + 2)) +
     bit_to_num (signal mw (t + d0 + d1 + d2 + r + 2)) =
     bit_cons
       ((signal sb2 (t + d0 + d1 + d2 + r + 2) <=>
         signal mc4 (t + d0 + d1 + d2 + r + 2)) <=>
        signal mw (t + d0 + d1 + d2 + r + 2))
       (bit_to_num
          ((signal sb2 (t + d0 + d1 + d2 + r + 2) /\
            signal mc4 (t + d0 + d1 + d2 + r + 2)) \/
           (signal sb2 (t + d0 + d1 + d2 + r + 2) /\
            signal mw (t + d0 + d1 + d2 + r + 2)) \/
           (signal mc4 (t + d0 + d1 + d2 + r + 2) /\
            signal mw (t + d0 + d1 + d2 + r + 2))))`
    SUBST1_TAC THENL
  [BOOL_CASES_TAC `signal sb2 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mc4 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mw (t + d0 + d1 + d2 + r + 2)` THEN
   REWRITE_TAC [bit_to_num_def; bit_cons_def] THEN
   NUM_REDUCE_TAC;
   ALL_TAC] THEN
  REWRITE_TAC
    [bit_cons_def; GSYM bit_shl_one; add_bit_shl;
     ONCE_REWRITE_RULE [ADD_SYM] (GSYM bit_shl_add);
     GSYM ADD_ASSOC; NUM_REDUCE_CONV `3 + 1`] THEN
  REWRITE_TAC [ADD_ASSOC] THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
  ASM_REWRITE_TAC [GSYM ADD_ASSOC; bit_to_num_zero; NOT_OR_THM] THEN
  STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SUBGOAL_THEN
    `((signal sb2 (t + d0 + d1 + d2 + r + 2) <=>
       signal mc4 (t + d0 + d1 + d2 + r + 2)) <=>
      signal mw (t + d0 + d1 + d2 + r + 2)) <=>
     (signal sb2 (t + d0 + d1 + d2 + r + 2) \/
      signal mc4 (t + d0 + d1 + d2 + r + 2) \/
      signal mw (t + d0 + d1 + d2 + r + 2))`
    SUBST1_TAC THENL
  [POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   POP_ASSUM MP_TAC THEN
   BOOL_CASES_TAC `signal sb2 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mc4 (t + d0 + d1 + d2 + r + 2)` THEN
   BOOL_CASES_TAC `signal mw (t + d0 + d1 + d2 + r + 2)` THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  MP_TAC
    (SPECL
       [`sb2 : wire`;
        `mc4 : wire`;
        `mw : wire`;
        `zc3 : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       or3_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `bappend zs0 (bappend zs1 (bwire zs2)) = zs`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2 + 1) + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend zc0 (bappend (bwire zc1) (bappend zc2 (bwire zc3))) = zc`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN
     `d1 + d2 + rs + 3 = (d1 + d2) + 1 + (rs + 1) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM wire_def] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC; GSYM wire_def] THEN
   SUBGOAL_THEN
     `d1 + d2 + 1 + rs + 1 = d1 + d2 + rs + 2`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC
    [bappend_bits_to_num; add_bit_shl; bwire_width; GSYM bit_shl_add;
     bwire_bits_to_num; GSYM bit_shl_one; GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `width zs0 = d1 + d2 + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zs : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zs1 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zs : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zc0 = d1 + d2` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width zc2 = rs + 1` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `zc : bus` THEN
   EXISTS_TAC `d1 + d2 + 1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [GSYM ADD_ASSOC] THEN
  SUBGOAL_THEN `rs + 1 + d1 + d2 + 1 = d1 + d2 + rs + 2` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN `1 + d1 + d2 + 1 = d1 + d2 + 2` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  SUBGOAL_THEN `rs + 1 + d1 + d2 + 2 = d1 + d2 + rs + 3` SUBST1_TAC THENL
  [CONV_TAC (LAND_CONV (REWR_CONV ADD_ASSOC THENC REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL; NUM_REDUCE_CONV `1 + 2`];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ground`;
        `zc1 : wire`;
        `t + d0 + d1 + d2 + r + 2`]
       connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC
    [EQ_ADD_LCANCEL; ground_signal; bit_to_num_false; zero_bit_shl;
     ZERO_ADD]);;

export_thm montgomery_mult_reduce_bits_to_num;;

let montgomery_mult_compress_bits_to_num = prove
 (`!n r x xs xc d rx ry rz ys yc t.
     width rx = r /\
     ~(n = 0) /\
     bit_width x <= r + 2 /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     bsignal xs (t + d) = bsignal xs t /\
     bsignal xc (t + d) = bsignal xc t /\
     bits_to_num (bsignal rx (t + d)) = (2 EXP r) MOD n /\
     bits_to_num (bsignal ry (t + d)) = (2 * (2 EXP r)) MOD n /\
     bits_to_num (bsignal rz (t + d)) = (3 * (2 EXP r)) MOD n /\
     montgomery_mult_compress xs xc d rx ry rz ys yc ==>
     (bits_to_num (bsignal ys (t + d)) +
      2 * bits_to_num (bsignal yc (t + d))) MOD n = x MOD n`,
  X_GEN_TAC `n : num` THEN
  X_GEN_TAC `k : num` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_mult_compress_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `k = r + 1` SUBST_VAR_TAC THENL
  [UNDISCH_THEN `width rx = k` (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend (bwire ys0) ys1 = ys` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  SUBGOAL_THEN `bappend (bwire yc0) yc1 = yc` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
   ALL_TAC] THEN
  REWRITE_TAC [bappend_bits_to_num] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `((bit_to_num (signal ys0 (t + d)) +
       2 * bit_to_num (signal yc0 (t + d))) +
      2 * (bits_to_num (bsignal ys1 (t + d)) +
           2 * bits_to_num (bsignal yc1 (t + d)))) MOD n` THEN
  CONJ_TAC THENL
  [AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC
     [bwire_width; bwire_bits_to_num; bit_shl_one; LEFT_ADD_DISTRIB] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   MATCH_ACCEPT_TAC ADD_SYM;
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`xs0 : wire`;
        `rn0 : wire`;
        `ys0 : wire`;
        `yc0 : wire`;
        `t + d : cycle`]
       adder2_bit_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC
    (SPECL
       [`xs1 : bus`;
        `xc0 : bus`;
        `rn1 : bus`;
        `ys1 : bus`;
        `yc1 : bus`;
        `t + d : cycle`]
       badder3_bits_to_num) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC
    `(((bit_to_num (signal xs0 (t + d)) +
        2 * bits_to_num (bsignal xs1 (t + d))) +
       2 * bits_to_num (bsignal xc0 (t + d))) +
      bits_to_num (bsignal rn (t + d))) MOD n` THEN
  CONJ_TAC THENL
  [AP_THM_TAC THEN
   AP_TERM_TAC THEN
   SUBGOAL_THEN `bappend (bwire rn0) rn1 = rn` (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def];
    ALL_TAC] THEN
   REWRITE_TAC
     [bwire_width; bwire_bits_to_num; bit_shl_one; LEFT_ADD_DISTRIB;
      bappend_bits_to_num] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bits_to_num (bsignal rn (t + d)) =
     bit_shl
       (bit_to_num (signal nsd (t + d)) +
        2 * bit_to_num (signal ncd (t + d)))
       (r + 1) MOD n` SUBST1_TAC THENL
  [MP_TAC
     (SPECL
        [`ncd : wire`;
         `rnh : bus`;
         `rnl : bus`;
         `rn : bus`;
         `t + d : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`nsd : wire`;
         `rz : bus`;
         `ry : bus`;
         `rnh : bus`;
         `t + d : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`nsd : wire`;
         `rx : bus`;
         `bground (r + 1)`;
         `rnl : bus`;
         `t + d : cycle`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   BOOL_CASES_TAC `signal ncd (t + d)` THEN
   BOOL_CASES_TAC `signal nsd (t + d)` THEN
   ASM_REWRITE_TAC
    [ONCE_REWRITE_RULE [MULT_SYM] bit_shl_def; ONE_MULT; ZERO_MULT;
     bground_bits_to_num; bit_to_num_true; bit_to_num_false; MULT_1;
     NUM_REDUCE_CONV `1 + 2`; ZERO_ADD; MULT_0; ADD_0] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC MOD_0 THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN MP_TAC th) THEN
  MP_TAC (SPEC `n : num` MOD_MOD_REFL') THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MP_TAC
    (SPECL
       [`ns : wire`;
        `d : num`;
        `nsd : wire`;
        `t : cycle`]
       pipe_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC
    (SPECL
       [`nc : wire`;
        `d : num`;
        `ncd : wire`;
        `t : cycle`]
       pipe_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `signal xs0 (t + d) = signal xs0 t` SUBST1_TAC THENL
  [MATCH_MP_TAC wire_signal THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `bsignal xs1 (t + d) = bsignal xs1 t` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_bsignal THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `1` THEN
   EXISTS_TAC `r : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `bsignal xc0 (t + d) = bsignal xc0 t` SUBST1_TAC THENL
  [MATCH_MP_TAC bsub_bsignal THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `0` THEN
   EXISTS_TAC `r : num` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width xs1 = r` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `1` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN `width xc0 = r` ASSUME_TAC THENL
  [MATCH_MP_TAC bsub_width THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `0` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_CASES_TAC `signal xs2 t /\ signal xc1 t /\ signal xc2 t` THENL
  [POP_ASSUM STRIP_ASSUME_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   SUBGOAL_THEN `x < 2 EXP SUC (SUC (SUC r))` MP_TAC THENL
   [MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `2 EXP bit_width x` THEN
    REWRITE_TAC [lt_exp_bit_width; LE_EXP] THEN
    NUM_REDUCE_TAC THEN
    REWRITE_TAC [ADD1; GSYM ADD_ASSOC] THEN
    REWRITE_TAC [NUM_REDUCE_CONV `1 + 1`] THEN
    ASM_REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   REWRITE_TAC [NOT_LT] THEN
   UNDISCH_THEN
     `bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x`
     (SUBST1_TAC o SYM) THEN
   SUBGOAL_THEN
     `bappend (bwire xs0) (bappend xs1 (bwire xs2)) = xs`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `r + 2 = 1 + (r + 1)` SUBST1_TAC THENL
    [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
    MATCH_MP_TAC bsub_add THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    ASM_REWRITE_TAC [GSYM wire_def];
    ALL_TAC] THEN
   SUBGOAL_THEN
     `bappend xc0 (bappend (bwire xc1) (bwire xc2)) = xc`
     (SUBST1_TAC o SYM) THENL
   [ASM_REWRITE_TAC [GSYM bsub_all] THEN
    SUBGOAL_THEN `r + 2 = r + (1 + 1)` SUBST1_TAC THENL
    [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
     ALL_TAC] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
    MATCH_MP_TAC bsub_add THEN
    ASM_REWRITE_TAC [GSYM wire_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC
     [bappend_bits_to_num; bwire_bits_to_num; bwire_width;
      GSYM bit_shl_one; bit_to_num_true; add_bit_shl; GSYM bit_shl_add] THEN
   REWRITE_TAC
     [GSYM ADD_ASSOC; one_bit_shl; GSYM ADD1;
      GSYM (ONCE_REWRITE_RULE [ADD_SYM] ADD1)] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC
     `2 EXP SUC r +
      2 EXP SUC r +
      2 EXP SUC (SUC r)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD_ASSOC; GSYM MULT_2; GSYM EXP_SUC; LE_REFL];
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADDR]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bit_to_num (signal ns t) +
     2 * bit_to_num (signal nc t) =
     bit_to_num (signal xs2 t) +
     bit_to_num (signal xc1 t) +
     2 * bit_to_num (signal xc2 t)`
    SUBST1_TAC THENL
  [MP_TAC
     (SPECL
        [`nct : wire`;
         `xc2 : wire`;
         `nc : wire`;
         `t : cycle`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_THEN
     `adder2 xs2 xc1 ns nct`
     (STRIP_ASSUME_TAC o REWRITE_RULE [adder2_def]) THEN
   MP_TAC
     (SPECL
        [`xs2 : wire`;
         `xc1 : wire`;
         `nct : wire`;
         `t : cycle`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`xs2 : wire`;
         `xc1 : wire`;
         `ns : wire`;
         `t : cycle`]
        xor2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_TAC `~(signal xs2 t /\ signal xc1 t /\ signal xc2 t)` THEN
   BOOL_CASES_TAC `signal xs2 t` THEN
   BOOL_CASES_TAC `signal xc1 t` THEN
   BOOL_CASES_TAC `signal xc2 t` THEN
   REWRITE_TAC
     [bit_to_num_true; bit_to_num_false; ZERO_ADD; MULT_0; ADD_0; MULT_1;
      NUM_REDUCE_CONV `1 + 1`];
   ALL_TAC] THEN
  UNDISCH_THEN
    `bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x`
    (SUBST1_TAC o SYM) THEN
  SUBGOAL_THEN
    `bappend (bwire xs0) (bappend xs1 (bwire xs2)) = xs`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN `r + 2 = 1 + (r + 1)` SUBST1_TAC THENL
   [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MATCH_MP_TAC bsub_add THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ASM_REWRITE_TAC [GSYM wire_def];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `bappend xc0 (bappend (bwire xc1) (bwire xc2)) = xc`
    (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [GSYM bsub_all] THEN
   SUBGOAL_THEN `r + 2 = r + (1 + 1)` SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`];
    ALL_TAC] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [ZERO_ADD; GSYM wire_def] THEN
   MATCH_MP_TAC bsub_add THEN
   ASM_REWRITE_TAC [GSYM wire_def];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [bappend_bits_to_num; bwire_bits_to_num; bwire_width;
     GSYM bit_shl_one; bit_to_num_true; add_bit_shl; GSYM bit_shl_add] THEN
  REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
  CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
  REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
  CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
  REWRITE_TAC [GSYM ADD_ASSOC]);;

export_thm montgomery_mult_compress_bits_to_num;;

let montgomery_mult_signal_load = prove
 (`!ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc t.
     signal ld t /\
     montgomery_mult
       ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc ==>
     ~signal dn t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_mult_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`jp : wire`;
        `dn : wire`]
       connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  MATCH_MP_TAC
    (SPECL
       [`ld : wire`;
        `jb : bus`;
        `jp : wire`;
        `t : cycle`]
       counter_pulse_signal_load) THEN
  ASM_REWRITE_TAC []);;

export_thm montgomery_mult_signal_load;;

let montgomery_mult_signal = prove
 (`!r ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc t k.
     width xs = r /\
     d3 <= d0 + d1 + d2 + r + 1 /\
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal jb t) + d0 + d1 + d2 + r + 3 =
     2 EXP width jb + width jb + d3 /\
     montgomery_mult
       ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc ==>
     (signal dn (t + k) <=> d3 + k = d0 + d1 + d2 + r + 2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_mult_def] THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`jp : wire`;
        `dn : wire`]
       connect_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  UNDISCH_THEN
    `d3 <= d0 + d1 + d2 + r + 1`
    (X_CHOOSE_THEN `dk : num` STRIP_ASSUME_TAC o
     REWRITE_RULE [LE_EXISTS]) THEN
  MP_TAC
    (SPECL
       [`dk : num`;
        `ld : wire`;
        `jb : bus`;
        `jp : wire`;
        `t : cycle`;
        `k : cycle`]
       counter_pulse_signal) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   CONV_TAC (REWR_CONV (GSYM (SPEC `d3 : num` EQ_ADD_RCANCEL))) THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   POP_ASSUM (CONV_TAC o LAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 2`];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM (SPEC `d3 : num` EQ_ADD_LCANCEL)))) THEN
  REWRITE_TAC [ADD_ASSOC] THEN
  POP_ASSUM
    (CONV_TAC o LAND_CONV o RAND_CONV o LAND_CONV o REWR_CONV o SYM) THEN
  REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`]);;

export_thm montgomery_mult_signal;;

let montgomery_mult_bits_to_num = prove
 (`!n r s k x y ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc
    t.
     width xs = r /\
     ~(n = 0) /\
     bit_width n <= r /\
     2 EXP (r + 2) * s = k * n + 1 /\
     d3 <= d0 + d1 + d2 + r + 1 /\
     (!i. i <= d0 + d1 + d2 + d4 + r + 2 ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        d0 <= i /\ i <= d0 + r + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     (!i.
        d0 + d1 <= i /\ i <= d0 + d1 + r + 1 ==>
        bits_to_num (bsignal ks (t + i)) +
        2 * bits_to_num (bsignal kc (t + i)) = k) /\
     (!i.
        d0 + d1 + d2 <= i /\ i <= d0 + d1 + d2 + r + 1 ==>
        bits_to_num (bsignal ns (t + i)) +
        2 * bits_to_num (bsignal nc (t + i)) = n) /\
     bits_to_num (bsignal jb t) + d0 + d1 + d2 + r + 3 =
     2 EXP width jb + width jb + d3 /\
     bits_to_num (bsignal rx (t + d0 + d1 + d2 + d4 + r + 3)) =
     (2 EXP r) MOD n /\
     bits_to_num (bsignal ry (t + d0 + d1 + d2 + d4 + r + 3)) =
     (2 * (2 EXP r)) MOD n /\
     bits_to_num (bsignal rz (t + d0 + d1 + d2 + d4 + r + 3)) =
     (3 * (2 EXP r)) MOD n /\
     montgomery_mult
       ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc ==>
     (bits_to_num (bsignal zs (t + d0 + d1 + d2 + d4 + r + 3)) +
      2 * bits_to_num (bsignal zc (t + d0 + d1 + d2 + d4 + r + 3))) MOD n =
     ((x * y) * s) MOD n`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`r : num`; `ld : wire`; `xs : bus`; `xc : bus`; `d0 : cycle`;
        `ys : bus`; `yc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
        `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
        `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `dn : wire`;
        `zs : bus`; `zc : bus`; `t : cycle`]
       montgomery_mult_signal) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM
    (STRIP_ASSUME_TAC o CONV_RULE (REWR_CONV montgomery_mult_def)) THEN
  SUBGOAL_THEN
    `t + d0 + d1 + d2 + d4 + r + 3 = (t + d0 + d1 + d2 + r + 3) + d4`
    ASSUME_TAC THENL
  [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [ADD_ASSOC];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`n : num`;
        `2 EXP (r + 2)`;
        `s : num`;
        `k : num`;
        `x * y : num`]
       montgomery_reduce_correct) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC montgomery_mult_compress_bits_to_num THEN
  EXISTS_TAC `r : num` THEN
  EXISTS_TAC `qsp : bus` THEN
  EXISTS_TAC `qcp : bus` THEN
  EXISTS_TAC `rx : bus` THEN
  EXISTS_TAC `ry : bus` THEN
  EXISTS_TAC `rz : bus` THEN
  CONJ_TAC THENL
  [UNDISCH_THEN `width xs = r` (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [MP_TAC
     (SPECL
        [`n : num`;
         `r : num`;
         `k : num`;
         `x : num`;
         `y : num`;
         `ld : wire`;
         `xs : bus`;
         `xc : bus`;
         `d0 : num`;
         `ys : bus`;
         `yc : bus`;
         `d1 : num`;
         `ks : bus`;
         `kc : bus`;
         `d2 : num`;
         `ns : bus`;
         `nc : bus`;
         `ps : bus`;
         `pc : bus`;
         `t : cycle`]
        montgomery_mult_reduce_bit_width) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!d.
       d <= d4 ==>
       (signal jpd ((t + d0 + d1 + d2 + r + 2) + d) <=> d = 0)`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   UNDISCH_THEN
     `d3 <= d0 + d1 + d2 + r + 1`
     (X_CHOOSE_THEN `dk : num` STRIP_ASSUME_TAC o
      REWRITE_RULE [LE_EXISTS]) THEN
   SUBGOAL_THEN
     `(t + d0 + d1 + d2 + r + 2) + d = (t + (dk + d + 1)) + d3`
     SUBST1_TAC THENL
   [REWRITE_TAC
      [GSYM ADD_ASSOC; GSYM (NUM_REDUCE_CONV `1 + 1`); EQ_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    POP_ASSUM (SUBST1_TAC o SYM) THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`jp : wire`;
         `d3 : num`;
         `jpd : wire`;
         `t + (dk + d + 1) : cycle`]
        pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   UNDISCH_THEN
     `!k.
        (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) ==>
        (signal dn (t + k) <=> d3 + k = d0 + d1 + d2 + r + 2)`
     (MP_TAC o SPEC `dk + d + 1 : cycle`) THEN
   ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `dk + d + 1` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(d0 + d1 + d2 + r + 1) + d + 1` THEN
    CONJ_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; LE_ADDR];
     REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
     REWRITE_TAC
       [ADD_ASSOC; LE_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `1 + 1`)] THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL]];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`jp : wire`;
         `dn : wire`]
        connect_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV ADD_SYM))) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `1 + 1`; EQ_ADD_RCANCEL_0];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [SUBGOAL_THEN
     `t + d0 + d1 + d2 + r + 3 = (t + d0 + d1 + d2 + r + 2) + 1`
     SUBST1_TAC THENL
   [REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`qsr : bus`;
         `qsp : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`qcr : bus`;
         `qcp : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`jpd : wire`;
         `ps : bus`;
         `qsp : bus`;
         `qsr : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`jpd : wire`;
         `pc : bus`;
         `qcp : bus`;
         `qcr : bus`;
         `t + d0 + d1 + d2 + r + 2`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `signal jpd (t + d0 + d1 + d2 + r + 2)`
     (SUBST1_TAC o EQT_INTRO) THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [LE_0; ADD_0];
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   MATCH_MP_TAC montgomery_mult_reduce_bits_to_num THEN
   EXISTS_TAC `s : num` THEN
   EXISTS_TAC `ld : wire` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `ys : bus` THEN
   EXISTS_TAC `yc : bus` THEN
   EXISTS_TAC `ks : bus` THEN
   EXISTS_TAC `kc : bus` THEN
   EXISTS_TAC `ns : bus` THEN
   EXISTS_TAC `nc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `d1 + d2 + r + 1` THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC
     [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 1`);
      LE_ADD];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!d.
       d <= d4 ==>
       bsignal qsp ((t + d0 + d1 + d2 + r + 3) + d) =
       bsignal qsp (t + d0 + d1 + d2 + r + 3) /\
       bsignal qcp ((t + d0 + d1 + d2 + r + 3) + d) =
       bsignal qcp (t + d0 + d1 + d2 + r + 3)`
    (MP_TAC o SPEC `d4 : num`) THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC [ADD_0];
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC [ADD_SUC] THEN
   REWRITE_TAC [ADD1] THEN
   MP_TAC
     (SPECL
        [`qsr : bus`;
         `qsp : bus`;
         `(t + d0 + d1 + d2 + r + 3) + d`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`qcr : bus`;
         `qcp : bus`;
         `(t + d0 + d1 + d2 + r + 3) + d`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`jpd : wire`;
         `ps : bus`;
         `qsp : bus`;
         `qsr : bus`;
         `(t + d0 + d1 + d2 + r + 3) + d`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC
     (SPECL
        [`jpd : wire`;
         `pc : bus`;
         `qcp : bus`;
         `qcr : bus`;
         `(t + d0 + d1 + d2 + r + 3) + d`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `~signal jpd ((t + d0 + d1 + d2 + r + 3) + d)`
     (SUBST1_TAC o EQF_INTRO) THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `SUC d`) THEN
    ASM_REWRITE_TAC [NOT_SUC] THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    REWRITE_TAC
      [ONCE_REWRITE_RULE [ADD_SYM] ADD1; ADD_ASSOC;
       NUM_REDUCE_CONV `2 + 1`];
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `SUC d` THEN
   ASM_REWRITE_TAC [SUC_LE];
   ALL_TAC] THEN
  REWRITE_TAC [LE_REFL] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC []);;

export_thm montgomery_mult_bits_to_num;;

let montgomery_double_exp_bits_to_num = prove
 (`!n r s k m x ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc
    t l. ?d. !j.
     width xs = r /\
     bit_width n <= r /\
     2 EXP (r + 2) * s = k * n + 1 /\
     d3 <= d0 + d1 + d2 + r + 1 /\
     d3 + d4 + 1 = l /\
     width mb + l <= d0 + d1 + d2 + d4 + r + 4 /\
     (!i. i <= d + j ==> (signal ld (t + i) <=> i <= l)) /\
     bits_to_num (bsignal mb (t + l + l + 1)) + m = 2 EXP width mb + 1 /\
     (bits_to_num (bsignal xs (t + l + l)) +
      2 * bits_to_num (bsignal xc (t + l + l))) MOD n =
     (x * 2 EXP (r + 2)) MOD n /\
     (!i.
        i < d ==>
        bits_to_num (bsignal ks (t + l + i)) +
        2 * bits_to_num (bsignal kc (t + l + i)) = k) /\
     (!i.
        i < d ==>
        bits_to_num (bsignal ns (t + l + i)) +
        2 * bits_to_num (bsignal nc (t + l + i)) = n) /\
     (!i.
        i < d ==>
        bits_to_num (bsignal jb (t + l + i)) + d0 + d1 + d2 + r + 3 =
        2 EXP width jb + width jb + d3) /\
     (!i.
        i < d ==>
        bits_to_num (bsignal rx (t + l + i)) = (2 EXP r) MOD n) /\
     (!i.
        i < d ==>
        bits_to_num (bsignal ry (t + l + i)) = (2 * (2 EXP r)) MOD n) /\
     (!i.
        i < d ==>
        bits_to_num (bsignal rz (t + l + i)) = (3 * (2 EXP r)) MOD n) /\
     montgomery_double_exp
       ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc ==>
     (!i. i <= d + j ==> (signal dn (t + l + i) <=> d <= i)) /\
     (bits_to_num (bsignal ys (t + l + d + j)) +
      2 * bits_to_num (bsignal yc (t + l + d + j))) MOD n =
     ((x EXP (2 EXP m)) * (2 EXP (r + 2))) MOD n`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `?d. l + 1 + (d0 + d1 + d2 + d4 + r + 4) * m = d`
    STRIP_ASSUME_TAC THENL
  [MATCH_ACCEPT_TAC EXISTS_REFL';
   ALL_TAC] THEN
  EXISTS_TAC `d : cycle` THEN
  GEN_TAC THEN
  REWRITE_TAC [montgomery_double_exp_def] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `2 EXP (r + 2) * s = k * n + 1` THEN
   ASM_REWRITE_TAC [MULT_EQ_1; MULT_0; ZERO_ADD] THEN
   REWRITE_TAC [DE_MORGAN_THM] THEN
   DISJ1_TAC THEN
   REWRITE_TAC [TWO; ADD_SUC; EXP_SUC; MULT_EQ_1] THEN
   REWRITE_TAC [ONE; NOT_SUC; SUC_INJ];
   ALL_TAC] THEN
  ASM_CASES_TAC `m = 0` THENL
  [SUBGOAL_THEN `F` CONTR_TAC THEN
   MP_TAC (SPEC `bsignal mb (t + l + l + 1)` bits_to_num_bound) THEN
   REWRITE_TAC [NOT_LT; length_bsignal] THEN
   ONCE_REWRITE_TAC [GSYM LE_SUC] THEN
   REWRITE_TAC [ADD1] THEN
   UNDISCH_THEN
     `bits_to_num (bsignal mb (t + l + l + 1)) + m = 2 EXP width mb + 1`
     (SUBST1_TAC o SYM) THEN
   ASM_REWRITE_TAC [LE_ADD_LCANCEL; LE_0];
   ALL_TAC] THEN
  UNDISCH_TAC
    `bits_to_num (bsignal mb (t + l + l + 1)) + m = 2 EXP width mb + 1` THEN
  MP_TAC (SPEC `m : num` num_CASES) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `ms : num` SUBST_VAR_TAC) THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [ADD_SUC] THEN
  REWRITE_TAC [ADD1; EQ_ADD_RCANCEL] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i : cycle. t + l + i = (t + i + 1) + (d3 + d4)`
    (fun th -> REWRITE_TAC [th]) THENL
  [GEN_TAC THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`sad : wire`;
        `sbd : wire`;
        `dn : wire`]
       nor2_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  MP_TAC
    (SPECL
       [`ps : bus`;
        `ys : bus`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  MP_TAC
    (SPECL
       [`pc : bus`;
        `yc : bus`]
       bconnect_bsignal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  MP_TAC
    (SPECL
       [`sa : wire`;
        `d3 + d4 : cycle`;
        `sad : wire`]
       pipe_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  MP_TAC
    (SPECL
       [`sb : wire`;
        `d3 + d4 : cycle`;
        `sbd : wire`]
       pipe_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  UNDISCH_TAC `!i. i <= d + j ==> (signal ld (t + i) <=> i <= l)` THEN
  SPEC_TAC (`j : cycle`, `j : cycle`) THEN
  REVERSE_TAC INDUCT_TAC THENL
  [STRIP_TAC THEN
   FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC i` THEN
    ASM_REWRITE_TAC [ADD_SUC; SUC_LE; LE_SUC];
    ALL_TAC] THEN
   STRIP_TAC THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [ADD_SUC; LE] THEN
    REVERSE_TAC STRIP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [GSYM ADD_SUC; LE_ADD] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    MP_TAC
      (SPECL
         [`sar : wire`;
          `sa : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sbr : wire`;
          `sb : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `saq : wire`;
          `sar : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `sbq : wire`;
          `sbr : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    UNDISCH_THEN
      `!i. i <= d + SUC j ==> (signal ld (t + i) <=> i <= l)`
      (MP_TAC o SPEC `d + SUC j : cycle`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC [LE_REFL];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN `d + SUC j <= l <=> F` SUBST1_TAC THENL
    [UNDISCH_THEN
       `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL_0; ADD_EQ_0; NOT_SUC];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [] THEN
    MP_TAC
      (SPECL
         [`san : wire`;
          `sap : wire`;
          `saq : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jp : wire`;
          `sap : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jpn : wire`;
          `sbp : wire`;
          `sbq : wire`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `mdn : wire`;
          `sbp : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `d + j : cycle`) THEN
    ASM_REWRITE_TAC [LE_REFL; LE_ADD; ADD1; GSYM ADD_ASSOC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_SUC; SUC_ADD] THEN
   REWRITE_TAC [ADD1] THEN
   MP_TAC
     (SPECL
        [`psr : bus`;
         `ps : bus`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`pcr : bus`;
         `pc : bus`]
        bdelay_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sad : wire`;
         `psq : bus`;
         `ps : bus`;
         `psr : bus`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sad : wire`;
         `pcq : bus`;
         `pc : bus`;
         `pcr : bus`]
        bcase1_bsignal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sa : wire`;
         `d3 + d4 : cycle`;
         `sad : wire`]
        pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sb : wire`;
         `d3 + d4 : cycle`;
         `sbd : wire`]
        pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `d + j : cycle`) THEN
   ASM_REWRITE_TAC [LE_REFL; LE_ADD] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  REWRITE_TAC [ADD_0] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= l ==> signal sa (t + i + 1) /\ signal sb (t + i + 1)`
    STRIP_ASSUME_TAC THENL
  [GEN_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MP_TAC
     (SPECL
        [`sar : wire`;
         `sa : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sbr : wire`;
         `sb : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `saq : wire`;
         `sar : wire`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `sbq : wire`;
         `sbr : wire`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `l : cycle` THEN
    UNDISCH_THEN
      `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
      (SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC [LE_ADD];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC
    (SPECL
       [`ms : num`;
        `srdd : wire`;
        `mb : bus`;
        `sadd : wire`;
        `md : wire`;
        `t + l + l + 1 : cycle`]
       event_counter_signal) THEN
  ASM_REWRITE_TAC [] THEN
  MP_TAC
    (SPECL
       [`sadd : wire`;
        `sbdd : wire`;
        `srdd : wire`]
       and2_signal) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  SUBGOAL_THEN
    `!i. signal sadd ((t + l + l + 1) + i) = signal sa (t + l + 1 + i)`
    (fun th -> REWRITE_TAC [th]) THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(t + l + l + 1) + i = ((t + l + 1 + i) + (d3 + d4)) + 1`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sad : wire`;
         `sadd : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sa : wire`;
         `d3 + d4 : cycle`;
         `sad : wire`]
        pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]);
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. signal sbdd ((t + l + l + 1) + i) = signal sb (t + l + 1 + i)`
    (fun th -> REWRITE_TAC [th]) THENL
  [GEN_TAC THEN
   SUBGOAL_THEN
     `(t + l + l + 1) + i = ((t + l + 1 + i) + (d3 + d4)) + 1`
     SUBST1_TAC THENL
   [ASM_REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   MP_TAC
     (SPECL
        [`sbd : wire`;
         `sbdd : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sb : wire`;
         `d3 + d4 : cycle`;
         `sbd : wire`]
        pipe_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]);
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!k.
       (!i.
          i <= k ==>
          (signal sa (t + l + 1 + i) /\ signal sb (t + l + 1 + i) <=>
           i = 0)) <=>
       (!i.
          ~(i = 0) /\ i <= k ==>
          ~signal sa (t + l + 1 + i) \/ ~signal sb (t + l + 1 + i))`
    (fun th -> REWRITE_TAC [th]) THENL
  [X_GEN_TAC `ki : cycle` THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `i : cycle`) THEN
    ASM_REWRITE_TAC [DE_MORGAN_THM];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REVERSE_TAC (ASM_CASES_TAC `i = 0`) THENL
   [ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [ADD_0] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!mi.
       mi <= ms ==>
       (!i.
          i < d0 + d1 + d2 + d4 + r + 3 ==>
          (~signal sa (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + i + 1) /\
           signal sb (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + i + 1)) /\
          (signal jp (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + i + 1) <=>
           i = d0 + d1 + d2 + d4 + r + 2)) /\
       signal sa (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi) /\
       ~signal sb (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi) /\
       (bits_to_num (bsignal ps (((t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi) + d3 + d4) + 1)) +
       2 * bits_to_num (bsignal pc (((t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi) + d3 + d4) + 1))) MOD n =
       (x EXP (2 EXP SUC mi) * 2 EXP (r + 2)) MOD n /\
       CARD {i | 0 < i /\
                 i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC mi /\
                 signal sa (t + l + 1 + i)} = mi`
    ASSUME_TAC THENL
  [MATCH_MP_TAC num_WF THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   SUBGOAL_THEN
     `signal sa (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi)`
     ASSUME_TAC THENL
   [ASM_CASES_TAC `mi = 0` THENL
    [UNDISCH_THEN
       `!i. i <= l ==> signal sa (t + i + 1) /\ signal sb (t + i + 1)`
       (MP_TAC o SPEC `l : cycle`) THEN
     ASM_REWRITE_TAC [LE_REFL; MULT_0; ADD_0] THEN
     STRIP_TAC;
     ALL_TAC] THEN
    MP_TAC (SPEC `mi : cycle` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `mis : cycle` SUBST_VAR_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `mis : cycle`) THEN
    REWRITE_TAC [SUC_LT] THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `SUC mis` THEN
     ASM_REWRITE_TAC [SUC_LE];
     ALL_TAC] THEN
    STRIP_TAC;
    ALL_TAC] THEN
   MATCH_MP_TAC (TAUT `!x y. x /\ (x ==> y) ==> x /\ y`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC num_WF THEN
    GEN_TAC THEN
    STRIP_TAC THEN
    STRIP_TAC THEN
    REVERSE_TAC CONJ_TAC THENL
    [ASM_CASES_TAC `d3 + d4 <= (i : cycle)` THENL
     [POP_ASSUM
        (X_CHOOSE_THEN `id : cycle` SUBST_VAR_TAC o
         REWRITE_RULE [LE_EXISTS]) THEN
      MP_TAC
        (SPECL
           [`r : num`; `sadd : wire`; `ps : bus`; `pc : bus`; `d0 : cycle`;
            `ps : bus`; `pc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
            `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
            `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `jp : wire`;
            `qs : bus`; `qc : bus`;
            `((t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi) + d3 + d4) + 1`;
            `id : cycle`]
           montgomery_mult_signal) THEN
      REVERSE_TAC ANTS_TAC THENL
      [REWRITE_TAC [GSYM ADD_ASSOC] THEN
       MP_TAC (SPECL [`1`; `id : cycle`] ADD_SYM) THEN
       DISCH_THEN SUBST1_TAC THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC (SPECL [`d4 : cycle`; `id : cycle`] ADD_SYM) THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC (SPECL [`d4 : cycle`; `r + 2`] ADD_SYM) THEN
       DISCH_THEN SUBST1_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL];
       ALL_TAC] THEN
      CONJ_TAC THENL
      [UNDISCH_THEN `width xs = r` (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC [];
       ALL_TAC] THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL
      [X_GEN_TAC `ix : cycle` THEN
       STRIP_TAC THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       SUBGOAL_THEN `d3 + d4 + 1 + ix = ix + d3 + d4 + 1` SUBST1_TAC THENL
       [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
        REWRITE_TAC [ADD_ASSOC];
        ALL_TAC] THEN
       REWRITE_TAC [ADD_ASSOC] THEN
       MP_TAC
         (SPECL
            [`sad : wire`;
             `sadd : wire`]
            delay_signal) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
       ONCE_REWRITE_TAC [GSYM ADD_ASSOC] THEN
       MP_TAC
         (SPECL
            [`sa : wire`;
             `d3 + d4 : cycle`;
             `sad : wire`]
            pipe_signal) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
       ASM_CASES_TAC `ix = 0` THENL
       [ASM_REWRITE_TAC [GSYM ADD_ASSOC; ADD_0];
        ALL_TAC] THEN
       MP_TAC (SPEC `ix : cycle` num_CASES) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (X_CHOOSE_THEN `iy : cycle` SUBST_VAR_TAC) THEN
       POP_ASSUM (K ALL_TAC) THEN
       FIRST_X_ASSUM (MP_TAC o SPEC `iy : cycle`) THEN
       SUBGOAL_THEN `iy < (d3 + d4) + (id : cycle)` ASSUME_TAC THENL
       [MATCH_MP_TAC LTE_TRANS THEN
        EXISTS_TAC `id : cycle` THEN
        ASM_REWRITE_TAC [GSYM LE_SUC_LT; LE_ADDR];
        ALL_TAC] THEN
       ASM_REWRITE_TAC [] THEN
       ANTS_TAC THENL
       [MATCH_MP_TAC LT_TRANS THEN
        EXISTS_TAC `(d3 + d4) + id : cycle` THEN
        ASM_REWRITE_TAC [];
        ALL_TAC] THEN
       STRIP_TAC THEN
       ASM_REWRITE_TAC [GSYM ADD_ASSOC; ADD1];
       ALL_TAC] THEN
      REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      UNDISCH_THEN
        `d3 + d4 + 1 = l`
        (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD_ASSOC; LT_ADD_RCANCEL] THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LT_ADD_LCANCEL] THEN
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * SUC mi` THEN
      CONJ_TAC THENL
      [REWRITE_TAC
         [MULT_SUC; LT_ADDR; LT_NZ; ADD_EQ_0;
          SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC];
       ASM_REWRITE_TAC [LE_MULT_LCANCEL; LE_SUC]];
      ALL_TAC] THEN
     POP_ASSUM (ASSUME_TAC o REWRITE_RULE [NOT_LE]) THEN
     SUBGOAL_THEN
       `i = d0 + d1 + d2 + d4 + r + 2 <=> F`
       SUBST1_TAC THENL
     [REWRITE_TAC [] THEN
      MATCH_MP_TAC LT_IMP_NEQ THEN
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `d3 + d4 : cycle` THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + r + 1) + d4 : cycle` THEN
      ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
      REWRITE_TAC
        [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 1`)] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; LE_ADD];
      ALL_TAC] THEN
     REWRITE_TAC [] THEN
     ASM_CASES_TAC `mi = 0` THENL
     [POP_ASSUM SUBST_VAR_TAC THEN
      REWRITE_TAC [MULT_0; ZERO_ADD] THEN
      MATCH_MP_TAC
        (SPECL
           [`sadd : wire`; `ps : bus`; `pc : bus`; `d0 : cycle`;
            `ps : bus`; `pc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
            `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
            `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `jp : wire`;
            `qs : bus`; `qc : bus`]
           montgomery_mult_signal_load) THEN
      ASM_REWRITE_TAC [] THEN
      SUBGOAL_THEN
        `t + l + 1 + i + 1 = ((t + (i + 1) + 1) + (d3 + d4)) + 1`
        SUBST1_TAC THENL
      [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
       CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       MATCH_ACCEPT_TAC ADD_SYM;
       ALL_TAC] THEN
      MP_TAC
        (SPECL
           [`sad : wire`;
            `sadd : wire`]
           delay_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      MP_TAC
        (SPECL
           [`sa : wire`;
            `d3 + d4 : cycle`;
            `sad : wire`]
           pipe_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      UNDISCH_THEN
        `!i. i <= l ==> signal sa (t + i + 1) /\ signal sb (t + i + 1)`
        (MP_TAC o SPEC `i + 1`) THEN
      ANTS_TAC THENL
      [REWRITE_TAC [GSYM ADD1; LE_SUC_LT] THEN
       MATCH_MP_TAC LTE_TRANS THEN
       EXISTS_TAC `d3 + d4 : cycle` THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       ASM_REWRITE_TAC [ADD_ASSOC; LE_ADD];
       ALL_TAC] THEN
      STRIP_TAC;
      ALL_TAC] THEN
     MP_TAC (SPEC `mi : cycle` num_CASES) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN `mis : cycle` SUBST_VAR_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC; GSYM ADD_ASSOC] THEN
     SUBGOAL_THEN
       `d3 + d4 + 1 <= d0 + d1 + d2 + d4 + r + 4 + i + 1`
       (X_CHOOSE_THEN `id : cycle` ASSUME_TAC o
        REWRITE_RULE [LE_EXISTS]) THENL
     [REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + r + 1) + d4` THEN
      ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
      REWRITE_TAC
        [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 3`);
         LE_ADD];
      ALL_TAC] THEN
     MP_TAC
       (SPECL
          [`r : num`; `sadd : wire`; `ps : bus`; `pc : bus`; `d0 : cycle`;
           `ps : bus`; `pc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
           `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
           `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `jp : wire`;
           `qs : bus`; `qc : bus`;
           `((t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mis) + d3 + d4) + 1`;
           `id : cycle`]
          montgomery_mult_signal) THEN
     REVERSE_TAC ANTS_TAC THENL
     [ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
      DISCH_THEN SUBST1_TAC THEN
      ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
      MATCH_MP_TAC LT_IMP_NEQ THEN
      CONV_TAC (REWR_CONV (GSYM (SPEC `d4 + 1` LT_ADD_RCANCEL))) THEN
      SUBGOAL_THEN
        `(d3 + id) + d4 + 1 = (d3 + d4 + 1) + id`
        SUBST1_TAC THENL
      [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
       CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
       REWRITE_TAC [ADD_ASSOC];
       ALL_TAC] THEN
      POP_ASSUM (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD_ASSOC; LT_ADD_RCANCEL] THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LT_ADD_LCANCEL] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC
        [ADD_ASSOC; LT_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `2 + 2`)] THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LT_ADD_LCANCEL; LT_ADD; LT_NZ] THEN
      REWRITE_TAC [ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 1`); NOT_SUC];
      ALL_TAC] THEN
     CONJ_TAC THENL
     [UNDISCH_THEN `width xs = r` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     CONJ_TAC THENL
     [X_GEN_TAC `ix : cycle` THEN
      STRIP_TAC THEN
      REWRITE_TAC [GSYM ADD_ASSOC] THEN
      SUBGOAL_THEN `d3 + d4 + 1 + ix = ix + d3 + d4 + 1` SUBST1_TAC THENL
      [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       REWRITE_TAC [ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      MP_TAC
        (SPECL
           [`sad : wire`;
            `sadd : wire`]
           delay_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      ONCE_REWRITE_TAC [GSYM ADD_ASSOC] THEN
      MP_TAC
        (SPECL
           [`sa : wire`;
            `d3 + d4 : cycle`;
            `sad : wire`]
           pipe_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      ASM_CASES_TAC `ix = 0` THENL
      [ASM_REWRITE_TAC [GSYM ADD_ASSOC; ADD_0] THEN
       ASM_CASES_TAC `mis = 0` THENL
       [ASM_REWRITE_TAC [MULT_0; ADD_0] THEN
        UNDISCH_THEN
          `!i. i <= l ==> signal sa (t + i + 1) /\ signal sb (t + i + 1)`
          (MP_TAC o SPEC `l : cycle`) THEN
        REWRITE_TAC [LE_REFL] THEN
        STRIP_TAC;
        ALL_TAC] THEN
       MP_TAC (SPEC `mis : cycle` num_CASES) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (X_CHOOSE_THEN `miss : cycle` SUBST_VAR_TAC) THEN
       POP_ASSUM (K ALL_TAC) THEN
       FIRST_X_ASSUM
         (fun th ->
            MP_TAC (SPEC `miss : cycle` th) THEN
            ANTS_TAC THENL
            [MATCH_MP_TAC LT_TRANS THEN
             EXISTS_TAC `SUC miss` THEN
             CONJ_TAC THEN
             MATCH_ACCEPT_TAC SUC_LT;
             ALL_TAC]) THEN
       REVERSE_TAC ANTS_TAC THENL
       [STRIP_TAC;
        ALL_TAC] THEN
       MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `SUC (SUC miss)` THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `SUC miss` THEN
       CONJ_TAC THEN
       MATCH_ACCEPT_TAC SUC_LE;
       ALL_TAC] THEN
      MP_TAC (SPEC `ix : cycle` num_CASES) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `iy : cycle` SUBST_VAR_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      FIRST_X_ASSUM
        (fun th ->
           MP_TAC (SPEC `mis : cycle` th) THEN
           ANTS_TAC THENL
           [MATCH_ACCEPT_TAC SUC_LT;
            ALL_TAC]) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `SUC mis` THEN
       ASM_REWRITE_TAC [SUC_LE];
       ALL_TAC] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `iy : cycle`) THEN
      REVERSE_TAC ANTS_TAC THENL
      [STRIP_TAC THEN
       ASM_REWRITE_TAC [GSYM ADD_ASSOC; ADD1];
       ALL_TAC] THEN
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `id : cycle` THEN
      ASM_REWRITE_TAC [GSYM LE_SUC_LT] THEN
      CONV_TAC (REWR_CONV (GSYM (SPEC `d3 + d4 + 1` LE_ADD_LCANCEL))) THEN
      FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV o SYM) THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_ASSOC; NUM_REDUCE_CONV `1 + 3`] THEN
      REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
      ASM_REWRITE_TAC [GSYM ADD1; LE_SUC_LT];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [ADD_ASSOC] THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC] THEN
     UNDISCH_THEN
       `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; LT_ADD_LCANCEL] THEN
     REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     MATCH_MP_TAC LET_TRANS THEN
     EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * ms` THEN
     CONJ_TAC THENL
     [REWRITE_TAC [LE_MULT_LCANCEL] THEN
      DISJ2_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `SUC mis` THEN
      ASM_REWRITE_TAC [SUC_LE];
      REWRITE_TAC
        [LT_ADD; LT_NZ; ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC]];
     ALL_TAC] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    MP_TAC
      (SPECL
         [`sar : wire`;
          `sa : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sbr : wire`;
          `sb : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `saq : wire`;
          `sar : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `sbq : wire`;
          `sbr : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    UNDISCH_THEN
      `!i. i <= d ==> (signal ld (t + i) <=> i <= l)`
      (MP_TAC o SPEC `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + i`) THEN
    ANTS_TAC THENL
    [UNDISCH_THEN
       `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [LE_ADD_LCANCEL] THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * ms + i` THEN
     ASM_REWRITE_TAC [LE_ADD_RCANCEL; LE_MULT_LCANCEL] THEN
     REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     REWRITE_TAC [LE_ADD_LCANCEL] THEN
     MATCH_MP_TAC LT_IMP_LE THEN
     MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `d0 + d1 + d2 + d4 + r + 3` THEN
     ASM_REWRITE_TAC [LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `SUC 3`); SUC_LE];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + i <= l <=> F`
      SUBST1_TAC THENL
    [REWRITE_TAC [NOT_LE; LT_ADD; LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [] THEN
    MP_TAC
      (SPECL
         [`san : wire`;
          `sap : wire`;
          `saq : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jp : wire`;
          `sap : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jpn : wire`;
          `sbp : wire`;
          `sbq : wire`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `mdn : wire`;
          `sbp : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `san : wire`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`jp : wire`;
          `jpn : wire`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`md : wire`;
          `mdn : wire`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    REVERSE_TAC (ASM_CASES_TAC `i = 0`) THENL
    [MP_TAC (SPEC `i : cycle` num_CASES) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN `is : cycle` SUBST_VAR_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `is : cycle`) THEN
     REWRITE_TAC [SUC_LT] THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC LT_TRANS THEN
      EXISTS_TAC `SUC is` THEN
      ASM_REWRITE_TAC [SUC_LT];
      ALL_TAC] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [ADD1] THEN
     MATCH_MP_TAC LT_IMP_NEQ THEN
     CONV_TAC (REWR_CONV (GSYM LT_SUC)) THEN
     ASM_REWRITE_TAC [GSYM ADD_SUC; NUM_REDUCE_CONV `SUC 2`];
     ALL_TAC] THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    ASM_REWRITE_TAC [ADD_0] THEN
    ASM_CASES_TAC `mi = 0` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     FIRST_ASSUM (MP_TAC o SPEC `l : cycle`) THEN
     REWRITE_TAC [LE_REFL; MULT_0; ADD_0] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC
       (SPECL
          [`sadd : wire`; `ps : bus`; `pc : bus`; `d0 : cycle`;
           `ps : bus`; `pc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
           `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
           `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `jp : wire`;
           `qs : bus`; `qc : bus`]
          montgomery_mult_signal_load) THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN
       `t + l + 1 = ((t + 1) + (d3 + d4)) + 1`
       SUBST1_TAC THENL
     [REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
      UNDISCH_THEN
        `d3 + d4 + 1 = l`
        (SUBST1_TAC o SYM) THEN
      REWRITE_TAC [ADD_ASSOC];
      ALL_TAC] THEN
     MP_TAC
       (SPECL
          [`sad : wire`;
           `sadd : wire`]
          delay_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sa : wire`;
           `d3 + d4 : cycle`;
           `sad : wire`]
          pipe_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
     REWRITE_TAC [LE_0; ZERO_ADD] THEN
     STRIP_TAC;
     ALL_TAC] THEN
    MP_TAC (SPEC `mi : cycle` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `mis : cycle` SUBST_VAR_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    FIRST_ASSUM (MP_TAC o SPEC `mis : cycle`) THEN
    REWRITE_TAC [SUC_LT] THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `SUC mis` THEN
     ASM_REWRITE_TAC [SUC_LE];
     ALL_TAC] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `l <= d0 + d1 + d2 + d4 + r + 4`
      (X_CHOOSE_THEN `dl : cycle` ASSUME_TAC o
       REWRITE_RULE [LE_EXISTS]) THENL
    [UNDISCH_THEN
       `d3 + d4 + 1 = l`
       (SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `(d0 + d1 + d2 + r + 1) + d4 + 1` THEN
     ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
     REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `3 + 1`)] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
     CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `2 + 1`)] THEN
     REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    FIRST_X_ASSUM
      (fun th ->
         MP_TAC (SPEC `dl + (l + dl) * mis : cycle` th) THEN
         ANTS_TAC THENL
         [GEN_TAC;
          ALL_TAC]) THENL
    [STRIP_TAC THEN
     SUBGOAL_THEN `i <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis` MP_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `dl + (l + dl) * mis : cycle` THEN
      ASM_REWRITE_TAC [MULT_SUC; LE_ADD_RCANCEL; LE_ADDR];
      ALL_TAC] THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN
     MP_TAC
       (SPECL
          [`i : cycle`; `d0 + d1 + d2 + d4 + r + 4`]
          (ONCE_REWRITE_RULE [MULT_SYM] DIVISION)) THEN
     ANTS_TAC THENL
     [REWRITE_TAC [ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC];
      ALL_TAC] THEN
     DISCH_THEN
       (CONJUNCTS_THEN2
          (fun th -> ONCE_REWRITE_TAC [th])
          MP_TAC) THEN
     SPEC_TAC (`i DIV (d0 + d1 + d2 + d4 + r + 4)`, `iq : num`) THEN
     GEN_TAC THEN
     SPEC_TAC (`i MOD (d0 + d1 + d2 + d4 + r + 4)`, `ir : num`) THEN
     GEN_TAC THEN
     STRIP_TAC THEN
     STRIP_TAC THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `iq <= SUC mis` MP_TAC THENL
     [MP_TAC (SPEC `d0 + d1 + d2 + d4 + r + 4` LE_MULT_LCANCEL) THEN
      REWRITE_TAC [ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC] THEN
      REWRITE_TAC [NUM_REDUCE_CONV `SUC 3`] THEN
      DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * iq + ir` THEN
      ASM_REWRITE_TAC [LE_ADD];
      ALL_TAC] THEN
     REWRITE_TAC [LE] THEN
     STRIP_TAC THENL
     [POP_ASSUM SUBST_VAR_TAC THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [LE_ADD_LCANCEL_0] THEN
      DISCH_THEN SUBST_VAR_TAC THEN
      ASM_REWRITE_TAC [ADD_0];
      ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     ASM_CASES_TAC `ir = 0` THENL
     [POP_ASSUM SUBST_VAR_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [ADD_0; MULT_EQ_0] THEN
      REWRITE_TAC [ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC] THEN
      REWRITE_TAC [NUM_REDUCE_CONV `SUC 3`] THEN
      STRIP_TAC THEN
      MP_TAC (SPEC `iq : num` num_CASES) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `iqs : num` SUBST_VAR_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [LE_SUC_LT] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM
        (fun th ->
           MP_TAC (SPEC `iqs : num` th) THEN
           ANTS_TAC THENL
           [MATCH_MP_TAC LT_TRANS THEN
            EXISTS_TAC `SUC iqs` THEN
            ASM_REWRITE_TAC [LT_SUC; SUC_LT] THEN
            NO_TAC;
            ALL_TAC]) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `SUC mis` THEN
       ASM_REWRITE_TAC [] THEN
       MATCH_MP_TAC LT_IMP_LE THEN
       MATCH_MP_TAC LT_TRANS THEN
       EXISTS_TAC `mis : num` THEN
       ASM_REWRITE_TAC [SUC_LT];
       ALL_TAC] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN (K ALL_TAC) THEN
     MP_TAC (SPEC `ir : num` num_CASES) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (X_CHOOSE_THEN `irs : num` SUBST_VAR_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [ADD1] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM
       (fun th ->
          MP_TAC (SPEC `iq : num` th) THEN
          ANTS_TAC THENL
          [ASM_REWRITE_TAC [LT_SUC_LE] THEN
           NO_TAC;
           ALL_TAC]) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `mis : num` THEN
      ASM_REWRITE_TAC [] THEN
      MATCH_MP_TAC LT_IMP_LE THEN
      ASM_REWRITE_TAC [GSYM LE_SUC_LT];
      ALL_TAC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `irs : num`) THEN
     ANTS_TAC THENL
     [CONV_TAC (REWR_CONV (GSYM LT_SUC)) THEN
      ASM_REWRITE_TAC [GSYM ADD_SUC; NUM_REDUCE_CONV `SUC 3`];
      ALL_TAC] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN
      `1 + (l + dl) * SUC mis =
       l + 1 + dl + (l + dl) * mis`
      SUBST1_TAC THENL
    [REWRITE_TAC [MULT_SUC; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
     MATCH_ACCEPT_TAC ADD_SYM;
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
      `!i.
         i + width mb <= dl + (l + dl) * mis <=>
         i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis`
      (fun th -> REWRITE_TAC [th]) THENL
    [GEN_TAC THEN
     CONV_TAC
       (LAND_CONV (REWR_CONV (GSYM (SPEC `l : cycle` LE_ADD_RCANCEL)))) THEN
     REWRITE_TAC [ADD_ASSOC] THEN
     AP_TERM_TAC THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; MULT_SUC];
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC [NOT_LE; GSYM LE_SUC_LT];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC (TAUT `!x y z. (x /\ y) /\ (x /\ y ==> z) ==> x /\ y /\ z`) THEN
   CONJ_TAC THENL
   [SUBGOAL_THEN
      `t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi =
       (t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi +
        (d0 + d1 + d2 + d4 + r + 3)) + 1`
      SUBST1_TAC THENL
    [REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `3 + 1`];
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`sar : wire`;
          `sa : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sbr : wire`;
          `sb : wire`]
         delay_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `saq : wire`;
          `sar : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`ld : wire`;
          `sbq : wire`;
          `sbr : wire`]
         or2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    UNDISCH_THEN
      `!i. i <= d ==> (signal ld (t + i) <=> i <= l)`
      (MP_TAC o
       SPEC
         `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi +
          d0 + d1 + d2 + d4 + r + 3`) THEN
    ANTS_TAC THENL
    [UNDISCH_THEN
       `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [LE_ADD_LCANCEL] THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * SUC mi` THEN
     ASM_REWRITE_TAC [LE_SUC; LE_MULT_LCANCEL] THEN
     REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     REWRITE_TAC [LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `SUC 3`); SUC_LE];
     ALL_TAC] THEN
    SUBGOAL_THEN
      `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi +
       d0 + d1 + d2 + d4 + r + 3 <= l <=> F`
      SUBST1_TAC THENL
    [REWRITE_TAC [NOT_LE; LT_ADD; LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [] THEN
    MP_TAC
      (SPECL
         [`san : wire`;
          `sap : wire`;
          `saq : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jp : wire`;
          `sap : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `jpn : wire`;
          `sbp : wire`;
          `sbq : wire`]
         case1_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `mdn : wire`;
          `sbp : wire`]
         and2_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `san : wire`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`jp : wire`;
          `jpn : wire`]
         not_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `d0 + d1 + d2 + d4 + r + 2`) THEN
    ANTS_TAC THENL
    [REWRITE_TAC [SYM (NUM_REDUCE_CONV `SUC 2`); ADD_SUC; SUC_LT];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `2 + 1`] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   STRIP_TAC THEN
   CONJ_TAC THENL
   [MP_TAC
      (SPECL
         [`psr : bus`;
          `ps : bus`]
         bdelay_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`pcr : bus`;
          `pc : bus`]
         bdelay_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sad : wire`;
          `psq : bus`;
          `ps : bus`;
          `psr : bus`]
         bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sbd : wire`;
          `xs : bus`;
          `qs : bus`;
          `psq : bus`]
         bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sad : wire`;
          `pcq : bus`;
          `pc : bus`;
          `pcr : bus`]
         bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sbd : wire`;
          `xc : bus`;
          `qc : bus`;
          `pcq : bus`]
         bcase1_bsignal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sa : wire`;
          `d3 + d4 : cycle`;
          `sad : wire`]
         pipe_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC
      (SPECL
         [`sb : wire`;
          `d3 + d4 : cycle`;
          `sbd : wire`]
         pipe_signal) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN
      `?xi.
         bits_to_num (bsignal ps (((t + l + 1 +
           (d0 + d1 + d2 + d4 + r + 4) * mi) + d3 + d4) + 1)) +
         2 * bits_to_num (bsignal pc (((t + l + 1 +
               (d0 + d1 + d2 + d4 + r + 4) * mi) + d3 + d4) + 1)) = xi`
      STRIP_ASSUME_TAC THENL
    [MATCH_ACCEPT_TAC EXISTS_REFL';
     ALL_TAC] THEN
    MP_TAC
      (SPECL
         [`n : num`; `r : num`; `s : num`; `k : num`; `xi : num`; `xi : num`;
          `sadd : wire`; `ps : bus`; `pc : bus`; `d0 : cycle`;
          `ps : bus`; `pc : bus`; `d1 : cycle`; `ks : bus`; `kc : bus`;
          `d2 : cycle`; `ns : bus`; `nc : bus`; `jb : bus`; `d3 : cycle`;
          `d4 : cycle`; `rx : bus`; `ry : bus`; `rz : bus`; `jp : wire`;
          `qs : bus`; `qc : bus`;
          `((t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi) + d3 + d4) + 1`]
         montgomery_mult_bits_to_num) THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [UNDISCH_THEN `width xs = r` (SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [CONJ_ASSOC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `!x.
           1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 + x =
           l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + x`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [GEN_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      REWRITE_TAC
        [GSYM LE_SUC_LT; GSYM ADD_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
      REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
      ASM_REWRITE_TAC
        [ADD_ASSOC; LE_ADD_RCANCEL; LE_MULT_LCANCEL; ADD_EQ_0; NOT_SUC];
      ALL_TAC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `!x.
           1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 + x =
           l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + x`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [GEN_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      REWRITE_TAC
        [GSYM LE_SUC_LT; GSYM ADD_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
      REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
      ASM_REWRITE_TAC
        [ADD_ASSOC; LE_ADD_RCANCEL; LE_MULT_LCANCEL; ADD_EQ_0; NOT_SUC];
      ALL_TAC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `!x.
           1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 + x =
           l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + x`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [GEN_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      REWRITE_TAC
        [GSYM LE_SUC_LT; GSYM ADD_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
      REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
      ASM_REWRITE_TAC
        [ADD_ASSOC; LE_ADD_RCANCEL; LE_MULT_LCANCEL; ADD_EQ_0; NOT_SUC];
      ALL_TAC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 =
         l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * ms` THEN
      ASM_REWRITE_TAC [LE_MULT_LCANCEL; MULT_SUC; LT_ADDR] THEN
      REWRITE_TAC [LT_NZ; SYM (NUM_REDUCE_CONV `SUC 3`); ADD_EQ_0; NOT_SUC];
      ALL_TAC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `!x.
           1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 + x =
           l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + x`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [GEN_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * ms + i` THEN
      ASM_REWRITE_TAC [LE_ADD_RCANCEL; LE_MULT_LCANCEL] THEN
      REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC; LT_ADD_LCANCEL] THEN
      REWRITE_TAC [LT_SUC_LE; ADD_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `d0 + d1 + d2 + r + 1` THEN
      ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC
        [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 2`);
         LE_ADD];
      ALL_TAC] THEN
     REVERSE_TAC CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC [GSYM ADD_ASSOC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_THEN
        `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
        (SUBST1_TAC o SYM) THEN
      SUBGOAL_THEN
        `!x.
           1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 + x =
           l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + x`
        (CONV_TAC o LAND_CONV o REWR_CONV) THENL
      [GEN_TAC THEN
       REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
       REWRITE_TAC [GSYM ADD_ASSOC] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       UNDISCH_THEN
         `d3 + d4 + 1 = l`
         (SUBST1_TAC o SYM) THEN
       REWRITE_TAC [GSYM ADD_ASSOC];
       ALL_TAC] THEN
      REWRITE_TAC [LT_ADD_LCANCEL] THEN
      MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * ms + i` THEN
      ASM_REWRITE_TAC [LE_ADD_RCANCEL; LE_MULT_LCANCEL] THEN
      REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC; LT_ADD_LCANCEL] THEN
      REWRITE_TAC [LT_SUC_LE; ADD_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `d0 + d1 + r + 1` THEN
      ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_ASSOC)) THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC
        [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 2`);
         LE_ADD];
      ALL_TAC] THEN
     REWRITE_TAC [GSYM CONJ_ASSOC] THEN
     CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN
      REWRITE_TAC [ADD_ASSOC] THEN
      SUBGOAL_THEN
        `!x. (((x + d3) + d4) + 1) + i = ((x + i) + (d3 + d4)) + 1`
        (fun th -> ONCE_REWRITE_TAC [th]) THENL
      [GEN_TAC THEN
       REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
       CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
       REWRITE_TAC [ADD_ASSOC];
       ALL_TAC] THEN
      MP_TAC
        (SPECL
           [`sad : wire`;
            `sadd : wire`]
           delay_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      MP_TAC
        (SPECL
           [`sa : wire`;
            `d3 + d4 : cycle`;
            `sad : wire`]
           pipe_signal) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [GSYM ADD_ASSOC] THEN
      ASM_CASES_TAC `i = 0` THENL
      [ASM_REWRITE_TAC [ADD_0];
       ALL_TAC] THEN
      MP_TAC (SPEC `i : num` num_CASES) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `is : num`) THEN
      ANTS_TAC THENL
      [REWRITE_TAC [GSYM LE_SUC_LT] THEN
       MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `d0 + d1 + d2 + d4 + r + 2` THEN
       ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
       REWRITE_TAC [SYM (NUM_REDUCE_CONV `SUC 2`); SUC_LE];
       ALL_TAC] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [ADD1];
      ALL_TAC] THEN
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [ADD_ASSOC] THEN
     SUBGOAL_THEN
       `!x. (((x + d3) + d4) + 1) + i = ((x + i) + (d3 + d4)) + 1`
       (fun th -> ONCE_REWRITE_TAC [th]) THENL
     [GEN_TAC THEN
      REWRITE_TAC [GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_ASSOC];
      ALL_TAC] THEN
     POP_ASSUM MP_TAC THEN
     POP_ASSUM (K ALL_TAC) THEN
     SPEC_TAC (`i : num`, `i : num`) THEN
     INDUCT_TAC THENL
     [DISCH_THEN (K ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN
      REWRITE_TAC [ZERO_ADD; GSYM ADD_ASSOC];
      ALL_TAC] THEN
     STRIP_TAC THEN
     MP_TAC
       (SPECL
          [`psr : bus`;
           `ps : bus`]
          bdelay_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`pcr : bus`;
           `pc : bus`]
          bdelay_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sad : wire`;
           `psq : bus`;
           `ps : bus`;
           `psr : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sbd : wire`;
           `xs : bus`;
           `qs : bus`;
           `psq : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sad : wire`;
           `pcq : bus`;
           `pc : bus`;
           `pcr : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sbd : wire`;
           `xc : bus`;
           `qc : bus`;
           `pcq : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sa : wire`;
           `d3 + d4 : cycle`;
           `sad : wire`]
          pipe_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sb : wire`;
           `d3 + d4 : cycle`;
           `sbd : wire`]
          pipe_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `i : num`) THEN
     ANTS_TAC THENL
     [REWRITE_TAC [GSYM LE_SUC_LT] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `d0 + r + 1` THEN
      ASM_REWRITE_TAC [LE_ADD_LCANCEL] THEN
      ONCE_REWRITE_TAC [ADD_ASSOC] THEN
      ONCE_REWRITE_TAC [ADD_ASSOC] THEN
      CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC
        [GSYM ADD_ASSOC; LE_ADD_LCANCEL; SYM (NUM_REDUCE_CONV `1 + 2`);
         LE_ADD];
      ALL_TAC] THEN
     REWRITE_TAC [GSYM ADD_ASSOC; ADD1] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `1 + d3 + d4 = d3 + d4 + 1` SUBST1_TAC THENL
     [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
      REWRITE_TAC [ADD_ASSOC];
      ALL_TAC] THEN
     FIRST_X_ASSUM (fun th -> MP_TAC th THEN ANTS_TAC) THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `SUC i` THEN
      ASM_REWRITE_TAC [SUC_LE];
      ALL_TAC] THEN
     REWRITE_TAC [ADD_ASSOC];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC] THEN
    SUBGOAL_THEN
      `t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * mi + d3 + d4 + 1 +
       d0 + d1 + d2 + d4 + r + 3 =
       t + l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC mi + d3 + d4`
      SUBST1_TAC THENL
    [REWRITE_TAC
       [EQ_ADD_LCANCEL; GSYM ADD_ASSOC;
        ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     ONCE_REWRITE_TAC [ADD_ASSOC] THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [EQ_ADD_RCANCEL; ADD_ASSOC] THEN
     REWRITE_TAC [GSYM ADD_ASSOC] THEN
     CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
     REWRITE_TAC [GSYM ADD_ASSOC; NUM_REDUCE_CONV `3 + 1`];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) THEN
    MP_TAC (SPEC `n : num` MOD_MULT_MOD2') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN
      (CONV_TAC o LAND_CONV o LAND_CONV o LAND_CONV o REWR_CONV o GSYM) THEN
    SUBGOAL_THEN
      `xi MOD n = (x EXP (2 EXP mi) * 2 EXP (r + 2)) MOD n`
      SUBST1_TAC THENL
    [POP_ASSUM (SUBST1_TAC o SYM) THEN
     REVERSE_TAC (ASM_CASES_TAC `mi = 0`) THENL
     [MP_TAC (SPEC `mi : num` num_CASES) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (X_CHOOSE_THEN `mis : num` SUBST_VAR_TAC) THEN
      POP_ASSUM (K ALL_TAC) THEN
      FIRST_X_ASSUM
        (fun th ->
           MP_TAC (SPEC `mis : num` th) THEN
           ANTS_TAC THENL
           [MATCH_ACCEPT_TAC SUC_LT;
            ALL_TAC]) THEN
      ANTS_TAC THENL
      [MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `SUC mis` THEN
       ASM_REWRITE_TAC [SUC_LE];
       ALL_TAC] THEN
      STRIP_TAC;
      ALL_TAC] THEN
     POP_ASSUM SUBST_VAR_TAC THEN
     REWRITE_TAC [MULT_0; ADD_0; EXP_0; EXP_1] THEN
     MP_TAC
       (SPECL
          [`psr : bus`;
           `ps : bus`]
          bdelay_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`pcr : bus`;
           `pc : bus`]
          bdelay_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sad : wire`;
           `psq : bus`;
           `ps : bus`;
           `psr : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sbd : wire`;
           `xs : bus`;
           `qs : bus`;
           `psq : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sad : wire`;
           `pcq : bus`;
           `pc : bus`;
           `pcr : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sbd : wire`;
           `xc : bus`;
           `qc : bus`;
           `pcq : bus`]
          bcase1_bsignal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sa : wire`;
           `d3 + d4 : cycle`;
           `sad : wire`]
          pipe_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     MP_TAC
       (SPECL
          [`sb : wire`;
           `d3 + d4 : cycle`;
           `sbd : wire`]
          pipe_signal) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
     UNDISCH_THEN
       `!i. i <= l ==> signal sa (t + i + 1) /\ signal sb (t + i + 1)`
       (MP_TAC o SPEC `l : cycle`) THEN
     REWRITE_TAC [LE_REFL] THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     REWRITE_TAC [GSYM ADD_ASSOC] THEN
     SUBGOAL_THEN `1 + d3 + d4 = l` SUBST1_TAC THENL
     [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
      ASM_REWRITE_TAC [GSYM ADD_ASSOC];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_MOD2') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    SUBGOAL_THEN
      `x EXP (2 EXP SUC mi) = x EXP (2 EXP mi) * x EXP (2 EXP mi)`
      SUBST1_TAC THENL
    [REWRITE_TAC [EXP_SUC; MULT_2; EXP_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    SUBGOAL_THEN
      `x EXP (2 EXP mi) * 2 EXP (r + 2) * x EXP (2 EXP mi) *
       2 EXP (r + 2) * s =
       (x EXP (2 EXP mi) * x EXP (2 EXP mi) * 2 EXP (r + 2)) *
       (2 EXP (r + 2) * s)`
      SUBST1_TAC THENL
    [REWRITE_TAC [MULT_ASSOC; EQ_MULT_RCANCEL] THEN
     REWRITE_TAC [GSYM MULT_ASSOC; EQ_MULT_LCANCEL] THEN
     DISJ1_TAC THEN
     DISJ1_TAC THEN
     DISJ2_TAC THEN
     MATCH_ACCEPT_TAC MULT_SYM;
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONV_TAC o LAND_CONV o REWR_CONV o GSYM) THEN
    MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
    MP_TAC (SPEC `n : num` (ONCE_REWRITE_RULE [MULT_SYM] MOD_MULT)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    REWRITE_TAC [ZERO_ADD] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    REWRITE_TAC [MULT_1];
    ALL_TAC] THEN
   ASM_CASES_TAC `mi = 0` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [SYM ONE; MULT_1] THEN
    SUBGOAL_THEN
      `!i.
         0 < i /\
         i + width mb + l <= d0 + d1 + d2 + d4 + r + 4 /\
         signal sa (t + l + 1 + i) <=> F`
      (fun th -> REWRITE_TAC [th; EMPTY_GSPEC; CARD_EMPTY]) THEN
    GEN_TAC THEN
    REWRITE_TAC [LT_NZ] THEN
    MATCH_MP_TAC (TAUT `!x y z. (x ==> y ==> ~z) ==> ~(x /\ y /\ z)`) THEN
    STRIP_TAC THEN
    MP_TAC (SPEC `i : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [SUC_ADD; ADD_SUC; LE_SUC; SYM (NUM_REDUCE_CONV `SUC 3`)] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `is : num`) THEN
    ANTS_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `is + width mb + l` THEN
     ASM_REWRITE_TAC [LT_ADD] THEN
     UNDISCH_THEN
       `d3 + d4 + 1 = l`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
     ALL_TAC] THEN
    REWRITE_TAC [MULT_0; ADD1; GSYM ADD_ASSOC; ZERO_ADD; ADD_0] THEN
    STRIP_TAC;
    ALL_TAC] THEN
   MP_TAC (SPEC `mi : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `mis : num` SUBST_VAR_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   SUBGOAL_THEN
     `{i | 0 < i /\
           i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC (SUC mis) /\
           signal sa (t + l + 1 + i)} =
      {i | 0 < i /\
           i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis /\
           signal sa (t + l + 1 + i)} UNION
      {i | (d0 + d1 + d2 + d4 + r + 4) * SUC mis < i + width mb + l /\
           i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC (SUC mis) /\
           signal sa (t + l + 1 + i)}`
     SUBST1_TAC THENL
   [REWRITE_TAC [EXTENSION] THEN
    X_GEN_TAC `i : num` THEN
    REWRITE_TAC [IN_UNION; IN_ELIM] THEN
    REVERSE_TAC (ASM_CASES_TAC `signal sa (t + l + 1 + i)`) THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `i = 0` THENL
    [ASM_REWRITE_TAC [LT_NZ; ZERO_ADD; DE_MORGAN_THM; NOT_LT] THEN
     DISJ1_TAC THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `d0 + d1 + d2 + d4 + r + 4` THEN
     ASM_REWRITE_TAC [MULT_SUC; LE_ADD];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [LT_NZ] THEN
    ASM_CASES_TAC
      `i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis` THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * SUC mis` THEN
     ASM_REWRITE_TAC [LE_MULT_LCANCEL; SUC_LE];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [GSYM NOT_LE];
    ALL_TAC] THEN
   MP_TAC
     (ISPECL
        [`{i | 0 < i /\
               i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis /\
               signal sa (t + l + 1 + i)}`;
         `{i | (d0 + d1 + d2 + d4 + r + 4) * SUC mis < i + width mb + l /\
               i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC (SUC mis) /\
               signal sa (t + l + 1 + i)}`]
        CARD_UNION) THEN
   ANTS_TAC THENL
   [CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{i | i <= (d0 + d1 + d2 + d4 + r + 4) * SUC mis}` THEN
     REWRITE_TAC [FINITE_NUMSEG_LE] THEN
     REWRITE_TAC [SUBSET] THEN
     X_GEN_TAC `i : num` THEN
     REWRITE_TAC [IN_ELIM] THEN
     STRIP_TAC THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `i + width mb + l` THEN
     ASM_REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `{i | i <= (d0 + d1 + d2 + d4 + r + 4) * SUC (SUC mis)}` THEN
     REWRITE_TAC [FINITE_NUMSEG_LE] THEN
     REWRITE_TAC [SUBSET] THEN
     X_GEN_TAC `i : num` THEN
     REWRITE_TAC [IN_ELIM] THEN
     STRIP_TAC THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `i + width mb + l` THEN
     ASM_REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [DISJOINT; EXTENSION] THEN
    X_GEN_TAC `i : num` THEN
    REWRITE_TAC [IN_INTER; IN_ELIM; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [NOT_LT];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM
     (fun th ->
        MP_TAC (SPEC `mis : num` th) THEN
        ANTS_TAC THENL
        [MATCH_ACCEPT_TAC SUC_LT;
         ALL_TAC]) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC mis` THEN
    ASM_REWRITE_TAC [SUC_LE];
    ALL_TAC] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   CONV_TAC (RAND_CONV (REWR_CONV ADD1)) THEN
   REWRITE_TAC [EQ_ADD_LCANCEL] THEN
   SUBGOAL_THEN
     `{i | (d0 + d1 + d2 + d4 + r + 4) * SUC mis < i + width mb + l /\
           i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC (SUC mis) /\
           signal sa (t + l + 1 + i)} =
      {(d0 + d1 + d2 + d4 + r + 4) * SUC mis}`
     (fun th -> REWRITE_TAC [th; CARD_SING]) THEN
   REWRITE_TAC [EXTENSION] THEN
   X_GEN_TAC `i : num` THEN
   REWRITE_TAC [IN_SING; IN_ELIM] THEN
   REVERSE_TAC EQ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC
      [LT_ADD; LE_ADD_LCANCEL; GSYM ADD_ASSOC;
       ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
    ASM_REWRITE_TAC [] THEN
    UNDISCH_THEN
      `d3 + d4 + 1 = l`
      (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
    ALL_TAC] THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM LE_ANTISYM; GSYM NOT_LT; GSYM DE_MORGAN_THM] THEN
   STRIP_TAC THENL
   [POP_ASSUM
      (X_CHOOSE_THEN `id : num` SUBST_VAR_TAC o
       REWRITE_RULE [LT_EXISTS]) THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [] THEN
    FIRST_X_ASSUM (K ALL_TAC o SPEC `id : num`) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `id : num`) THEN
    ANTS_TAC THENL
    [POP_ASSUM MP_TAC THEN
     REWRITE_TAC
       [LE_ADD_LCANCEL; GSYM ADD_ASSOC;
        ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
     REWRITE_TAC [SUC_ADD; LE_SUC_LT] THEN
     REWRITE_TAC [GSYM NOT_LE; CONTRAPOS_THM] THEN
     STRIP_TAC THEN
     UNDISCH_THEN
       `d3 + d4 + 1 = l`
       (SUBST1_TAC o SYM) THEN
     REWRITE_TAC
       [GSYM ADD1; SYM (NUM_REDUCE_CONV `SUC 3`); ADD_SUC; LE_SUC] THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `id : num` THEN
     ASM_REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    REWRITE_TAC [ADD1] THEN
    STRIP_TAC;
    ALL_TAC] THEN
   UNDISCH_THEN
     `width mb + l <= d0 + d1 + d2 + d4 + r + 4`
     (X_CHOOSE_THEN `wd : num` (STRIP_ASSUME_TAC o SYM) o
      REWRITE_RULE [GSYM ADD_ASSOC; LE_EXISTS]) THEN
   UNDISCH_THEN
     `(d0 + d1 + d2 + d4 + r + 4) * SUC mis < i + width mb + l`
     (X_CHOOSE_THEN `id : num` STRIP_ASSUME_TAC o
      REWRITE_RULE [LT_EXISTS]) THEN
   UNDISCH_TAC `signal sa (t + l + 1 + i)` THEN
   REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
   FIRST_X_ASSUM
     (CONV_TAC o LAND_CONV o RAND_CONV o LAND_CONV o RAND_CONV o
      REWR_CONV o SYM) THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   SUBGOAL_THEN
     `width mb + l + wd + SUC id = wd + id + 1 + width mb + l`
     SUBST1_TAC THENL
   [ONCE_REWRITE_TAC [ADD_ASSOC] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; ADD1];
    ALL_TAC] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `wd + id : num`) THEN
   ANTS_TAC THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC
      [LT_ADD_LCANCEL; GSYM ADD_ASSOC;
       ONCE_REWRITE_RULE [ADD_SYM] MULT_SUC] THEN
    REWRITE_TAC [SYM (NUM_REDUCE_CONV `SUC 3`); GSYM ADD1; ADD_SUC; LT_SUC];
    ALL_TAC] THEN
   REWRITE_TAC [GSYM ADD_ASSOC] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  UNDISCH_THEN
    `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms = d`
    SUBST_VAR_TAC THEN
  REVERSE_TAC CONJ_TAC THENL
  [POP_ASSUM (MP_TAC o SPEC `ms : num`) THEN
   REWRITE_TAC [LE_REFL; ADD1; GSYM ADD_ASSOC] THEN
   SUBGOAL_THEN `1 + d3 + d4 = d3 + d4 + 1` SUBST1_TAC THENL
   [CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC];
    ALL_TAC] THEN
   STRIP_TAC;
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i < (d0 + d1 + d2 + d4 + r + 4) * SUC ms ==>
       (signal sa (t + l + 1 + SUC i) <=> ~signal sb (t + l + 1 + SUC i))`
    ASSUME_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [GSYM LE_SUC_LT] THEN
   MP_TAC (SPEC `i : num` NOT_SUC) THEN
   MP_TAC
     (SPECL
        [`SUC i : cycle`; `d0 + d1 + d2 + d4 + r + 4`]
        (ONCE_REWRITE_RULE [MULT_SYM] DIVISION)) THEN
   ANTS_TAC THENL
   [REWRITE_TAC [ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC];
    ALL_TAC] THEN
   DISCH_THEN
     (CONJUNCTS_THEN2
        (fun th -> ONCE_REWRITE_TAC [th])
        MP_TAC) THEN
   SPEC_TAC (`SUC i DIV (d0 + d1 + d2 + d4 + r + 4)`, `iq : num`) THEN
   GEN_TAC THEN
   SPEC_TAC (`SUC i MOD (d0 + d1 + d2 + d4 + r + 4)`, `ir : num`) THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   DISCH_THEN
     (MP_TAC o
      REWRITE_RULE
        [ADD_EQ_0; MULT_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`); NOT_SUC]) THEN
   ASM_CASES_TAC `ir = 0` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [ADD_0] THEN
    STRIP_TAC THEN
    MP_TAC (SPEC `iq : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `iqs : num` SUBST_VAR_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    DISCH_THEN
     (STRIP_ASSUME_TAC o
      REWRITE_RULE
        [LE_MULT_LCANCEL; ADD_EQ_0; SYM (NUM_REDUCE_CONV `SUC 3`);
         NOT_SUC; LE_SUC]) THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `iqs : num`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   DISCH_THEN (K ALL_TAC) THEN
   MP_TAC (SPEC `ir : num` num_CASES) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (X_CHOOSE_THEN `irs : num` SUBST_VAR_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM
     (STRIP_ASSUME_TAC o
      REWRITE_RULE [SYM (NUM_REDUCE_CONV `SUC 3`); ADD_SUC; LT_SUC]) THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `iq <= (ms : num)` MP_TAC THENL
   [REWRITE_TAC [GSYM LT_SUC_LE] THEN
    MP_TAC (SPEC `d0 + d1 + d2 + d4 + r + 4` LT_MULT_LCANCEL) THEN
    REWRITE_TAC [SYM (NUM_REDUCE_CONV `SUC 3`); ADD_SUC; NOT_SUC] THEN
    DISCH_THEN (CONV_TAC o REWR_CONV o GSYM) THEN
    REWRITE_TAC [NUM_REDUCE_CONV `SUC 3`; GSYM ADD_SUC] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `(d0 + d1 + d2 + d4 + r + 4) * iq + SUC irs` THEN
    ASM_REWRITE_TAC [LT_ADD; LT_NZ; NOT_SUC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `iq : num`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `irs : num`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [ADD1];
   ALL_TAC] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms <= i <=>
     i = l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms`
    SUBST1_TAC THENL
  [ASM_REWRITE_TAC [GSYM LE_ANTISYM];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC [GSYM LT_SUC_LE; LT] THEN
  ASM_CASES_TAC `i = l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [ADD_ASSOC] THEN
   MP_TAC
     (SPECL
        [`sar : wire`;
         `sa : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sbr : wire`;
         `sb : wire`]
        delay_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `saq : wire`;
         `sar : wire`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`ld : wire`;
         `sbq : wire`;
         `sbr : wire`]
        or2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   UNDISCH_THEN
     `!i.
        i <= l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms ==>
        (signal ld (t + i) <=> i <= l)`
     (MP_TAC o
      SPEC `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms`) THEN
   REWRITE_TAC [GSYM ADD_ASSOC; LE_REFL] THEN
   SUBGOAL_THEN
     `l + 1 + (d0 + d1 + d2 + d4 + r + 4) * SUC ms <= l <=> F`
     SUBST1_TAC THENL
   [REWRITE_TAC [NOT_LE; LT_ADD; LT_NZ; ADD_EQ_0; ONE; NOT_SUC];
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [] THEN
   MP_TAC
     (SPECL
        [`san : wire`;
         `sap : wire`;
         `saq : wire`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sb : wire`;
         `jp : wire`;
         `sap : wire`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sb : wire`;
         `jpn : wire`;
         `sbp : wire`;
         `sbq : wire`]
        case1_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sa : wire`;
         `mdn : wire`;
         `sbp : wire`]
        and2_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`sa : wire`;
         `san : wire`]
        not_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC
     (SPECL
        [`md : wire`;
         `mdn : wire`]
        not_signal) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM
     (fun th ->
        MP_TAC (SPEC `ms : num` th) THEN
        ANTS_TAC THENL
        [MATCH_ACCEPT_TAC LE_REFL;
         ALL_TAC]) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN
     `l <= d0 + d1 + d2 + d4 + r + 4`
     (X_CHOOSE_THEN `dl : cycle` ASSUME_TAC o
      REWRITE_RULE [LE_EXISTS]) THENL
   [UNDISCH_THEN
      `d3 + d4 + 1 = l`
      (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(d0 + d1 + d2 + r + 1) + d4 + 1` THEN
    ASM_REWRITE_TAC [LE_ADD_RCANCEL] THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `3 + 1`)] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; LE_ADD_LCANCEL] THEN
    CONV_TAC (RAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL; SYM (NUM_REDUCE_CONV `2 + 1`)] THEN
    REWRITE_TAC [LE_ADD];
    ALL_TAC] THEN
   FIRST_X_ASSUM
     (fun th ->
        MP_TAC (SPEC `dl + (l + dl) * ms : cycle` th) THEN
        ANTS_TAC THENL
        [GEN_TAC;
         ALL_TAC]) THENL
   [STRIP_TAC THEN
    MP_TAC (SPEC `i : num` num_CASES) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `is : num` SUBST_VAR_TAC) THEN
    MATCH_MP_TAC (TAUT `!x y. (x <=> ~y) ==> (~x \/ ~y)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [MULT_SUC; GSYM LE_SUC_LT] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `dl + (l + dl) * ms : num` THEN
    ASM_REWRITE_TAC [LE_ADD_RCANCEL; LE_ADDR];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
   SUBGOAL_THEN
     `1 + (l + dl) * SUC ms =
      l + 1 + dl + (l + dl) * ms`
     SUBST1_TAC THENL
   [REWRITE_TAC [MULT_SUC; ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_ACCEPT_TAC ADD_SYM;
    ALL_TAC] THEN
   DISCH_THEN SUBST1_TAC THEN
   SUBGOAL_THEN
     `!i.
        i + width mb <= dl + (l + dl) * ms <=>
        i + width mb + l <= (d0 + d1 + d2 + d4 + r + 4) * SUC ms`
     (fun th -> REWRITE_TAC [th]) THENL
   [GEN_TAC THEN
    CONV_TAC
      (LAND_CONV (REWR_CONV (GSYM (SPEC `l : cycle` LE_ADD_RCANCEL)))) THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    AP_TERM_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC] THEN
    REWRITE_TAC [GSYM ADD_ASSOC; MULT_SUC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [DE_MORGAN_THM] THEN
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `i <= (l : num)` THENL
  [MATCH_MP_TAC (TAUT `!x y. x /\ y ==> x \/ y`) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM
    (X_CHOOSE_THEN `id : num` SUBST_VAR_TAC o
     REWRITE_RULE [NOT_LE; LT_EXISTS]) THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [ONCE_REWRITE_RULE [ADD_SYM] ADD1; GSYM ADD_ASSOC; LT_ADD_LCANCEL] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC (TAUT `!x y. (x <=> ~y) ==> x \/ y`) THEN
  REWRITE_TAC [GSYM ADD1] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [ONCE_REWRITE_RULE [ADD_SYM] ADD1]);;

export_thm montgomery_double_exp_bits_to_num;;

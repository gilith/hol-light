(* ========================================================================= *)
(* MONTGOMERY MULTIPLICATION                                                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for Montgomery multiplication.                            *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/montgomery/montgomery.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of Montgomery multiplication [1].                              *)
(*                                                                           *)
(* 1. http://en.wikipedia.org/wiki/Montgomery_reduction                      *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-def";;

let montgomery_reduce_def = new_definition
  `!n r k a.
     montgomery_reduce n r k a =
     (a + ((a * k) MOD r) * n) DIV r`;;

export_thm montgomery_reduce_def;;

let (montgomery_double_exp_zero,montgomery_double_exp_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!n r k a. montgomery_double_exp n r k a 0 = a) /\
     (!n r k a m.
        montgomery_double_exp n r k a (SUC m) =
        let b = montgomery_reduce n r k (a * a) in
        let c = if r <= b then b - n else b in
        montgomery_double_exp n r k c m)` in
  CONJ_PAIR def;;

export_thm montgomery_double_exp_zero;;
export_thm montgomery_double_exp_suc;;

let montgomery_double_exp_def =
    CONJ montgomery_double_exp_zero montgomery_double_exp_suc;;

(* ------------------------------------------------------------------------- *)
(* Properties of Montgomery multiplication.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery-thm";;

(***
let montgomery_reduce_divides = prove
  (`!n r s k a.
      ~(n = 0) /\
      r * s = k * n + 1 ==>
      montgomery_reduce n r k a =
      a DIV r + (((a * k) MOD r) * n) DIV r +
      (if (a * k * n) MOD r = 0 then 0 else 1)`,

   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
***)

let montgomery_reduce_correct = prove
  (`!n r s k a.
      ~(n = 0) /\
      r * s = k * n + 1 ==>
      montgomery_reduce n r k a MOD n = (a * s) MOD n`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(montgomery_reduce n r k a * (r * s)) MOD n` THEN
   CONJ_TAC THENL
   [SPEC_TAC (`montgomery_reduce n r k a`,`m : num`) THEN
    GEN_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
    MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(m * k * n) MOD n = 0` SUBST1_TAC THENL
    [REWRITE_TAC [MULT_ASSOC] THEN
     ONCE_REWRITE_TAC [MULT_SYM] THEN
     MATCH_MP_TAC MOD_MULT THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REWRITE_TAC [ZERO_ADD] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC MOD_MOD_REFL THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [MULT_ASSOC; montgomery_reduce_def] THEN
   MP_TAC (SPEC `n : num` MOD_MULT_MOD2') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC (SPECL [`a + (a * k) MOD r * n`; `r : num`] DIVISION_DEF_DIV) THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `(a + (a * k) MOD r * n) MOD r = 0` SUBST1_TAC THENL
   [MP_TAC (SPEC `r : num` MOD_MOD_REFL') THEN
    MP_TAC (SPEC `r : num` MOD_MULT_MOD2') THEN
    MP_TAC (SPEC `r : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
    POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
    SUBGOAL_THEN `a + (a * k) * n = a * (1 + k * n)` SUBST1_TAC THENL
    [REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1; MULT_ASSOC];
     ALL_TAC] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    ONCE_REWRITE_TAC [MULT_SYM] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MATCH_MP_TAC MOD_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [ADD_0] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   SUBGOAL_THEN `((a * k) MOD r * n) MOD n = 0` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC [MULT_SYM] THEN
    MATCH_MP_TAC MOD_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   REWRITE_TAC [ADD_0] THEN
   MATCH_MP_TAC MOD_MOD_REFL THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_correct;;

let montgomery_reduce_bound = prove
  (`!n r k m a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * m ==>
      montgomery_reduce n r k a < m + n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_reduce_def] THEN
   MATCH_MP_TAC LT_LDIV THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB] THEN
   MATCH_MP_TAC LTE_TRANS THEN
   EXISTS_TAC `a + r * n : num` THEN
   ASM_REWRITE_TAC [LT_ADD_LCANCEL; LE_ADD_RCANCEL; LT_MULT_RCANCEL] THEN
   MATCH_MP_TAC DIVISION_DEF_MOD THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm montgomery_reduce_bound;;

let montgomery_reduce_normalized_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * n ==>
      montgomery_reduce n r k a < 2 * n`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [MULT_2] THEN
   MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_normalized_bound;;

let montgomery_reduce_unnormalized_bound = prove
  (`!n r k a.
      ~(n = 0) /\
      ~(r = 0) /\
      a <= r * r ==>
      montgomery_reduce n r k a < r + n`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC montgomery_reduce_bound THEN
   ASM_REWRITE_TAC []);;

export_thm montgomery_reduce_unnormalized_bound;;

let montgomery_double_exp_correct = prove
  (`!n r s k a m.
      ~(n = 0) /\
      n <= r /\
      r * s = k * n + 1 ==>
      montgomery_double_exp n r k a m MOD n =
      ((a * s) EXP (2 EXP m) * r) MOD n`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [GEN_TAC THEN
    REWRITE_TAC [montgomery_double_exp_zero; EXP_0; EXP_1] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    MP_TAC (SPEC `n : num` MOD_MULT_RMOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(s * r) MOD n = 1 MOD n` SUBST1_TAC THENL
    [MATCH_MP_TAC MOD_EQ THEN
     EXISTS_TAC `k : num` THEN
     ONCE_REWRITE_TAC [MULT_SYM; ADD_SYM] THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC [MULT_1]];
    ALL_TAC] THEN
   GEN_TAC THEN
   ASM_REWRITE_TAC
     [montgomery_double_exp_suc; EXP_SUC; LET_DEF; LET_END_DEF; EXP_MULT;
      EXP_2] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MP_TAC (SPEC `n : num` MOD_EXP_MOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   MP_TAC (SPEC `n : num` MOD_MULT_LMOD') THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `((montgomery_reduce n r k (a * a) - n) + n) MOD n` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
     MP_TAC (SPEC `n : num` MOD_REFL) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [ADD_0] THEN
     MATCH_MP_TAC MOD_MOD_REFL THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `montgomery_reduce n r k (a * a) MOD n` THEN
     CONJ_TAC THENL
     [AP_THM_TAC THEN
      AP_TERM_TAC THEN
      MATCH_MP_TAC SUB_ADD THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `r : num` THEN
      ASM_REWRITE_TAC [];
      MATCH_MP_TAC montgomery_reduce_correct THEN
      ASM_REWRITE_TAC []]];
    MATCH_MP_TAC montgomery_reduce_correct THEN
    ASM_REWRITE_TAC []]);;

export_thm montgomery_double_exp_correct;;

let montgomery_double_exp_bound = prove
  (`!n r k a m.
      ~(n = 0) /\
      n <= r /\
      a < r ==>
      montgomery_double_exp n r k a m < r`,
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [montgomery_double_exp_zero];
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [montgomery_double_exp_suc; LET_DEF; LET_END_DEF] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [GSYM NOT_LT] THEN
   ASM_CASES_TAC `montgomery_reduce n r k (a * a) < r` THENL
   [ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [GSYM (SPEC `n : num` LT_ADD_RCANCEL)] THEN
   SUBGOAL_THEN
     `montgomery_reduce n r k (a * a) - n + n =
      montgomery_reduce n r k (a * a)` SUBST1_TAC THENL
   [MATCH_MP_TAC SUB_ADD THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `r : num` THEN
    ASM_REWRITE_TAC [] THEN
    ASM_REWRITE_TAC [GSYM NOT_LT];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   MATCH_MP_TAC montgomery_reduce_unnormalized_bound THEN
   ASM_REWRITE_TAC [] THEN
   CONJ_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [NOT_LT; LE_0];
    POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [LT_LE]) THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `a * r : num` THEN
    ASM_REWRITE_TAC [LE_MULT_LCANCEL; LE_MULT_RCANCEL]]);;

export_thm montgomery_double_exp_bound;;

(* ------------------------------------------------------------------------- *)
(* Definition of a Montgomery multiplication circuit.                        *)
(* ------------------------------------------------------------------------- *)

(* -------------------------------------------------------------- *)
(* Montgomery multiplication modulo 2^(r+4)                       *)
(* -------------------------------------------------------------- *)
(*        r+5 r+4 r+3 r+2 r+1  r  ... d+2 d+1  d  ...  2   1   0  *)
(* -------------------------------------------------------------- *)
(*  xs  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  xc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ys  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  yc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ks  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  kc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ns  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  nc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  pb  =  -   -   -   -   -   -  ...  -   -   X  ...  X   X   X  *)
(*  ps  =  -   -   -   X   X   X  ...  X   X   -  ...  -   -   -  *)
(*  pc  =  -   -   -   X   X   X  ...  X   -   -  ...  -   -   -  *)
(* -------------------------------------------------------------- *)
(*  vs  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  vc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  sa  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  sb  =  -   -   -   X   X   X  ...  X   -   -  ...  -   -   -  *)
(*  sc  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  sd  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(* -------------------------------------------------------------- *)
(*  zs  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  zc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)

(***
let montgomery_mult_def = new_definition
  `!ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc.
     montgomery_mult ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc <=>
     ?r pb ps pc pbp qb qs qc vb vs vc vt sa sb sc sd
      ld1 ld2 pb1 pbp0 pbp1 qb2.
       width xs = r + 2 /\
       width xc = r + 2 /\
       width ys = r + 2 /\
       width yc = r + 2 /\
       width ks = r + 3 /\
       width kc = r + 3 /\
       width ns = r + 1 /\
       width nc = r + 1 /\
       width zs = r + 2 /\
       width zc = r + 2 /\
       width ps = r + 2 /\
       width pc = r + 2 /\
       width pbp = d1 + d2 + 1 /\
       width qs = r + 3 /\
       width qc = r + 3 /\
       width vs = r + 1 /\
       width vc = r + 1 /\
       width sa = r + 1 /\
       width sb = r + 1 /\
       width sc = r + 1 /\
       width sd = r + 1
       /\
       wire pbp d1 pb1 /\
       bsub pbp 1 (d1 + d2) pbp0 /\
       brev pbp0 pbp1
       /\
       sum_carry_mult ld xs xc d0 ys yc pb ps pc /\
       pipe ld (d0 + d1) ld1 /\
       bpipe pb pbp /\
       bmult ld1 pb1 ks kc qb qs qc /\
       pipe ld1 d2 ld2 /\
       pipe qb d2 qb2 /\
       bmult ld2 qb2 ns nc vb vs vc /\
       sticky ld2 vb vt`;;

export_thm montgomery_mult_def;;

let montgomery_compress_def = new_definition
  `!rx ry rz xs xc ys' yc'.
      montgomery_compress rx ry rz xs xc ys' yc' <=>
      ?r.
         width rx = r /\
         width ry = r /\
         width rz = r /\
         width xs = (r + 2) /\
         width xc = (r + 2)
         /\
         width ys' = r /\
         width yc' = r`;;

export_thm montgomery_compress_def;;

let montgomery_circuit_def = new_definition
  `!ld nb kb rx ry rz xs xc ys yc
    zs' zc'.
      montgomery_circuit
        ld nb kb rx ry rz xs xc ys yc
        zs' zc' <=>
      ?r ps pc qs qc.
         width nb = r /\
         width kb = r /\
         width rx = r /\
         width ry = r /\
         width rz = r /\
         width xs = r /\
         width xc = r /\
         width ys = r /\
         width yc = r
         /\
         width zs' = r /\
         width zc' = r
         /\
         montgomery_loop nb kb xs xc ps pc /\
         bdelay ps qs /\
         bdelay pc qc /\
         montgomery_compress rx ry rz qs qc zs' zc'`;;

export_thm montgomery_circuit_def;;

(* ------------------------------------------------------------------------- *)
(* Correctness of a Montgomery multiplication circuit.                       *)
(* ------------------------------------------------------------------------- *)

(***)
let montgomery_mult_bits_to_num = prove
 (`!x y n kn ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc t k.
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal xs t) + 2 * bits_to_num (bsignal xc t) = x /\
     (!i.
        i <= d0 + k /\ d0 <= i /\ i <= width xs + d0 + 1 ==>
        bits_to_num (bsignal ys (t + i)) +
        2 * bits_to_num (bsignal yc (t + i)) = y) /\
     (!i.
        d0 + d1 <= i /\ i <= d0 + d1 + k ==>
        bits_to_num (bsignal ks (t + i)) +
        2 * bits_to_num (bsignal kc (t + i)) = kn) /\
     (!i.
        d0 + d1 + d2 <= i /\ i <= d0 + d1 + d2 + k ==>
        bits_to_num (bsignal ns (t + i)) +
        2 * bits_to_num (bsignal nc (t + i)) = n) /\
     montgomery_mult ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc ==>
     bits_to_num (bsignal zs (t + d0 + d1 + d2 + k)) +
     2 * bits_to_num (bsignal zc (t + d0 + d1 + d2 + k)) =
     bit_shr (x * y + bit_bound (x * y * kn) (k + 1) * n) (k + 1)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_mult_def] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i.
       i <= k ==>
       bit_cons (signal pb (t + d0 + i))
         (bits_to_num (bsignal ps (t + d0 + i)) +
          2 * bits_to_num (bsignal pc (t + d0 + i))) =
       bit_shr (bit_bound x (i + 1) * y) i`
    ASSUME_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC sum_carry_mult_bits_to_num THEN
   EXISTS_TAC `ld : wire` THEN
   EXISTS_TAC `xs : bus` THEN
   EXISTS_TAC `xc : bus` THEN
   EXISTS_TAC `ys : bus` THEN
   EXISTS_TAC `yc : bus` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT CONJ_TAC THENL
   [X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`j : cycle`; `i : cycle`; `k : cycle`] LE_TRANS) THEN
    ASM_REWRITE_TAC [];
    X_GEN_TAC `j : cycle` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `d0 + i : cycle` THEN
    ASM_REWRITE_TAC [LE_ADD_LCANCEL]];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= k ==> signal pb (t + d0 + i) = bit_nth (x * y) i`
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
       i <= k ==>
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
    `!i. i <= k ==> (signal ld1 (t + d0 + d1 + i) <=> i = 0)`
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
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= k ==> signal pb1 (t + d0 + d1 + i) = bit_nth (x * y) i`
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
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i.
       i <= k ==>
       bit_cons (signal qb (t + d0 + d1 + i))
         (bits_to_num (bsignal qs (t + d0 + d1 + i)) +
          2 * bits_to_num (bsignal qc (t + d0 + d1 + i))) =
       bit_shr (bit_bound (x * y) (i + 1) * kn) i`
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
   MP_TAC (SPECL [`j : cycle`; `i : cycle`; `k : cycle`] LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_THEN `j <= (i : cycle)` (K ALL_TAC) THEN
   UNDISCH_THEN `i <= (k : cycle)` (K ALL_TAC) THEN
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
  POP_ASSUM (K ALL_TAC) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
    `!i. i <= k ==> signal qb (t + d0 + d1 + i) = bit_nth (x * y * kn) i`
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
     `bit_nth (bit_bound (bit_bound (x * y) (i + 1) * kn) (i + 1)) i` THEN
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
    `!i. i <= k ==> (signal ld2 (t + d0 + d1 + d2 + i) <=> i = 0)`
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
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  SUBGOAL_THEN
    `!i. i <= k ==> signal qb2 (t + d0 + d1 + d2 + i) = bit_nth (x * y * kn) i`
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
       i <= k ==>
       bit_cons (signal vb (t + d0 + d1 + d2 + i))
         (bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
          2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i))) =
       bit_shr (bit_bound (x * y * kn) (i + 1) * n) i`
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
   MP_TAC (SPECL [`j : cycle`; `i : cycle`; `k : cycle`] LE_TRANS) THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_THEN `j <= (i : cycle)` (K ALL_TAC) THEN
   UNDISCH_THEN `i <= (k : cycle)` (K ALL_TAC) THEN
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
       i <= k ==>
       bits_to_num (bsignal vs (t + d0 + d1 + d2 + i)) +
       2 * bits_to_num (bsignal vc (t + d0 + d1 + d2 + i)) =
       bit_shr (bit_bound (x * y * kn) (i + 1) * n) (i + 1)`
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
       i <= k ==>
       signal vb (t + d0 + d1 + d2 + i) =
       bit_nth (x * y * kn * n) i`
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
     `bit_nth (bit_bound (bit_bound (x * y * kn) (i + 1) * n) (i + 1)) i` THEN
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
       i <= k ==>
       (signal vt (t + d0 + d1 + d2 + i) <=>
        ~(bit_bound (x * y * kn * n) (i + 1) = 0))`
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
      (?j. j <= i /\ bit_nth (x * y * kn * n) j)`
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
  (***)
  SUBGOAL_THEN
    `!i.
       d1 + d2 + i <= k ==>
       bits_to_num (bsignal sa (t + d0 + d1 + d2 + i + 1)) +
       bits_to_num (bsignal sb (t + d0 + d1 + d2 + i + 1)) +
       bits_to_num (bsignal sc (t + d0 + d1 + d2 + i + 1)) +
       bits_to_num (bsignal sd (t + d0 + d1 + d2 + i + 1)) =
       bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (i + 1) +
       bit_shr (bit_bound (x * y * kn) (i + 1) * n) (i + 1) +
       bit_to_num (~(bit_bound (x * y * kn * n) (i + 1) = 0))`
    MP_TAC THENL
  [REPEAT STRIP_TAC THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC
     `bit_bound (bit_shr (x * y) (i + 1)) (d1 + d2) +
      bit_shl
        (bit_shr (bit_bound x (d1 + d2 + i + 1) * y) (d1 + d2 + i + 1))
        (d1 + d2) +
      bit_shr (bit_bound (x * y * kn) (i + 1) * n) (i + 1) +
      bit_to_num (~(bit_bound (x * y * kn * n) (i + 1) = 0))` THEN
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
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(d1 + d2) + i : cycle` THEN
    REWRITE_TAC [LE_ADDR] THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   UNDISCH_THEN
     `!i.
        i <= k ==>
        bits_to_num (bsignal ps (t + d0 + i)) +
        2 * bits_to_num (bsignal pc (t + d0 + i)) =
        bit_shr (bit_bound x (i + 1) * y) (i + 1)`
     (MP_TAC o SPEC `d1 + d2 + i : cycle`) THEN
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
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [ADD_ASSOC] THEN
    UNDISCH_THEN `jr + j + 1 = d1 + d2` (SUBST1_TAC o SYM) THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [ADD_ASSOC; LE_ADD_RCANCEL] THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    REWRITE_TAC [GSYM ADD_ASSOC; LE_ADDR];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   (***)
   UNDISCH_THEN
     `!i.
        i <= k ==>
        (signal vt (t + d0 + d1 + d2 + i) <=>
         ~(bit_bound (x * y * kn * n) (i + 1) = 0))`
     (MP_TAC o SPEC `i : cycle`) THEN
   ANTS_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `(d1 + d2) + i : cycle` THEN
    REWRITE_TAC [LE_ADDR] THEN
    ASM_REWRITE_TAC [GSYM ADD_ASSOC];
    ALL_TAC] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN


    FIRST_X_ASSUM (MP_TAC o SPEC `j + i + 1`) THEN
    ANTS_TAC THENL
    [CHEAT_TAC;
     ALL_TAC] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN


let montgomery_circuit = prove
 (`!n r s k x y ld nb kb rx ry rz xs xc ys yc zs' zc' t.
      ~(n = 0) /\
      (2 EXP (r + 2)) * s = k * n + 1 /\
      width nb = r /\
      (!i. i < r ==> (signal ld (t + i) <=> i = 0)) /\
      (!i.
         0 < i /\ i < r ==>
         bits_to_num (bsignal nb (t + i)) = n) /\
      (!i.
         0 < i /\ i < r ==>
         bits_to_num (bsignal kb (t + i)) = k MOD (2 EXP r)) /\
      bits_to_num (bsignal rx (t + (r + 8))) = (2 EXP r) MOD n /\
      bits_to_num (bsignal ry (t + (r + 8))) = (2 * (2 EXP r)) MOD n /\
      bits_to_num (bsignal rz (t + (r + 8))) = (3 * (2 EXP r)) MOD n /\
      (!i.
        i < r ==>
        bits_to_num (bsignal xs' (t + i)) +
        2 * bits_to_num (bsignal xc' (t + i)) = x) /\
      bits_to_num (bsignal ys' t) +
      2 * bits_to_num (bsignal yc' t) = y /\
      montgomery_circuit
        ld nb kb rx ry rz xs xc ys yc
        zs' zc' ==>
      (bits_to_num (bsignal zs' (t + (r + 8))) +
       2 * bits_to_num (bsignal zc' (t + (r + 8)))) MOD n =
      ((x * y) * s) MOD n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [montgomery_circuit_def] THEN
  STRIP_TAC THEN
***)

(* ------------------------------------------------------------------------- *)
(* Automatically generating verified Montgomery multiplication circuits.     *)
(* ------------------------------------------------------------------------- *)

let mk_montgomery n =
    let r = mk_numeral (add_num (bitwidth_num (dest_numeral n)) num_2) in
    let egcd =
        let rth = NUM_REDUCE_CONV (mk_comb (`(EXP) 2`, r)) in
        let eth = prove_egcd (rhs (concl rth)) n in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let s = rand (lhs (concl egcd)) in
    let k = lhand (lhand (rhs (concl egcd))) in
    (egcd,s,k);;

(* ------------------------------------------------------------------------- *)
(* LCS35 Time Capsule Crypto-Puzzle [1].                                     *)
(*                                                                           *)
(* 1. http://people.csail.mit.edu/rivest/lcs35-puzzle-description.txt        *)
(* ------------------------------------------------------------------------- *)

(***
let time_capsule_n_def = new_definition
  `time_capsule_n =
   6314466083072888893799357126131292332363298818330841375588990772701957128924885547308446055753206513618346628848948088663500368480396588171361987660521897267810162280557475393838308261759713218926668611776954526391570120690939973680089721274464666423319187806830552067951253070082020241246233982410737753705127344494169501180975241890667963858754856319805507273709904397119733614666701543905360152543373982524579313575317653646331989064651402133985265800341991903982192844710212464887459388853582070318084289023209710907032396934919962778995323320184064522476463966355937367009369212758092086293198727008292431243681`;;

export_thm time_capsule_n_def;;

let time_capsule_t_def = new_definition
  `time_capsule_t = 79685186856218`;;

export_thm time_capsule_t_def;;

let time_capsule_z_def = new_definition
  `time_capsule_z =
   4273385266812394147070994861525419078076239304748427595531276995752128020213613672254516516003537339494956807602382848752586901990223796385882918398855224985458519974818490745795238804226283637519132355620865854807750610249277739682050363696697850022630763190035330004501577720670871722527280166278354004638073890333421755189887803390706693131249675969620871735333181071167574435841870740398493890811235683625826527602500294010908702312885095784549814408886297505226010693375643169403606313753753943664426620220505295457067077583219793772829893613745614142047193712972117251792879310395477535810302267611143659071382`;;

export_thm time_capsule_z_def;;
***)

logfile_end ();;

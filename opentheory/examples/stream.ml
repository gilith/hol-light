(* ------------------------------------------------------------------------- *)
(* Streams.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "stream-def";;

let (snth_stream,stream_snth) =
  let exists = prove (`?(s : num -> A). T`, REWRITE_TAC []) in
  let tybij =
      REWRITE_RULE []
        (new_type_definition "stream" ("stream","snth") exists) in
  let th1 = prove
    (`!(s : A stream). stream (snth s) = s`, REWRITE_TAC [tybij])
  and th2 = prove
    (`!(f : num -> A). snth (stream f) = f`, REWRITE_TAC [tybij]) in
  (th1,th2);;

export_thm snth_stream;;
export_thm stream_snth;;

let stream_tybij = CONJ snth_stream stream_snth;;

let shd_def = new_definition
  `!s : A stream. shd s = snth s 0`;;

export_thm shd_def;;

let sdrop_def = new_definition
  `!(s : A stream) n. sdrop s n = stream (\m. snth s (m + n))`;;

export_thm sdrop_def;;

let stl_def = new_definition
  `!s : A stream. stl s = sdrop s 1`;;

export_thm stl_def;;

let scons_def = new_definition
  `!h (t : A stream).
     scons h t = stream (\n. if n = 0 then h else snth t (n - 1))`;;

export_thm scons_def;;

let ssplit_def = new_definition
  `!s : A stream.
     ssplit s =
     (stream (\n. snth s (2 * n)),
      stream (\n. snth s (2 * n + 1)))`;;

export_thm ssplit_def;;

let sinterleave_def = new_definition
  `!s1 s2 : A stream.
     sinterleave s1 s2 =
     stream (\n. if EVEN n then snth s1 (n DIV 2) else snth s2 (n DIV 2))`;;

export_thm sinterleave_def;;

let sappend_def = new_definition
  `!l (s : A stream).
     sappend l s =
     stream (\n. if n < LENGTH l then nth l n else snth s (n - LENGTH l))`;;

export_thm sappend_def;;

logfile "stream-thm";;

let snth_eq_imp = prove
  (`!(s1 : A stream) s2.
      (!n. snth s1 n = snth s2 n) ==>
      s1 = s2`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM snth_stream] THEN
   AP_TERM_TAC THEN
   ASM_REWRITE_TAC [FUN_EQ_THM]);;

export_thm snth_eq_imp;;

let shd_scons = prove
  (`!(h : A) t. shd (scons h t) = h`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [shd_def; scons_def; stream_snth]);;

export_thm shd_scons;;

let stl_scons = prove
  (`!(h : A) t. stl (scons h t) = t`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC
     [stl_def; scons_def; sdrop_def; stream_snth; GSYM ADD1;
      NOT_SUC; SUC_SUB1]);;

export_thm stl_scons;;

let snth_sappend = prove
  (`!l (s : A stream) n.
      snth (sappend l s) n =
      if n < LENGTH l then nth l n else snth s (n - LENGTH l)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [sappend_def; stream_snth]);;

export_thm snth_sappend;;

let sappend_assoc = prove
  (`!l1 l2 (s : A stream).
      sappend (APPEND l1 l2) s = sappend l1 (sappend l2 s)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [snth_sappend; LENGTH_APPEND] THEN
   ASM_CASES_TAC `n < LENGTH (l1 : A list)` THENL
   [SUBGOAL_THEN
      `n < LENGTH (l1 : A list) + LENGTH (l2 : A list)` ASSUME_TAC THENL
    [MATCH_MP_TAC LTE_TRANS THEN
     EXISTS_TAC `LENGTH (l1 : A list)` THEN
     ASM_REWRITE_TAC [LE_ADD];
     ALL_TAC] THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`l1 : A list`; `l2 : A list`; `n : num`] nth_append) THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
   REWRITE_TAC [LT_ADD_LCANCEL; ADD_SUB2] THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`l1 : A list`; `l2 : A list`;
                   `LENGTH (l1 : A list) + d`] nth_append) THEN
    ASM_REWRITE_TAC [LT_ADD_LCANCEL; ADD_SUB2] THEN
    DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
    [SUBGOAL_THEN `F` CONTR_TAC THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [NOT_LT; LE_ADD];
     REFL_TAC];
    ALL_TAC] THEN
   REWRITE_TAC [] THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [ADD_ASSOC; ADD_SUB2]);;

export_thm sappend_assoc;;

let nil_sappend = prove
  (`!s : A stream. sappend [] s = s`,
   GEN_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [sappend_def; LENGTH; LT; SUB_0; stream_snth]);;

export_thm nil_sappend;;

let cons_sappend = prove
  (`!h t (s : A stream). sappend (CONS h t) s = scons h (sappend t s)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC snth_eq_imp THEN
   GEN_TAC THEN
   REWRITE_TAC [sappend_def; stream_snth; scons_def; LENGTH] THEN
   NUM_CASES_TAC `n : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LT_NZ; NOT_SUC; nth_0];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [NOT_SUC; LT_SUC; SUC_SUB1] THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [] THEN
    MATCH_MP_TAC nth_suc THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [] THEN
    AP_TERM_TAC THEN
    POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_LT; LE_EXISTS]) THEN
    DISCH_THEN (CHOOSE_THEN SUBST1_TAC) THEN
    REWRITE_TAC [GSYM SUC_ADD; ADD_SUB2]]);;

export_thm cons_sappend;;

let ssplit_sinterleave = prove
  (`!s1 s2 : A stream. ssplit (sinterleave s1 s2) = (s1,s2)`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [ssplit_def; sinterleave_def; PAIR_EQ] THEN
   SUBGOAL_THEN `~(2 = 0)` ASSUME_TAC THENL
   [NUM_REDUCE_TAC;
    ALL_TAC] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC snth_eq_imp THEN
    GEN_TAC THEN
    REWRITE_TAC [stream_snth; EVEN_DOUBLE] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC DIV_MULT THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC snth_eq_imp THEN
    GEN_TAC THEN
    REWRITE_TAC [stream_snth; GSYM NOT_ODD] THEN
    SUBGOAL_THEN `ODD (2 * n + 1)`
      (fun th ->
         (SUBST1_TAC o EQT_INTRO) th THEN
         (STRIP_ASSUME_TAC o REWRITE_RULE [ODD_MOD]) th) THENL
    [REWRITE_TAC [GSYM ADD1; ODD_DOUBLE];
     ALL_TAC] THEN
    REWRITE_TAC [] THEN
    AP_TERM_TAC THEN
    MP_TAC (SPECL [`2`; `(2 * n + 1) DIV 2`; `n : num`] EQ_MULT_LCANCEL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MP_TAC (SPECL [`2 * n + 1 : num`; `2`] DIVISION_DEF_DIV) THEN
    ASM_REWRITE_TAC [EQ_ADD_RCANCEL] THEN
    DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm ssplit_sinterleave;;

logfile_end ();;

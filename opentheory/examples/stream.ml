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

logfile_end ();;

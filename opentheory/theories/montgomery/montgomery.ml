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
(* Montgomery multiplication.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "montgomery";;

let montgomery_reduction = prove
  (`!n r s k a.
      ~(n = 0) /\
      r * s = k * n + 1 ==>
      ((a + ((a * k) MOD r) * n) DIV r) MOD n = (a * s) MOD n`,
   REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_VAR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [ZERO_MULT; GSYM ADD1; NOT_SUC];
    ALL_TAC] THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(((a + (a * k) MOD r * n) DIV r) * (r * s)) MOD n` THEN
   CONJ_TAC THENL
   [SPEC_TAC (`(a + (a * k) MOD r * n) DIV r`,`q : num`) THEN
    GEN_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    ASM_REWRITE_TAC [LEFT_ADD_DISTRIB; MULT_1] THEN
    MP_TAC (SPEC `n : num` MOD_ADD_MOD') THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th] THEN ASSUME_TAC th) THEN
    SUBGOAL_THEN `(q * k * n) MOD n = 0` SUBST1_TAC THENL
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
   REWRITE_TAC [MULT_ASSOC] THEN
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

export_thm montgomery_reduction;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Natural number divisibility.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "natural-divides-def";;

let divides_def = new_definition
  `!(a:num) b. divides a b <=> ?c. c * a = b`;;

export_thm divides_def;;

logfile "natural-divides-thm";;

let symmetry_reduction = prove
  (`!p : num -> num -> bool.
      (!m n. p m n ==> p n m) /\
      (!m n. m <= n ==> p m n) ==>
      (!m n. p m n)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`m : num`; `n : num`] LE_CASES) THEN
   STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_THEN `!m n : num. p m n ==> p n m` MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let divides_zero = prove
  (`!a. divides a 0`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [MULT]);;

export_thm divides_zero;;

let divides_one = prove
  (`!a. divides a 1 <=> a = 1`,
   REWRITE_TAC [divides_def; MULT_EQ_1; UNWIND_THM2]);;

export_thm divides_one;;

let zero_divides = prove
  (`!a. divides 0 a <=> a = 0`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def; MULT_0] THEN
   MATCH_ACCEPT_TAC EQ_SYM_EQ);;

export_thm zero_divides;;

let one_divides = prove
  (`!a. divides 1 a`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def; MULT_CLAUSES] THEN
   EXISTS_TAC `a : num` THEN
   REFL_TAC);;

export_thm one_divides;;

let divides_refl = prove
  (`!a. divides a a`,
   GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   EXISTS_TAC `1` THEN
   REWRITE_TAC [MULT_CLAUSES]);;

export_thm divides_refl;;

let divides_add = prove
  (`!a b c. divides a b /\ divides a c ==> divides a (b + c)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [divides_def] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
   EXISTS_TAC `(c' : num) + c''` THEN
   MATCH_ACCEPT_TAC RIGHT_ADD_DISTRIB);;

export_thm divides_add;;

let divides_sub = prove
  (`!a b c. c <= b /\ divides a b /\ divides a c ==> divides a (b - c)`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_divides] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [SUB_REFL];
    REWRITE_TAC [divides_def] THEN
    STRIP_TAC THEN
    REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [LE_MULT_RCANCEL] THEN
    STRIP_TAC THEN
    EXISTS_TAC `(c' : num) - c''` THEN
    MATCH_MP_TAC RIGHT_SUB_DISTRIB THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm divides_sub;;

logfile_end ();;

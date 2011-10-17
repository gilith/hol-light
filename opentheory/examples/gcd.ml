(* ------------------------------------------------------------------------- *)
(* Natural number greatest common divisor.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "natural-gcd-def";;

let gcd_induction = prove
  (`!p : num -> num -> bool.
      (!m n. p m n ==> p n m) /\
      (!n. p 0 n) /\
      (!m n. p m n ==> p (m + n) n) ==>
      (!m n. p m n)`,
   REPEAT STRIP_TAC THEN
   WF_INDUCT_TAC `(m : num) + n` THEN
   ASM_CASES_TAC `m = 0` THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
   ASM_CASES_TAC `n = 0` THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    UNDISCH_THEN `!(m : num) n. p m n ==> p n m` MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    ALL_TAC] THEN
   MP_TAC (SPECL [`m : num`; `n : num`] LE_CASES) THEN
   STRIP_TAC THENL
   [UNDISCH_THEN `!(m : num) n. p m n ==> p n m` MATCH_MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    UNDISCH_THEN `!(m : num) n. p m n ==> p (m + n) n` MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV ADD_SYM))) THEN
    ASM_REWRITE_TAC [LT_ADDR; LT_NZ];
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [LE_EXISTS] THEN
    DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    UNDISCH_THEN `!(m : num) n. p m n ==> p (m + n) n` MATCH_MP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONV_TAC (LAND_CONV (REWR_CONV ADD_SYM)) THEN
    ASM_REWRITE_TAC [LT_ADD; LT_NZ]]);;

let gcd_exists = prove
  (`!a b. ?g.
      divides g a /\ divides g b /\
      !c. divides c a /\ divides c b ==> divides c g`,
   MATCH_MP_TAC gcd_induction THEN
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `g:num` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `b : num` THEN
    REWRITE_TAC [divides_zero; divides_refl];
    EXISTS_TAC `g : num` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC divides_add THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `divides c ((a + b) - b)`
       (fun th -> MP_TAC th THEN REWRITE_TAC [ADD_SUB]) THEN
     MATCH_MP_TAC divides_sub THEN
     ASM_REWRITE_TAC [LE_ADDR]]]);;

let (gcd_divides1,gcd_divides2,gcd_greatest) =
    let def = new_specification ["gcd"]
                (REWRITE_RULE [SKOLEM_THM] gcd_exists) in
    let def = REWRITE_RULE [FORALL_AND_THM] def in
    let div1 = CONJUNCT1 def in
    let def = CONJUNCT2 def in
    let div2 = CONJUNCT1 def in
    let def = CONJUNCT2 def in
    (div1,div2,def);;

export_thm gcd_divides1;;
export_thm gcd_divides2;;
export_thm gcd_greatest;;

logfile "natural-gcd-thm";;

(***
let gcd_recursion = prove
  (`!a b.
      gcd a b =
        if a = 0 then b
        else if a <= b then gcd a (b - a)
        else gcd b a`,
***)

logfile_end ();;

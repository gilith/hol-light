(* ------------------------------------------------------------------------- *)
(* Natural number greatest common divisor.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "natural-gcd-def";;

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

let gcd_unique = prove
  (`!a b g.
      divides g a /\ divides g b /\
      (!c. divides c a /\ divides c b ==> divides c g) ==>
      gcd a b = g`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [gcd_divides1; gcd_divides2];
    MATCH_MP_TAC gcd_greatest THEN
    ASM_REWRITE_TAC []]);;

export_thm gcd_unique;;

let gcd_refl = prove
  (`!a. gcd a a = a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [divides_refl]);;

export_thm gcd_refl;;

let gcd_comm = prove
  (`!a b. gcd a b = gcd b a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [gcd_divides1; gcd_divides2] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_greatest THEN
   ASM_REWRITE_TAC []);;

export_thm gcd_comm;;

let gcd_assoc = prove
  (`!a b c. gcd (gcd a b) c = gcd a (gcd b c)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC gcd_greatest THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd a b` THEN
     REWRITE_TAC [gcd_divides1];
     MATCH_MP_TAC gcd_greatest THEN
     STRIP_TAC THENL
     [MATCH_MP_TAC divides_trans THEN
      EXISTS_TAC `gcd a b` THEN
      REWRITE_TAC [gcd_divides1; gcd_divides2];
      REWRITE_TAC [gcd_divides2]]];
    MATCH_MP_TAC gcd_greatest THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC gcd_greatest THEN
     STRIP_TAC THENL
     [REWRITE_TAC [gcd_divides1];
      MATCH_MP_TAC divides_trans THEN
      EXISTS_TAC `gcd b c` THEN
      REWRITE_TAC [gcd_divides1; gcd_divides2]];
     MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd b c` THEN
     REWRITE_TAC [gcd_divides2]]]);;

export_thm gcd_assoc;;

let zero_gcd = prove
  (`!a. gcd 0 a = a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [zero_divides; divides_zero; divides_refl]);;

export_thm zero_gcd;;

let gcd_zero = prove
  (`!a. gcd a 0 = a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [zero_divides; divides_zero; divides_refl]);;

export_thm gcd_zero;;

let one_gcd = prove
  (`!a. gcd 1 a = 1`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [one_divides; divides_one; divides_refl] THEN
   REPEAT STRIP_TAC);;

export_thm one_gcd;;

let gcd_one = prove
  (`!a. gcd a 1 = 1`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC one_gcd);;

export_thm gcd_one;;

let gcd_addl = prove
  (`!a b. gcd a (a + b) = gcd a b`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [gcd_divides1] THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_add THEN
    REWRITE_TAC [gcd_divides1; gcd_divides2];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC gcd_greatest THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `divides c ((a + b) - a)`
      (fun th -> MP_TAC th THEN REWRITE_TAC [ADD_SUB2]) THEN
    MATCH_MP_TAC divides_sub THEN
    ASM_REWRITE_TAC [LE_ADD]]);;

export_thm gcd_addl;;

let gcd_addr = prove
  (`!a b. gcd a (b + a) = gcd a b`,
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   ACCEPT_TAC gcd_addl);;

export_thm gcd_addr;;

let addl_gcd = prove
  (`!a b. gcd (b + a) b = gcd a b`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gcd_comm] THEN
   MATCH_ACCEPT_TAC gcd_addl);;

export_thm addl_gcd;;

let addr_gcd = prove
  (`!a b. gcd (a + b) b = gcd a b`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gcd_comm] THEN
   MATCH_ACCEPT_TAC gcd_addr);;

export_thm addr_gcd;;

let gcd_sub = prove
  (`!a b. a <= b ==> gcd a (b - a) = gcd a b`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [gcd_divides1] THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_sub THEN
    ASM_REWRITE_TAC [gcd_divides1; gcd_divides2];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC gcd_greatest THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `divides c ((b - a) + a)` MP_TAC THENL
    [MATCH_MP_TAC divides_add THEN
     ASM_REWRITE_TAC [];
     MATCH_MP_TAC EQ_IMP THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC SUB_ADD THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm gcd_sub;;

let sub_gcd = prove
  (`!a b. b <= a ==> gcd (a - b) b = gcd a b`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gcd_comm] THEN
   MATCH_ACCEPT_TAC gcd_sub);;

export_thm sub_gcd;;

let gcd_recursion = prove
  (`!a b.
      gcd a b =
        if a = 0 then b
        else if a <= b then gcd a (b - a)
        else gcd b a`,
   REPEAT GEN_TAC THEN
   COND_CASES_TAC THENL
   [ASM_REWRITE_TAC [zero_gcd];
    COND_CASES_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC gcd_sub THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_ACCEPT_TAC gcd_comm]]);;

export_thm gcd_recursion;;

(***
let egcd_exists = prove
  (`!a b. ?s t. s * a + gcd a b = t * b`
***)

logfile_end ();;

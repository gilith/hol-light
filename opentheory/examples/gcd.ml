(* ------------------------------------------------------------------------- *)
(* Natural number greatest common divisor.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "natural-gcd-def";;

let (gcd_divides1,gcd_divides2,gcd_greatest_imp) =
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
export_thm gcd_greatest_imp;;

logfile "natural-gcd-thm";;

let gcd_greatest = prove
  (`!a b c. divides c (gcd a b) <=> divides c a /\ divides c b`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `gcd a b` THEN
    ASM_REWRITE_TAC [gcd_divides1; gcd_divides2];
    MATCH_ACCEPT_TAC gcd_greatest_imp]);;

export_thm gcd_greatest;;

let gcd_divides1_imp = prove
  (`!a b c. divides b a ==> divides (gcd b c) a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `b : num` THEN
   ASM_REWRITE_TAC [gcd_divides1]);;

export_thm gcd_divides1_imp;;

let gcd_divides2_imp = prove
  (`!a b c. divides b a ==> divides (gcd c b) a`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `b : num` THEN
   ASM_REWRITE_TAC [gcd_divides2]);;

export_thm gcd_divides2_imp;;

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
    MATCH_MP_TAC gcd_greatest_imp THEN
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
   MATCH_MP_TAC gcd_greatest_imp THEN
   ASM_REWRITE_TAC []);;

export_thm gcd_comm;;

let gcd_assoc = prove
  (`!a b c. gcd (gcd a b) c = gcd a (gcd b c)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC gcd_greatest_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd a b` THEN
     REWRITE_TAC [gcd_divides1];
     MATCH_MP_TAC gcd_greatest_imp THEN
     STRIP_TAC THENL
     [MATCH_MP_TAC divides_trans THEN
      EXISTS_TAC `gcd a b` THEN
      REWRITE_TAC [gcd_divides1; gcd_divides2];
      REWRITE_TAC [gcd_divides2]]];
    MATCH_MP_TAC gcd_greatest_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC gcd_greatest_imp THEN
     STRIP_TAC THENL
     [REWRITE_TAC [gcd_divides1];
      MATCH_MP_TAC divides_trans THEN
      EXISTS_TAC `gcd b c` THEN
      REWRITE_TAC [gcd_divides1; gcd_divides2]];
     MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `gcd b c` THEN
     REWRITE_TAC [gcd_divides2]]]);;

export_thm gcd_assoc;;

let divides_gcd = prove
  (`!a b. gcd a b = a <=> divides a b`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_ACCEPT_TAC gcd_divides2;
    STRIP_TAC THEN
    MATCH_MP_TAC gcd_unique THEN
    ASM_REWRITE_TAC [divides_refl] THEN
    REPEAT STRIP_TAC]);;

export_thm divides_gcd;;

let gcd_divides = prove
  (`!a b. gcd b a = a <=> divides a b`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC divides_gcd);;

export_thm gcd_divides;;

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

let gcd_is_zero = prove
  (`!a b. gcd a b = 0 <=> a = 0 /\ b = 0`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_gcd];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM zero_divides] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   MATCH_ACCEPT_TAC gcd_divides1);;

export_thm gcd_is_zero;;

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

let gcd_is_one = prove
  (`!a b. (!c. divides c a /\ divides c b ==> c = 1) ==> gcd a b = 1`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   ASM_REWRITE_TAC [divides_one; one_divides]);;

export_thm gcd_is_one;;

let gcd_addl = prove
  (`!a b. gcd a (a + b) = gcd a b`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC gcd_unique THEN
   REWRITE_TAC [gcd_divides1] THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC divides_add THEN
    REWRITE_TAC [gcd_divides1; gcd_divides2];
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC gcd_greatest_imp THEN
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
    MATCH_MP_TAC gcd_greatest_imp THEN
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

let egcd_exists = prove
  (`!a b. ?s t. dist (s * a) (t * b) = gcd a b`,
   MATCH_MP_TAC gcd_induction THEN
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `0` THEN
    EXISTS_TAC `1` THEN
    REWRITE_TAC [zero_gcd; ONE_MULT; ZERO_MULT; DIST_LZERO];
    EXISTS_TAC `t : num` THEN
    EXISTS_TAC `s : num` THEN
    ONCE_REWRITE_TAC [gcd_comm; DIST_SYM] THEN
    FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `(s : num) + t` THEN
    EXISTS_TAC `t : num` THEN
    ASM_REWRITE_TAC
      [gcd_addr; RIGHT_ADD_DISTRIB; LEFT_ADD_DISTRIB; DIST_RADD]]);;

export_thm egcd_exists;;

let egcd_exists_nonzero1 = prove
  (`!a b. ~(a = 0) ==> ?s t. t * b + gcd a b = s * a`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`a : num`; `b : num`] egcd_exists) THEN
   REWRITE_TAC [DIST_CASES] THEN
   STRIP_TAC THENL
   [ALL_TAC;
    EXISTS_TAC `s : num` THEN
    EXISTS_TAC `t : num` THEN
    FIRST_ASSUM ACCEPT_TAC] THEN
   MP_TAC (SPECL [`a : num`; `b : num`] gcd_divides1) THEN
   REWRITE_TAC [divides_def] THEN
   DISCH_THEN (X_CHOOSE_THEN `k : num` MP_TAC) THEN
   MP_TAC (SPEC `k : num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [ZERO_MULT];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   EXISTS_TAC `SUC (s * (n : num))` THEN
   EXISTS_TAC `n * (t : num)` THEN
   REWRITE_TAC [SUC_MULT] THEN
   POP_ASSUM (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [SUC_MULT] THEN
   REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [GSYM MULT_ASSOC] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB; EQ_ADD_RCANCEL] THEN
   REWRITE_TAC [MULT_ASSOC] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_ACCEPT_TAC MULT_SYM);;

export_thm egcd_exists_nonzero1;;

let egcd_exists_nonzero2 = prove
  (`!a b. ~(a = 0) ==> ?s t. t * b + gcd b a = s * a`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC egcd_exists_nonzero1);;

export_thm egcd_exists_nonzero2;;

let mult_gcd_cancel = prove
  (`!a b c. gcd (a * b) (a * c) = a * gcd b c`,
   GEN_TAC THEN
   MATCH_MP_TAC gcd_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [zero_gcd; MULT_0];
    ONCE_REWRITE_TAC [gcd_comm] THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [gcd_addr; LEFT_ADD_DISTRIB] THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm mult_gcd_cancel;;

let gcd_mult_cancel = prove
  (`!a b c. gcd (b * a) (c * a) = gcd b c * a`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC mult_gcd_cancel);;

export_thm gcd_mult_cancel;;

let mult1_coprime = prove
  (`!a b c. gcd (a * b) c = 1 ==> gcd b c = 1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM divides_one] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC gcd_greatest_imp THEN
   REWRITE_TAC [gcd_divides2] THEN
   MATCH_MP_TAC divides_mult2 THEN
   MATCH_ACCEPT_TAC gcd_divides1);;

export_thm mult1_coprime;;

let mult2_coprime = prove
  (`!a b c. gcd (b * a) c = 1 ==> gcd b c = 1`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC mult1_coprime);;

export_thm mult2_coprime;;

let coprime_mult1 = prove
  (`!a b c. gcd b (a * c) = 1 ==> gcd b c = 1`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [gcd_comm] THEN
   MATCH_ACCEPT_TAC mult1_coprime);;

export_thm coprime_mult1;;

let coprime_mult2 = prove
  (`!a b c. gcd b (c * a) = 1 ==> gcd b c = 1`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC coprime_mult1);;

export_thm coprime_mult2;;

let coprime_induction = prove
  (`!p.
      p 0 0 /\
      (!a b. gcd a b = 1 ==> p a b) /\
      (!c a b. ~(c = 0) /\ p a b ==> p (c * a) (c * b)) ==>
      !a b. p a b`,
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `gcd a b = 0` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [gcd_is_zero] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    ALL_TAC] THEN
   MP_TAC (SPECL [`a:num`; `b:num`] gcd_divides1) THEN
   REWRITE_TAC [divides_def] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `s:num`
        (fun th -> SUBST1_TAC (SYM th) THEN ASSUME_TAC th)) THEN
   MP_TAC (SPECL [`a:num`; `b:num`] gcd_divides2) THEN
   REWRITE_TAC [divides_def] THEN
   DISCH_THEN
     (X_CHOOSE_THEN `t:num`
        (fun th ->
           CONV_TAC (RAND_CONV (REWR_CONV (SYM th))) THEN ASSUME_TAC th)) THEN
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC gcd_is_one THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM divides_one] THEN
   MP_TAC (SPECL [`gcd a b`; `c : num`; `1`] divides_mult_cancel) THEN
   ASM_REWRITE_TAC [ONE_MULT] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC gcd_greatest_imp THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    ASM_REWRITE_TAC [divides_mult_cancel];
    FIRST_X_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    ASM_REWRITE_TAC [divides_mult_cancel]]);;

export_thm coprime_induction;;

let egcd_divides = prove
  (`!a b s t. divides (gcd a b) (dist (s * a) (t * b))`,
   MATCH_MP_TAC coprime_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [MULT_0; DIST_REFL; divides_zero];
    ASM_REWRITE_TAC [one_divides];
    REWRITE_TAC [mult_gcd_cancel; MULT_ASSOC] THEN
    CONV_TAC (RAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
    CONV_TAC (RAND_CONV (LAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
    REWRITE_TAC [GSYM MULT_ASSOC; GSYM DIST_LMUL; mult_divides_cancel] THEN
    ASM_REWRITE_TAC []]);;

export_thm egcd_divides;;

let coprime_egcd = prove
  (`!a b s t. dist (s * a) (t * b) = 1 ==> gcd a b = 1`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [GSYM divides_one] THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   MATCH_ACCEPT_TAC egcd_divides);;

export_thm coprime_egcd;;

let square_coprime_imp = prove
  (`!a b. gcd a b = 1 ==> gcd (a * a) b = 1`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [MULT_0];
    ALL_TAC] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`a : num`; `b : num`] egcd_exists_nonzero1) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC coprime_egcd THEN
   EXISTS_TAC `s * s : num` THEN
   EXISTS_TAC `(t * b) * t + t + t : num` THEN
   REWRITE_TAC [DIST_CASES] THEN
   DISJ2_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC EQ_TRANS THEN
   EXISTS_TAC `(s * a) * (s * a) : num` THEN
   CONJ_TAC THENL
   [REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC [MULT_ASSOC] THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC MULT_SYM;
    ALL_TAC] THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ONE_MULT; MULT_1] THEN
   REWRITE_TAC [MULT_ASSOC; ADD_ASSOC]);;

export_thm square_coprime_imp;;

let coprime_square_imp = prove
  (`!a b. gcd b a = 1 ==> gcd b (a * a) = 1`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC square_coprime_imp);;

export_thm coprime_square_imp;;

let coprime_mult_imp = prove
  (`!a b c. gcd a b = 1 /\ gcd a c = 1 ==> gcd a (b * c) = 1`,
   GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [zero_gcd] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [MULT_1];
    ALL_TAC] THEN
   MATCH_MP_TAC coprime_induction THEN
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [MULT_0];
    REPEAT (POP_ASSUM MP_TAC) THEN
    ASM_CASES_TAC `b' = 0` THENL
    [ASM_REWRITE_TAC [MULT_0] THEN
     REPEAT STRIP_TAC;
     ALL_TAC] THEN
    ASM_CASES_TAC `b = 0` THENL
    [ASM_REWRITE_TAC [ZERO_MULT] THEN
     REPEAT STRIP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`b' : num`; `a : num`] egcd_exists_nonzero2) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    MP_TAC (SPECL [`b : num`; `a : num`] egcd_exists_nonzero2) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    MP_TAC (SPECL [`b : num`; `b' : num`] egcd_exists) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `x : num` (X_CHOOSE_THEN `y : num` ASSUME_TAC)) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `s : num` (X_CHOOSE_THEN `t : num` ASSUME_TAC)) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `p : num` (X_CHOOSE_THEN `q : num` ASSUME_TAC)) THEN
    MATCH_MP_TAC coprime_egcd THEN
    EXISTS_TAC `dist (x * b * q) (y * b' * t)` THEN
    EXISTS_TAC `dist (x * p) (y * s)` THEN
    REWRITE_TAC [DIST_RMUL] THEN
    SUBGOAL_THEN
      `(x * p) * (b * b') = (x * b * q) * a + x * b : num` SUBST1_TAC THENL
    [MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `(x * b) * (p * b') : num` THEN
     CONJ_TAC THENL
     [REWRITE_TAC [MULT_ASSOC] THEN
      AP_THM_TAC THEN
      AP_TERM_TAC THEN
      REWRITE_TAC [GSYM MULT_ASSOC] THEN
      AP_TERM_TAC THEN
      MATCH_ACCEPT_TAC MULT_SYM;
      ALL_TAC] THEN
     FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_1; ONE_MULT] THEN
     REWRITE_TAC [EQ_ADD_RCANCEL; GSYM MULT_ASSOC];
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN
      `(y * s) * (b * b') = (y * b' * t) * a + y * b' : num` SUBST1_TAC THENL
    [MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `y * (s * b) * b' : num` THEN
     CONJ_TAC THENL
     [REWRITE_TAC [MULT_ASSOC];
      ALL_TAC] THEN
     FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_1; ONE_MULT] THEN
     REWRITE_TAC [EQ_ADD_RCANCEL; GSYM MULT_ASSOC] THEN
     AP_TERM_TAC THEN
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
     REWRITE_TAC [MULT_ASSOC];
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM
      (STRIP_ASSUME_TAC o
       ONCE_REWRITE_RULE [ADD_SYM] o
       REWRITE_RULE [DIST_CASES]) THENL
    [FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [ADD_ASSOC; DIST_RADD; DIST_DIST_SUC];
     FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [ADD_ASSOC; DIST_RADD] THEN
     CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV DIST_SYM))) THEN
     CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV DIST_SYM))) THEN
     MATCH_ACCEPT_TAC DIST_DIST_SUC];
    UNDISCH_TAC `gcd a b = 1 /\ gcd a b' = 1 ==> gcd a (b * b') = 1` THEN
    ANTS_TAC THENL
    [CONJ_TAC THENL
     [MATCH_MP_TAC coprime_mult1 THEN
      EXISTS_TAC `c : num` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC coprime_mult1 THEN
      EXISTS_TAC `c : num` THEN
      FIRST_ASSUM ACCEPT_TAC];
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    SUBGOAL_THEN `gcd (c * c) a = 1` MP_TAC THENL
    [MATCH_MP_TAC square_coprime_imp THEN
     ONCE_REWRITE_TAC [gcd_comm] THEN
     MATCH_MP_TAC coprime_mult2 THEN
     EXISTS_TAC `b : num` THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    POP_ASSUM (K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`a : num`; `b * b' : num`] egcd_exists_nonzero1) THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM (K ALL_TAC) THEN
    MP_TAC (SPECL [`c * c : num`; `a : num`] egcd_exists_nonzero1) THEN
    ASM_REWRITE_TAC [MULT_EQ_0] THEN
    POP_ASSUM_LIST (K ALL_TAC) THEN
    DISCH_THEN
      (X_CHOOSE_THEN `p : num` (X_CHOOSE_THEN `q : num` ASSUME_TAC)) THEN
    STRIP_TAC THEN
    MATCH_MP_TAC coprime_egcd THEN
    EXISTS_TAC `q * t * b * b' + s : num` THEN
    EXISTS_TAC `p * t : num` THEN
    REWRITE_TAC [DIST_CASES] THEN
    DISJ2_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    REWRITE_TAC [RIGHT_ADD_DISTRIB] THEN
    FIRST_X_ASSUM (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [ADD_ASSOC; EQ_ADD_RCANCEL] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(q * a + 1) * (t * b * b') : num` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [RIGHT_ADD_DISTRIB; EQ_ADD_RCANCEL; ONE_MULT] THEN
     REWRITE_TAC [GSYM MULT_ASSOC] THEN
     AP_TERM_TAC THEN
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
     REWRITE_TAC [MULT_ASSOC];
     FIRST_X_ASSUM SUBST1_TAC THEN
     REWRITE_TAC [GSYM MULT_ASSOC] THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [MULT_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
     REWRITE_TAC [MULT_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [GSYM MULT_ASSOC] THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC MULT_SYM]]);;

export_thm coprime_mult_imp;;

let mult_coprime_imp = prove
  (`!a b c. gcd b a = 1 /\ gcd c a = 1 ==> gcd (b * c) a = 1`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC coprime_mult_imp);;

export_thm mult_coprime_imp;;

let coprime_mult = prove
  (`!a b c. gcd a (b * c) = 1 <=> gcd a b = 1 /\ gcd a c = 1`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
    [MATCH_MP_TAC coprime_mult2 THEN
     EXISTS_TAC `c : num` THEN
     FIRST_ASSUM ACCEPT_TAC;
     MATCH_MP_TAC coprime_mult1 THEN
     EXISTS_TAC `b : num` THEN
     FIRST_ASSUM ACCEPT_TAC];
    MATCH_ACCEPT_TAC coprime_mult_imp]);;

export_thm coprime_mult;;

let mult_coprime = prove
  (`!a b c. gcd (b * c) a = 1 <=> gcd b a = 1 /\ gcd c a = 1`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC coprime_mult);;

export_thm mult_coprime;;

let square_coprime = prove
  (`!a b. gcd (a * a) b = 1 <=> gcd a b = 1`,
   REWRITE_TAC [mult_coprime]);;

export_thm square_coprime;;

let coprime_square = prove
  (`!a b. gcd b (a * a) = 1 <=> gcd b a = 1`,
   REWRITE_TAC [coprime_mult]);;

export_thm coprime_square;;

let coprime_gcd_mult2 = prove
  (`!a b c. gcd a b = 1 ==> gcd a (b * c) = gcd a c`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   GEN_TAC THEN
   MATCH_MP_TAC coprime_induction THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [MULT_0];
    ASM_REWRITE_TAC [coprime_mult];
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV MULT_ASSOC))) THEN
    CONV_TAC (LAND_CONV (RAND_CONV (LAND_CONV (REWR_CONV MULT_SYM)))) THEN
    REWRITE_TAC [GSYM MULT_ASSOC; mult_gcd_cancel] THEN
    AP_TERM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC mult1_coprime THEN
    EXISTS_TAC `c : num` THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm coprime_gcd_mult2;;

let coprime_gcd_mult1 = prove
  (`!a b c. gcd a b = 1 ==> gcd a (c * b) = gcd a c`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC coprime_gcd_mult2);;

export_thm coprime_gcd_mult1;;

let coprime_mult1_gcd = prove
  (`!a b c. gcd b a = 1 ==> gcd (c * b) a = gcd c a`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC coprime_gcd_mult1);;

export_thm coprime_mult1_gcd;;

let coprime_mult2_gcd = prove
  (`!a b c. gcd b a = 1 ==> gcd (b * c) a = gcd c a`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC coprime_gcd_mult2);;

export_thm coprime_mult2_gcd;;

let coprime_mult_divides = prove
  (`!a b c. gcd b c = 1 /\ divides b a /\ divides c a ==> divides (b * c) a`,
   REPEAT STRIP_TAC THEN
   UNDISCH_THEN `divides b a`
     (X_CHOOSE_THEN `k:num` SUBST_VAR_TAC o
      ONCE_REWRITE_RULE [MULT_SYM] o
      REWRITE_RULE [divides_def]) THEN
   REWRITE_TAC [mult_divides_cancel] THEN
   ASM_CASES_TAC `b = 0` THEN
   ASM_REWRITE_TAC [] THEN
   UNDISCH_TAC `divides c (b * k)` THEN
   REWRITE_TAC [GSYM divides_gcd] THEN
   DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC coprime_gcd_mult2 THEN
   ONCE_REWRITE_TAC [gcd_comm] THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm coprime_mult_divides;;

let divides_gcd_mult = prove
  (`!a b c. divides (gcd a (b * c)) (gcd a b * gcd a c)`,
   MATCH_MP_TAC coprime_induction THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC [zero_gcd; ZERO_MULT; divides_refl];
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [ONE_MULT] THEN
    MATCH_MP_TAC divides_refl_imp THEN
    MATCH_MP_TAC coprime_gcd_mult2 THEN
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `k : num` THEN
    X_GEN_TAC `a : num` THEN
    X_GEN_TAC `b : num` THEN
    STRIP_TAC THEN
    X_GEN_TAC `c : num` THEN
    ASM_REWRITE_TAC [mult_gcd_cancel; GSYM MULT_ASSOC; mult_divides_cancel] THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `gcd a b * gcd a c` THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [mult_divides_cancel] THEN
    DISJ2_TAC THEN
    REWRITE_TAC [gcd_greatest; gcd_divides2] THEN
    MATCH_MP_TAC divides_mult2 THEN
    MATCH_ACCEPT_TAC gcd_divides1]);;

export_thm divides_gcd_mult;;

logfile "natural-gcd-lcm-def";;

let (zero_lcm,lcm_gcd) =
  let def = new_definition
    `!a b. lcm a b = if a = 0 then 0 else (a * b) DIV (gcd a b)` in
  let zero = prove
    (`!a. lcm 0 a = 0`,
     REWRITE_TAC [def])
  and mult = prove
    (`!a b. lcm a b * gcd a b = a * b`,
     REPEAT GEN_TAC THEN
     REWRITE_TAC [def] THEN
     ASM_CASES_TAC `a = 0` THENL
     [ASM_REWRITE_TAC [ZERO_MULT];
      ALL_TAC] THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `~(gcd a b = 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC [gcd_is_zero];
      ALL_TAC] THEN
     MP_TAC (SPECL [`gcd a b`; `a * (b:num)`] divides_div) THEN
     ANTS_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     MATCH_MP_TAC divides_mult1 THEN
     MATCH_ACCEPT_TAC gcd_divides1) in
  (zero,mult);;

export_thm zero_lcm;;
export_thm lcm_gcd;;

logfile "natural-gcd-lcm-thm";;

let lcm_comm = prove
  (`!a b. lcm a b = lcm b a`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `gcd a b = 0` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [gcd_is_zero] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [zero_lcm];
    MP_TAC (SPECL [`lcm a b`; `lcm b a`; `gcd a b`] EQ_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV gcd_comm))) THEN
    REWRITE_TAC [lcm_gcd] THEN
    MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm lcm_comm;;

let lcm_zero = prove
  (`!a. lcm a 0 = 0`,
   ONCE_REWRITE_TAC [lcm_comm] THEN
   ACCEPT_TAC zero_lcm);;

export_thm lcm_zero;;

let divides_lcm1 = prove
  (`!a b. divides a (lcm a b)`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a = 0` THENL
   [ASM_REWRITE_TAC [divides_zero; zero_lcm];
    ALL_TAC] THEN
   SUBGOAL_THEN `~(gcd a b = 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC [gcd_is_zero];
    ALL_TAC] THEN
   MP_TAC (SPECL [`gcd a b`; `a : num`; `lcm a b`] divides_mult_cancel) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [lcm_gcd] THEN
   MATCH_MP_TAC mult_divides_mult THEN
   REWRITE_TAC [gcd_divides2; divides_refl]);;

export_thm divides_lcm1;;

let divides_lcm2 = prove
  (`!a b. divides b (lcm a b)`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [lcm_comm] THEN
   MATCH_ACCEPT_TAC divides_lcm1);;

export_thm divides_lcm2;;

let divides_lcm1_imp = prove
  (`!a b c. divides a b ==> divides a (lcm b c)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `b : num` THEN
   ASM_REWRITE_TAC [divides_lcm1]);;

export_thm divides_lcm1_imp;;

let divides_lcm2_imp = prove
  (`!a b c. divides a b ==> divides a (lcm c b)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_trans THEN
   EXISTS_TAC `b : num` THEN
   ASM_REWRITE_TAC [divides_lcm2]);;

export_thm divides_lcm2_imp;;

let mult_lcm_cancel = prove
  (`!a b c. lcm (a * b) (a * c) = a * lcm b c`,
   REPEAT GEN_TAC THEN
   ASM_CASES_TAC `a * gcd b c = 0` THENL
   [POP_ASSUM MP_TAC THEN
    REWRITE_TAC [MULT_EQ_0; gcd_is_zero] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [ZERO_MULT; lcm_zero; MULT_0];
    MP_TAC (SPECL [`lcm (a * b) (a * c)`; `a * lcm b c`; `a * gcd b c`]
                  EQ_MULT_RCANCEL) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV (GSYM mult_gcd_cancel)))) THEN
    REWRITE_TAC [lcm_gcd] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV MULT_SYM))) THEN
    REWRITE_TAC [MULT_ASSOC; lcm_gcd] THEN
    REWRITE_TAC [GSYM MULT_ASSOC] THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm mult_lcm_cancel;;

let lcm_mult_cancel = prove
  (`!a b c. lcm (b * a) (c * a) = lcm b c * a`,
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   ACCEPT_TAC mult_lcm_cancel);;

export_thm lcm_mult_cancel;;

let lcm_least_imp = prove
  (`!a b c. divides a c /\ divides b c ==> divides (lcm a b) c`,
   MATCH_MP_TAC coprime_induction THEN
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [lcm_zero];
    MP_TAC (SPECL [`gcd a b`; `lcm a b`; `c : num`] divides_mult_cancel) THEN
    REWRITE_TAC [lcm_gcd] THEN
    ASM_REWRITE_TAC [MULT_1] THEN
    NUM_REDUCE_TAC THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC coprime_mult_divides THEN
    ASM_REWRITE_TAC [];
    SUBGOAL_THEN `divides c c'` MP_TAC THENL
    [MATCH_MP_TAC mult1_divides THEN
     EXISTS_TAC `a : num` THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    DISCH_THEN
      (X_CHOOSE_THEN `k:num` SUBST_VAR_TAC o
       REWRITE_RULE [MULT_SYM] o
       REWRITE_RULE [divides_def]) THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [mult_divides_cancel; mult_lcm_cancel; IMP_IMP]]);;

export_thm lcm_least_imp;;

let lcm_least = prove
  (`!a b c. divides (lcm a b) c <=> divides a c /\ divides b c`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `lcm a b` THEN
    ASM_REWRITE_TAC [divides_lcm1; divides_lcm2];
    MATCH_ACCEPT_TAC lcm_least_imp]);;

export_thm lcm_least;;

let lcm_unique = prove
  (`!a b l.
      divides a l /\ divides b l /\
      (!c. divides a c /\ divides b c ==> divides l c) ==>
      lcm a b = l`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC lcm_least_imp THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [divides_lcm1; divides_lcm2]]);;

export_thm lcm_unique;;

let one_lcm = prove
  (`!a. lcm 1 a = a`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC lcm_unique THEN
   REWRITE_TAC [one_divides; divides_refl]);;

export_thm one_lcm;;

let lcm_one = prove
  (`!a. lcm a 1 = a`,
   ONCE_REWRITE_TAC [lcm_comm] THEN
   ACCEPT_TAC one_lcm);;

export_thm lcm_one;;

let lcm_is_one = prove
  (`!a b. lcm a b = 1 <=> a = 1 /\ b = 1`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [REWRITE_TAC [GSYM divides_one] THEN
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `lcm a b` THEN
    ASM_REWRITE_TAC [divides_lcm1; divides_lcm2];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [lcm_one]]);;

export_thm lcm_is_one;;

let lcm_is_zero = prove
  (`!a b. lcm a b = 0 <=> a = 0 \/ b = 0`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    REWRITE_TAC [GSYM MULT_EQ_0] THEN
    ONCE_REWRITE_TAC [GSYM lcm_gcd] THEN
    ASM_REWRITE_TAC [ZERO_MULT];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [zero_lcm; lcm_zero]]);;

export_thm lcm_is_zero;;

let lcm_refl = prove
  (`!a. lcm a a = a`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC lcm_unique THEN
   REWRITE_TAC [divides_refl]);;

export_thm lcm_refl;;

let lcm_assoc = prove
  (`!a b c. lcm (lcm a b) c = lcm a (lcm b c)`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [MATCH_MP_TAC lcm_least_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC lcm_least_imp THEN
     STRIP_TAC THENL
     [MATCH_ACCEPT_TAC divides_lcm1;
      MATCH_MP_TAC divides_lcm2_imp THEN
      MATCH_ACCEPT_TAC divides_lcm1];
     MATCH_MP_TAC divides_lcm2_imp THEN
     MATCH_ACCEPT_TAC divides_lcm2];
    MATCH_MP_TAC lcm_least_imp THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_lcm1_imp THEN
     MATCH_ACCEPT_TAC divides_lcm1;
     MATCH_MP_TAC lcm_least_imp THEN
     STRIP_TAC THENL
     [MATCH_MP_TAC divides_lcm1_imp THEN
      MATCH_ACCEPT_TAC divides_lcm2;
      MATCH_ACCEPT_TAC divides_lcm2]]]);;

export_thm lcm_assoc;;

let divides_lcm = prove
  (`!a b. lcm a b = a <=> divides b a`,
   REPEAT GEN_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_ACCEPT_TAC divides_lcm2;
    STRIP_TAC THEN
    MATCH_MP_TAC lcm_unique THEN
    ASM_REWRITE_TAC [divides_refl] THEN
    REPEAT STRIP_TAC]);;

export_thm divides_lcm;;

let lcm_divides = prove
  (`!a b. lcm b a = a <=> divides b a`,
   ONCE_REWRITE_TAC [lcm_comm] THEN
   ACCEPT_TAC divides_lcm);;

export_thm lcm_divides;;

let lcm_left_distrib = prove
  (`!a b c. gcd a (lcm b c) = lcm (gcd a b) (gcd a c)`,
   REPEAT GEN_TAC THEN
   MATCH_MP_TAC divides_antisym THEN
   STRIP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC [lcm_least; gcd_greatest; gcd_divides1; gcd_divides2] THEN
    STRIP_TAC THENL
    [MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `b : num` THEN
     REWRITE_TAC [gcd_divides2; divides_lcm1];
     MATCH_MP_TAC divides_trans THEN
     EXISTS_TAC `c : num` THEN
     REWRITE_TAC [gcd_divides2; divides_lcm2]]] THEN
   SUBGOAL_THEN `?ac. gcd a c = ac` (CHOOSE_THEN MP_TAC) THENL
   [EXISTS_TAC `gcd a c` THEN
    REFL_TAC;
    ALL_TAC] THEN
   SUBGOAL_THEN `?ab. gcd a b = ab` (CHOOSE_THEN MP_TAC) THENL
   [EXISTS_TAC `gcd a b` THEN
    REFL_TAC;
    ALL_TAC] THEN
   SPEC_TAC (`c : num`, `c : num`) THEN
   SPEC_TAC (`b : num`, `b : num`) THEN
   SPEC_TAC (`a : num`, `a : num`) THEN
   SPEC_TAC (`ac : num`, `ac : num`) THEN
   SPEC_TAC (`ab : num`, `ab : num`) THEN
   MATCH_MP_TAC coprime_induction THEN
   REPEAT CONJ_TAC THENL
   [REWRITE_TAC [gcd_is_zero] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [gcd_zero; lcm_zero; divides_refl];
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    MP_TAC (SPECL [`ab : num`; `ac : num`] lcm_gcd) THEN
    ASM_REWRITE_TAC [MULT_1] THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC divides_trans THEN
    EXISTS_TAC `gcd a (b * c)` THEN
    CONJ_TAC THENL
    [REWRITE_TAC [gcd_greatest; gcd_divides1] THEN
     MATCH_MP_TAC gcd_divides2_imp THEN
     ONCE_REWRITE_TAC [GSYM lcm_gcd] THEN
     MATCH_MP_TAC divides_mult1 THEN
     MATCH_ACCEPT_TAC divides_refl;
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
     MATCH_ACCEPT_TAC divides_gcd_mult];
    X_GEN_TAC `k : num` THEN
    X_GEN_TAC `ab : num` THEN
    X_GEN_TAC `ac : num` THEN
    STRIP_TAC THEN
    X_GEN_TAC `a : num` THEN
    X_GEN_TAC `b : num` THEN
    X_GEN_TAC `c : num` THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `divides k (gcd a b) /\ divides k (gcd a c)` MP_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     MATCH_MP_TAC divides_mult1 THEN
     MATCH_ACCEPT_TAC divides_refl;
     ALL_TAC] THEN
    REWRITE_TAC [gcd_greatest] THEN
    CONV_TAC (LAND_CONV (REWRITE_CONV [divides_def])) THEN
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [MULT_SYM])) THEN
    REWRITE_TAC [IMP_CONJ] THEN
    DISCH_THEN (K ALL_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `b' : num` SUBST_VAR_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `c' : num` SUBST_VAR_TAC) THEN
    DISCH_THEN (X_CHOOSE_THEN `a' : num` SUBST_VAR_TAC) THEN
    POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC
      [mult_gcd_cancel; mult_lcm_cancel; EQ_MULT_LCANCEL;
       mult_divides_cancel]]);;

export_thm lcm_left_distrib;;

let lcm_right_distrib = prove
  (`!a b c. gcd (lcm b c) a = lcm (gcd b a) (gcd c a)`,
   ONCE_REWRITE_TAC [gcd_comm] THEN
   ACCEPT_TAC lcm_left_distrib);;

export_thm lcm_right_distrib;;

let gcd_left_distrib = prove
  (`!a b c. lcm a (gcd b c) = gcd (lcm a b) (lcm a c)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [lcm_left_distrib] THEN
   REWRITE_TAC [lcm_right_distrib; gcd_refl; GSYM lcm_assoc] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   REWRITE_TAC
     [lcm_assoc; divides_lcm; lcm_least; gcd_divides1; gcd_divides2]);;

export_thm gcd_left_distrib;;

let gcd_right_distrib = prove
  (`!a b c. lcm (gcd b c) a = gcd (lcm b a) (lcm c a)`,
   ONCE_REWRITE_TAC [lcm_comm] THEN
   ACCEPT_TAC gcd_left_distrib);;

export_thm gcd_right_distrib;;

logfile_end ();;

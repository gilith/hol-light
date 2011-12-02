(* ========================================================================= *)
(* Natural number arithmetic.                                                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "recursion.ml";;

(* ------------------------------------------------------------------------- *)
(* Note: all the following proofs are intuitionistic and intensional, except *)
(* for the least number principle num_WOP.                                   *)
(* (And except the arith rewrites at the end; these could be done that way   *)
(* but they use the conditional anyway.) In fact, one could very easily      *)
(* write a "decider" returning P \/ ~P for quantifier-free P.                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<",(12,"right"));;
parse_as_infix("<=",(12,"right"));;
parse_as_infix(">",(12,"right"));;
parse_as_infix(">=",(12,"right"));;

parse_as_infix("+",(16,"right"));;
parse_as_infix("-",(18,"left"));;
parse_as_infix("*",(20,"right"));;
parse_as_infix("EXP",(24,"left"));;

parse_as_infix("DIV",(22,"left"));;
parse_as_infix("MOD",(22,"left"));;

(* ------------------------------------------------------------------------- *)
(* The predecessor function.                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "natural-dest";;

let PRE =
    let def = new_recursive_definition num_RECURSION
          `(PRE 0 = 0) /\
           (!n. PRE (SUC n) = n)` in
    CONJUNCT2 def;;

export_thm PRE;;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "natural-add-def";;

let (ZERO_ADD,SUC_ADD) =
  let def = new_recursive_definition num_RECURSION
    `(!n. 0 + n = n) /\
     (!m n. (SUC m) + n = SUC(m + n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm ZERO_ADD;;
export_thm SUC_ADD;;

let ADD = CONJ ZERO_ADD SUC_ADD;;

logfile "natural-add-thm";;

let ADD_0 = prove
 (`!m. m + 0 = m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);;

export_thm ADD_0;;

let ADD_SUC = prove
 (`!m n. m + (SUC n) = SUC(m + n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD]);;

export_thm ADD_SUC;;

let ADD_CLAUSES = prove
 (`(!n. 0 + n = n) /\
   (!m. m + 0 = m) /\
   (!m n. (SUC m) + n = SUC(m + n)) /\
   (!m n. m + (SUC n) = SUC(m + n))`,
  REWRITE_TAC[ADD; ADD_0; ADD_SUC]);;

let ADD_SYM = prove
 (`!m n. m + n = n + m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

export_thm ADD_SYM;;

let ADD_ASSOC = prove
 (`!m n p. m + (n + p) = (m + n) + p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

export_thm ADD_ASSOC;;

let ADD_AC = prove
 (`!m n p.
     (m + n = n + m) /\
     ((m + n) + p = m + (n + p)) /\
     (m + (n + p) = n + (m + p))`,
  MESON_TAC[ADD_ASSOC; ADD_SYM]);;

let ADD_EQ_0 = prove
 (`!m n. (m + n = 0) <=> (m = 0) /\ (n = 0)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; NOT_SUC]);;

export_thm ADD_EQ_0;;

let EQ_ADD_LCANCEL = prove
 (`!m n p. (m + n = m + p) <=> (n = p)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUC_INJ]);;

export_thm EQ_ADD_LCANCEL;;

let EQ_ADD_RCANCEL = prove
 (`!m n p. (m + p = n + p) <=> (m = n)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL);;

export_thm EQ_ADD_RCANCEL;;

let EQ_ADD_LCANCEL_0 = prove
 (`!m n. (m + n = m) <=> (n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; SUC_INJ]);;

export_thm EQ_ADD_LCANCEL_0;;

let EQ_ADD_RCANCEL_0 = prove
 (`!m n. (m + n = n) <=> (m = 0)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC EQ_ADD_LCANCEL_0);;

export_thm EQ_ADD_RCANCEL_0;;

(* ------------------------------------------------------------------------- *)
(* Now define "bitwise" binary representation of numerals.                   *)
(* ------------------------------------------------------------------------- *)

let BIT0 = prove
 (`!n. BIT0 n = n + n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[BIT0_DEF; ADD_CLAUSES]);;

let BIT1 = prove
 (`!n. BIT1 n = SUC(n + n)`,
  REWRITE_TAC[BIT1_DEF; BIT0]);;

let BIT0_THM = prove
 (`!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n`,
  REWRITE_TAC[NUMERAL; BIT0]);;

let BIT1_THM = prove
 (`!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)`,
  REWRITE_TAC[NUMERAL; BIT1]);;

(* ------------------------------------------------------------------------- *)
(* Following is handy before num_CONV arrives.                               *)
(* ------------------------------------------------------------------------- *)

let ONE = prove
 (`1 = SUC 0`,
  REWRITE_TAC [NUMERAL; REWRITE_RULE [NUMERAL] BIT1_DEF;
               REWRITE_RULE [NUMERAL] BIT0_DEF]);;

let TWO = prove
 (`2 = SUC 1`,
  REWRITE_TAC [NUMERAL; REWRITE_RULE [NUMERAL] BIT1_DEF;
               REWRITE_RULE [NUMERAL] BIT0_DEF]);;

(* ------------------------------------------------------------------------- *)
(* One immediate consequence.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-add-thm";;

let ADD1 = prove
 (`!m. SUC m = m + 1`,
  REWRITE_TAC[BIT1_THM; ADD_CLAUSES]);;

export_thm ADD1;;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

logfile "natural-mult-def";;

let (ZERO_MULT,SUC_MULT) =
    let def = new_recursive_definition num_RECURSION
        `(!n. 0 * n = 0) /\
         (!m n. (SUC m) * n = (m * n) + n)` in
    (CONJUNCT1 def, CONJUNCT2 def);;

export_thm ZERO_MULT;;
export_thm SUC_MULT;;

let MULT = CONJ ZERO_MULT SUC_MULT;;

logfile "natural-mult-thm";;

let MULT_0 = prove
 (`!m. m * 0 = 0`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT; ADD_CLAUSES]);;

export_thm MULT_0;;

let MULT_SUC = prove
 (`!m n. m * (SUC n) = m + (m * n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT; ADD_CLAUSES; ADD_ASSOC]);;

export_thm MULT_SUC;;

let MULT_1 = prove
 (`!m. m * 1 = m`,
  REWRITE_TAC [ONE; MULT_SUC; MULT_0; ADD_0]);;

export_thm MULT_1;;

let ONE_MULT = prove
 (`!m. 1 * m = m`,
  REWRITE_TAC [ONE; SUC_MULT; ZERO_MULT; ADD]);;

export_thm ONE_MULT;;

let MULT_CLAUSES = prove
 (`(!n. 0 * n = 0) /\
   (!m. m * 0 = 0) /\
   (!n. 1 * n = n) /\
   (!m. m * 1 = m) /\
   (!m n. (SUC m) * n = (m * n) + n) /\
   (!m n. m * (SUC n) = m + (m * n))`,
  REWRITE_TAC [ZERO_MULT; MULT_0; ONE_MULT; MULT_1; SUC_MULT; MULT_SUC]);;

let MULT_SYM = prove
 (`!m n. m * n = n * m`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EQT_INTRO(SPEC_ALL ADD_SYM)]);;

export_thm MULT_SYM;;

let LEFT_ADD_DISTRIB = prove
 (`!m n p. m * (n + p) = (m * n) + (m * p)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ADD; MULT_CLAUSES; ADD_ASSOC]);;

export_thm LEFT_ADD_DISTRIB;;

let RIGHT_ADD_DISTRIB = prove
 (`!m n p. (m + n) * p = (m * p) + (n * p)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_ADD_DISTRIB);;

export_thm RIGHT_ADD_DISTRIB;;

let MULT_ASSOC = prove
 (`!m n p. m * (n * p) = (m * n) * p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; RIGHT_ADD_DISTRIB]);;

export_thm MULT_ASSOC;;

let MULT_LASSOC = prove
 (`!m n p. m * (n * p) = n * (m * p)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MULT_ASSOC] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC MULT_SYM);;

export_thm MULT_LASSOC;;

let MULT_AC = prove
 (`!m n p.
     (m * n = n * m) /\
     ((m * n) * p = m * (n * p)) /\
     (m * (n * p) = n * (m * p))`,
  REPEAT STRIP_TAC THENL
  [MATCH_ACCEPT_TAC MULT_SYM;
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_ACCEPT_TAC MULT_ASSOC;
   MATCH_ACCEPT_TAC MULT_LASSOC]);;

let MULT_EQ_0 = prove
 (`!m n. (m * n = 0) <=> (m = 0) \/ (n = 0)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; NOT_SUC]);;

export_thm MULT_EQ_0;;

let EQ_MULT_LCANCEL = prove
 (`!m n p. (m * n = m * p) <=> (m = 0) \/ (n = p)`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; NOT_SUC] THEN
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GSYM NOT_SUC; NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ; GSYM ADD_ASSOC; EQ_ADD_LCANCEL]);;

export_thm EQ_MULT_LCANCEL;;

let EQ_MULT_RCANCEL = prove
 (`!m n p. (m * p = n * p) <=> (m = n) \/ (p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; DISJ_SYM] THEN MATCH_ACCEPT_TAC EQ_MULT_LCANCEL);;

export_thm EQ_MULT_RCANCEL;;

let EQ_MULTL = prove
 (`!m n. (m = m * n) <=> (m = 0) \/ (n = 1)`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV (GSYM MULT_1)))) THEN
  REWRITE_TAC [EQ_MULT_LCANCEL] THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC EQ_SYM_EQ);;

export_thm EQ_MULTL;;

let EQ_MULTR = prove
 (`!m n. (m = n * m) <=> (m = 0) \/ (n = 1)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  MATCH_ACCEPT_TAC EQ_MULTL);;

export_thm EQ_MULTR;;

let MULTL_EQ = prove
 (`!m n. (m * n = m) <=> (m = 0) \/ (n = 1)`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
  MATCH_ACCEPT_TAC EQ_MULTL);;

export_thm MULTL_EQ;;

let MULTR_EQ = prove
 (`!m n. (n * m = m) <=> (m = 0) \/ (n = 1)`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV EQ_SYM_EQ)) THEN
  MATCH_ACCEPT_TAC EQ_MULTR);;

export_thm MULTR_EQ;;

let MULT_2 = prove
 (`!n. 2 * n = n + n`,
  GEN_TAC THEN REWRITE_TAC[BIT0_THM; MULT_CLAUSES; RIGHT_ADD_DISTRIB]);;

export_thm MULT_2;;

let MULT_EQ_1 = prove
 (`!m n. (m * n = 1) <=> (m = 1) /\ (n = 1)`,
  INDUCT_TAC THEN INDUCT_TAC THEN REWRITE_TAC
    [MULT_CLAUSES; ADD_CLAUSES; BIT0_THM; BIT1_THM; GSYM NOT_SUC] THEN
  REWRITE_TAC[SUC_INJ; ADD_EQ_0; MULT_EQ_0] THEN
  CONV_TAC TAUT);;

export_thm MULT_EQ_1;;

(* ------------------------------------------------------------------------- *)
(* Exponentiation.                                                           *)
(* ------------------------------------------------------------------------- *)

logfile "natural-exp-def";;

let (EXP_0,EXP_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!m. m EXP 0 = 1) /\
     (!m n. m EXP (SUC n) = m * (m EXP n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm EXP_0;;
export_thm EXP_SUC;;

let EXP = CONJ EXP_0 EXP_SUC;;

logfile "natural-exp-thm";;

let EXP_EQ_0 = prove
 (`!m n. (m EXP n = 0) <=> (m = 0) /\ ~(n = 0)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC
    [BIT1_THM; NOT_SUC; NOT_SUC; EXP; MULT_CLAUSES; ADD_CLAUSES; ADD_EQ_0]);;

export_thm EXP_EQ_0;;

let EXP_EQ_1 = prove
 (`!x n. x EXP n = 1 <=> x = 1 \/ n = 0`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_EQ_1; NOT_SUC] THEN
  CONV_TAC TAUT);;

export_thm EXP_EQ_1;;

let EXP_ZERO = prove
 (`!n. 0 EXP n = if n = 0 then 1 else 0`,
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[EXP_EQ_0; EXP_EQ_1]);;

export_thm EXP_ZERO;;

let EXP_ADD = prove
 (`!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP; ADD_CLAUSES; MULT_CLAUSES; MULT_AC]);;

export_thm EXP_ADD;;

let EXP_ONE = prove
 (`!n. 1 EXP n = 1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES]);;

export_thm EXP_ONE;;

let EXP_1 = prove
 (`!n. n EXP 1 = n`,
  REWRITE_TAC[ONE; EXP; MULT_CLAUSES; ADD_CLAUSES]);;

export_thm EXP_1;;

let EXP_2 = prove
 (`!n. n EXP 2 = n * n`,
  REWRITE_TAC[BIT0_THM; BIT1_THM; EXP; EXP_ADD; MULT_CLAUSES; ADD_CLAUSES]);;

export_thm EXP_2;;

let MULT_EXP = prove
 (`!p m n. (m * n) EXP p = m EXP p * n EXP p`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES; MULT_AC]);;

export_thm MULT_EXP;;

let EXP_MULT = prove
 (`!m n p. m EXP (n * p) = (m EXP n) EXP p`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EXP_ADD; EXP; MULT_CLAUSES] THENL
   [CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    INDUCT_TAC THEN ASM_REWRITE_TAC[EXP; MULT_CLAUSES];
    REWRITE_TAC[MULT_EXP] THEN MATCH_ACCEPT_TAC MULT_SYM]);;

export_thm EXP_MULT;;

(* ------------------------------------------------------------------------- *)
(* Define the orderings recursively too.                                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-order-def";;

let (LE_ZERO,LE_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!m. (m <= 0) <=> (m = 0)) /\
     (!m n. (m <= SUC n) <=> (m = SUC n) \/ (m <= n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm LE_ZERO;;
export_thm LE_SUC;;

let LE = CONJ LE_ZERO LE_SUC;;

let (LT_ZERO,LT_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!m. (m < 0) <=> F) /\
     (!m n. (m < SUC n) <=> (m = n) \/ (m < n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm LT_ZERO;;
export_thm LT_SUC;;

let LT = CONJ LT_ZERO LT_SUC;;

let GE = new_definition
  `!m n. m >= n <=> n <= m`;;

export_thm GE;;

let GT = new_definition
  `!m n. m > n <=> n < m`;;

export_thm GT;;

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum of natural numbers.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "natural-order-min-max-def";;

let MAX = new_definition
  `!m n. MAX m n = if m <= n then n else m`;;

export_thm MAX;;

let MIN = new_definition
  `!m n. MIN m n = if m <= n then m else n`;;

export_thm MIN;;

(* ------------------------------------------------------------------------- *)
(* Step cases.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "natural-order-thm";;

let LE_SUC_LT = prove
 (`!m n. (SUC m <= n) <=> (m < n)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LE; LT; NOT_SUC; SUC_INJ]);;

export_thm LE_SUC_LT;;

let LT_SUC_LE = prove
 (`!m n. (m < SUC n) <=> (m <= n)`,
  GEN_TAC THEN INDUCT_TAC THEN ONCE_REWRITE_TAC[LT; LE] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[LT]);;

export_thm LT_SUC_LE;;

let LE_SUC = prove
 (`!m n. (SUC m <= SUC n) <=> (m <= n)`,
  REWRITE_TAC[LE_SUC_LT; LT_SUC_LE]);;

export_thm LE_SUC;;

let LT_SUC = prove
 (`!m n. (SUC m < SUC n) <=> (m < n)`,
  REWRITE_TAC[LT_SUC_LE; LE_SUC_LT]);;

export_thm LT_SUC;;

(* ------------------------------------------------------------------------- *)
(* Base cases.                                                               *)
(* ------------------------------------------------------------------------- *)

let LE_0 = prove
 (`!n. 0 <= n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LE]);;

export_thm LE_0;;

let LT_0 = prove
 (`!n. 0 < SUC n`,
  REWRITE_TAC[LT_SUC_LE; LE_0]);;

export_thm LT_0;;

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let LE_REFL = prove
 (`!n. n <= n`,
  INDUCT_TAC THEN REWRITE_TAC[LE]);;

export_thm LE_REFL;;

let LT_REFL = prove
 (`!n. ~(n < n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[LT]);;

export_thm LT_REFL;;

(* ------------------------------------------------------------------------- *)
(* Antisymmetry.                                                             *)
(* ------------------------------------------------------------------------- *)

let LE_ANTISYM = prove
 (`!m n. (m <= n /\ n <= m) <=> (m = n)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; SUC_INJ] THEN
  REWRITE_TAC[LE; NOT_SUC; GSYM NOT_SUC]);;

export_thm LE_ANTISYM;;

let LT_ANTISYM = prove
 (`!m n. ~(m < n /\ n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC] THEN REWRITE_TAC[LT]);;

export_thm LT_ANTISYM;;

let LET_ANTISYM = prove
 (`!m n. ~(m <= n /\ n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC]);;

export_thm LET_ANTISYM;;

let LTE_ANTISYM = prove
 (`!m n. ~(m < n /\ n <= m)`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[LET_ANTISYM]);;

export_thm LTE_ANTISYM;;

(* ------------------------------------------------------------------------- *)
(* Transitivity.                                                             *)
(* ------------------------------------------------------------------------- *)

let LE_TRANS = prove
 (`!m n p. m <= n /\ n <= p ==> m <= p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LE_0] THEN REWRITE_TAC[LE; NOT_SUC]);;

export_thm LE_TRANS;;

let LT_TRANS = prove
 (`!m n p. m < n /\ n < p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LT_SUC; LT_0] THEN REWRITE_TAC[LT; NOT_SUC]);;

export_thm LT_TRANS;;

let LET_TRANS = prove
 (`!m n p. m <= n /\ n < p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; LT_0] THEN REWRITE_TAC[LT; LE; NOT_SUC]);;

export_thm LET_TRANS;;

let LTE_TRANS = prove
 (`!m n p. m < n /\ n <= p ==> m < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; LT_0] THEN REWRITE_TAC[LT; LE; NOT_SUC]);;

export_thm LTE_TRANS;;

(* ------------------------------------------------------------------------- *)
(* Totality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let LE_CASES = prove
 (`!m n. m <= n \/ n <= m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_0; LE_SUC]);;

export_thm LE_CASES;;

let LT_CASES = prove
 (`!m n. (m < n) \/ (n < m) \/ (m = n)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LT_SUC; SUC_INJ] THEN
  REWRITE_TAC[LT; NOT_SUC; GSYM NOT_SUC] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

export_thm LT_CASES;;

let LET_CASES = prove
 (`!m n. m <= n \/ n < m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC_LT; LT_SUC_LE; LE_0]);;

export_thm LET_CASES;;

let LTE_CASES = prove
 (`!m n. m < n \/ n <= m`,
  ONCE_REWRITE_TAC[DISJ_SYM] THEN MATCH_ACCEPT_TAC LET_CASES);;

export_thm LTE_CASES;;

(* ------------------------------------------------------------------------- *)
(* Relationship between orderings.                                           *)
(* ------------------------------------------------------------------------- *)

let LE_LT = prove
 (`!m n. (m <= n) <=> (m < n) \/ (m = n)`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE_SUC; LT_SUC; SUC_INJ; LE_0; LT_0] THEN
  REWRITE_TAC[LE; LT]);;

export_thm LE_LT;;

let LT_LE = prove
 (`!m n. (m < n) <=> (m <= n) /\ ~(m = n)`,
  REWRITE_TAC[LE_LT] THEN REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[LT_REFL];
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[]]);;

export_thm LT_LE;;

let NOT_LE = prove
 (`!m n. ~(m <= n) <=> (n < m)`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC; GSYM NOT_SUC; LE_0] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

export_thm NOT_LE;;

let NOT_LT = prove
 (`!m n. ~(m < n) <=> n <= m`,
  REPEAT INDUCT_TAC THEN ASM_REWRITE_TAC[LE_SUC; LT_SUC] THEN
  REWRITE_TAC[LE; LT; NOT_SUC; GSYM NOT_SUC; LE_0] THEN
  W(W (curry SPEC_TAC) o hd o frees o snd) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

export_thm NOT_LT;;

let LT_IMP_LE = prove
 (`!m n. m < n ==> m <= n`,
  REWRITE_TAC[LT_LE] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

export_thm LT_IMP_LE;;

let EQ_IMP_LE = prove
 (`!m n. (m = n) ==> m <= n`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[LE_REFL]);;

export_thm EQ_IMP_LE;;

(* ------------------------------------------------------------------------- *)
(* Ordering and succession.                                                  *)
(* ------------------------------------------------------------------------- *)

let SUC_LT = prove
 (`!n. n < SUC n`,
  REWRITE_TAC [LT_SUC_LE; LE_REFL]);;

export_thm SUC_LT;;

let SUC_LE = prove
 (`!n. n <= SUC n`,
  REWRITE_TAC [LE_LT; SUC_LT]);;

export_thm SUC_LE;;

(* ------------------------------------------------------------------------- *)
(* Often useful to shuffle between different versions of "0 < n".            *)
(* ------------------------------------------------------------------------- *)

let LT_NZ = prove
 (`!n. 0 < n <=> ~(n = 0)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[NOT_SUC; LT; EQ_SYM_EQ] THEN
  CONV_TAC TAUT);;

export_thm LT_NZ;;

let LE_1 = prove
 (`(!n. ~(n = 0) ==> 0 < n) /\
   (!n. ~(n = 0) ==> 1 <= n) /\
   (!n. 0 < n ==> ~(n = 0)) /\
   (!n. 0 < n ==> 1 <= n) /\
   (!n. 1 <= n ==> 0 < n) /\
   (!n. 1 <= n ==> ~(n = 0))`,
  REWRITE_TAC[LT_NZ; GSYM NOT_LT; ONE; LT]);;

(* ------------------------------------------------------------------------- *)
(* Relate the orderings to arithmetic operations.                            *)
(* ------------------------------------------------------------------------- *)

logfile "natural-add-thm";;

let LE_EXISTS = prove
 (`!m n. (m <= n) <=> (?d. n = m + d)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[LE] THENL
   [REWRITE_TAC[CONV_RULE(LAND_CONV SYM_CONV) (SPEC_ALL ADD_EQ_0)] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM; EXISTS_REFL];
    EQ_TAC THENL
     [DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES];
        DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
        EXISTS_TAC `SUC d` THEN REWRITE_TAC[ADD_CLAUSES]];
      ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUC_INJ] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN DISJ2_TAC THEN
      REWRITE_TAC[EQ_ADD_LCANCEL; GSYM EXISTS_REFL]]]);;

export_thm LE_EXISTS;;

let LT_EXISTS = prove
 (`!m n. (m < n) <=> (?d. n = m + SUC d)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[LT; ADD_CLAUSES; GSYM NOT_SUC] THEN
  ASM_REWRITE_TAC[SUC_INJ] THEN EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN2 SUBST1_TAC MP_TAC) THENL
     [EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES];
      DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC) THEN
      EXISTS_TAC `SUC d` THEN REWRITE_TAC[ADD_CLAUSES]];
    ONCE_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; SUC_INJ] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN DISJ2_TAC THEN
    REWRITE_TAC[SUC_INJ; EQ_ADD_LCANCEL; GSYM EXISTS_REFL]]);;

export_thm LT_EXISTS;;

(* ------------------------------------------------------------------------- *)
(* Interaction with addition.                                                *)
(* ------------------------------------------------------------------------- *)

let LE_ADD = prove
 (`!m n. m <= m + n`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[LE; ADD_CLAUSES; LE_REFL]);;

export_thm LE_ADD;;

let LE_ADDR = prove
 (`!m n. n <= m + n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD);;

export_thm LE_ADDR;;

let LT_ADD = prove
 (`!m n. (m < m + n) <=> (0 < n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES; LT_SUC]);;

export_thm LT_ADD;;

let LT_ADDR = prove
 (`!m n. (n < m + n) <=> (0 < m)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD);;

export_thm LT_ADDR;;

let LE_ADD_LCANCEL = prove
 (`!m n p. (m + n) <= (m + p) <=> n <= p`,
  REWRITE_TAC[LE_EXISTS; GSYM ADD_ASSOC; EQ_ADD_LCANCEL]);;

export_thm LE_ADD_LCANCEL;;

let LE_ADD_RCANCEL = prove
 (`!m n p. (m + p) <= (n + p) <=> (m <= n)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LE_ADD_LCANCEL);;

export_thm LE_ADD_RCANCEL;;

let LT_ADD_LCANCEL = prove
 (`!m n p. (m + n) < (m + p) <=> n < p`,
  REWRITE_TAC[LT_EXISTS; GSYM ADD_ASSOC; EQ_ADD_LCANCEL; SUC_INJ]);;

export_thm LT_ADD_LCANCEL;;

let LT_ADD_RCANCEL = prove
 (`!m n p. (n + m) < (p + m) <=> (n < p)`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC LT_ADD_LCANCEL);;

export_thm LT_ADD_RCANCEL;;

let LE_ADD2 = prove
 (`!m n p q. m <= p /\ n <= q ==> m + n <= p + q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a + b` THEN ASM_REWRITE_TAC[ADD_AC]);;

export_thm LE_ADD2;;

let LET_ADD2 = prove
 (`!m n p q. m <= p /\ n < q ==> m + n < p + q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS; LT_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a + b` THEN ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES; ADD_AC]);;

export_thm LET_ADD2;;

let LTE_ADD2 = prove
 (`!m n p q. m < p /\ n <= q ==> m + n < p + q`,
  ONCE_REWRITE_TAC[ADD_SYM; CONJ_SYM] THEN
  MATCH_ACCEPT_TAC LET_ADD2);;

export_thm LTE_ADD2;;

let LT_ADD2 = prove
 (`!m n p q. m < p /\ n < q ==> m + n < p + q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LTE_ADD2 THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN
  ASM_REWRITE_TAC[]);;

export_thm LT_ADD2;;

(* ------------------------------------------------------------------------- *)
(* And multiplication.                                                       *)
(* ------------------------------------------------------------------------- *)

logfile "natural-mult-thm";;

let LT_MULT = prove
 (`!m n. (0 < m * n) <=> (0 < m) /\ (0 < n)`,
  REPEAT INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_0]);;

export_thm LT_MULT;;

let LE_MULT2 = prove
 (`!m n p q. m <= n /\ p <= q ==> m * p <= n * q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_TAC `a:num`) (X_CHOOSE_TAC `b:num`)) THEN
  EXISTS_TAC `a * p + m * b + a * b` THEN
  ASM_REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; ADD_ASSOC]);;

export_thm LE_MULT2;;

let LT_LMULT = prove
 (`!m n p. ~(m = 0) /\ n < p ==> m * n < m * p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LT_LE] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL];
    ASM_REWRITE_TAC[EQ_MULT_LCANCEL]]);;

export_thm LT_LMULT;;

let LE_MULT_LCANCEL = prove
 (`!m n p. (m * n) <= (m * p) <=> (m = 0) \/ n <= p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LE_REFL; LE_0; NOT_SUC] THEN
  REWRITE_TAC[LE_SUC] THEN
  REWRITE_TAC[LE; LE_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM(el 4(CONJUNCTS MULT_CLAUSES)); NOT_SUC]);;

export_thm LE_MULT_LCANCEL;;

let LE_MULT_RCANCEL = prove
 (`!m n p. (m * p) <= (n * p) <=> (m <= n) \/ (p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; DISJ_SYM] THEN
  MATCH_ACCEPT_TAC LE_MULT_LCANCEL);;

export_thm LE_MULT_RCANCEL;;

let LT_MULT_LCANCEL = prove
 (`!m n p. (m * n) < (m * p) <=> ~(m = 0) /\ n < p`,
  REPEAT INDUCT_TAC THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_REFL; LT_0; NOT_SUC] THEN
  REWRITE_TAC[LT_SUC] THEN
  REWRITE_TAC[LT; LT_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  ASM_REWRITE_TAC[GSYM(el 4(CONJUNCTS MULT_CLAUSES)); NOT_SUC]);;

export_thm LT_MULT_LCANCEL;;

let LT_MULT_RCANCEL = prove
 (`!m n p. (m * p) < (n * p) <=> (m < n) /\ ~(p = 0)`,
  ONCE_REWRITE_TAC[MULT_SYM; CONJ_SYM] THEN
  MATCH_ACCEPT_TAC LT_MULT_LCANCEL);;

export_thm LT_MULT_RCANCEL;;

let LT_MULT2 = prove
 (`!m n p q. m < n /\ p < q ==> m * p < n * q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LET_TRANS THEN
  EXISTS_TAC `n * p` THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; LT_IMP_LE; LT_MULT_LCANCEL] THEN
  UNDISCH_TAC `m < n` THEN CONV_TAC CONTRAPOS_CONV THEN SIMP_TAC[LT]);;

export_thm LT_MULT2;;

let LE_SQUARE_REFL = prove
 (`!n. n <= n * n`,
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; LE_0; LE_ADDR]);;

export_thm LE_SQUARE_REFL;;

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

let WLOG_LE = prove
 (`!P. (!m n. P m n <=> P n m) /\ (!m n. m <= n ==> P m n) ==> !m n. P m n`,
  MESON_TAC[LE_CASES]);;

let WLOG_LT = prove
 (`!P.
     (!m. P m m) /\ (!m n. P m n <=> P n m) /\ (!m n. m < n ==> P m n)
     ==> !m y. P m y`,
  MESON_TAC[LT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Existence of least and greatest elements of (finite) set.                 *)
(* ------------------------------------------------------------------------- *)

logfile "natural-order-thm";;

let num_WF = prove
 (`!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n`,
  GEN_TAC THEN MP_TAC(SPEC `\n. !m. m < n ==> P m` num_INDUCTION) THEN
  REWRITE_TAC[LT; BETA_THM] THEN MESON_TAC[LT]);;

export_thm num_WF;;

let num_WOP = prove
 (`!P. (?n. P n) <=> (?n. P(n) /\ !m. m < n ==> ~P(m))`,
  GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC num_WF THEN ASM_MESON_TAC[]);;

export_thm num_WOP;;

let num_MAX = prove
 (`!P. (?x. P x) /\ (?M. !x. P x ==> x <= M) <=>
       ?m. P m /\ (!x. P x ==> x <= m)`,
  GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:num`) MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` MP_TAC o ONCE_REWRITE_RULE[num_WOP]) THEN
    DISCH_THEN(fun th -> EXISTS_TAC `m:num` THEN MP_TAC th) THEN
    REWRITE_TAC[TAUT `(a /\ b ==> c /\ a) <=> (a /\ b ==> c)`] THEN
    SPEC_TAC(`m:num`,`m:num`) THEN INDUCT_TAC THENL
     [REWRITE_TAC[LE; LT] THEN DISCH_THEN(IMP_RES_THEN SUBST_ALL_TAC) THEN
      POP_ASSUM ACCEPT_TAC;
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `m:num`)) THEN
      REWRITE_TAC[LT] THEN CONV_TAC CONTRAPOS_CONV THEN
      DISCH_TAC THEN REWRITE_TAC[] THEN X_GEN_TAC `p:num` THEN
      FIRST_ASSUM(MP_TAC o SPEC `p:num`) THEN REWRITE_TAC[LE] THEN
      ASM_CASES_TAC `p = SUC m` THEN ASM_REWRITE_TAC[]];
    REPEAT STRIP_TAC THEN EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]);;

export_thm num_MAX;;

(* ------------------------------------------------------------------------- *)
(* Oddness and evenness (recursively rather than inductively!)               *)
(* ------------------------------------------------------------------------- *)

logfile "natural-div-def";;

let (EVEN_ZERO,EVEN_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(EVEN 0 <=> T) /\
     (!n. EVEN (SUC n) <=> ~(EVEN n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm EVEN_ZERO;;
export_thm EVEN_SUC;;

let EVEN = CONJ EVEN_ZERO EVEN_SUC;;

let (ODD_ZERO,ODD_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(ODD 0 <=> F) /\
     (!n. ODD (SUC n) <=> ~(ODD n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm ODD_ZERO;;
export_thm ODD_SUC;;

let ODD = CONJ ODD_ZERO ODD_SUC;;

logfile "natural-div-thm";;

let NOT_EVEN = prove
 (`!n. ~(EVEN n) <=> ODD n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ODD]);;

export_thm NOT_EVEN;;

let NOT_ODD = prove
 (`!n. ~(ODD n) <=> EVEN n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ODD]);;

export_thm NOT_ODD;;

let EVEN_OR_ODD = prove
 (`!n. EVEN n \/ ODD n`,
  INDUCT_TAC THEN REWRITE_TAC[EVEN; ODD; NOT_EVEN; NOT_ODD] THEN
  ONCE_REWRITE_TAC[DISJ_SYM] THEN ASM_REWRITE_TAC[]);;

export_thm EVEN_OR_ODD;;

let EVEN_AND_ODD = prove
 (`!n. ~(EVEN n /\ ODD n)`,
  REWRITE_TAC[GSYM NOT_EVEN; ITAUT `~(p /\ ~p)`]);;

export_thm EVEN_AND_ODD;;

let EVEN_ADD = prove
 (`!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[EVEN; ADD_CLAUSES] THEN
  X_GEN_TAC `p:num` THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `p:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

export_thm EVEN_ADD;;

let EVEN_MULT = prove
 (`!m n. EVEN(m * n) <=> EVEN(m) \/ EVEN(n)`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES; EVEN_ADD; EVEN] THEN
  X_GEN_TAC `p:num` THEN
  DISJ_CASES_THEN MP_TAC (SPEC `n:num` EVEN_OR_ODD) THEN
  DISJ_CASES_THEN MP_TAC (SPEC `p:num` EVEN_OR_ODD) THEN
  REWRITE_TAC[GSYM NOT_EVEN] THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[]);;

export_thm EVEN_MULT;;

let EVEN_EXP = prove
 (`!m n. EVEN(m EXP n) <=> EVEN(m) /\ ~(n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[EVEN; EXP; ONE; EVEN_MULT; NOT_SUC] THEN
  CONV_TAC ITAUT);;

export_thm EVEN_EXP;;

let ODD_ADD = prove
 (`!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_ADD] THEN
  CONV_TAC ITAUT);;

export_thm ODD_ADD;;

let ODD_MULT = prove
 (`!m n. ODD(m * n) <=> ODD(m) /\ ODD(n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_MULT] THEN
  CONV_TAC ITAUT);;

export_thm ODD_MULT;;

let ODD_EXP = prove
 (`!m n. ODD(m EXP n) <=> ODD(m) \/ (n = 0)`,
  GEN_TAC THEN INDUCT_TAC THEN
  ASM_REWRITE_TAC[ODD; EXP; ONE; ODD_MULT; NOT_SUC] THEN
  CONV_TAC ITAUT);;

export_thm ODD_EXP;;

let EVEN_DOUBLE = prove
 (`!n. EVEN(2 * n)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_MULT] THEN DISJ1_TAC THEN
  PURE_REWRITE_TAC[BIT0_THM; BIT1_THM] THEN REWRITE_TAC[EVEN; EVEN_ADD]);;

export_thm EVEN_DOUBLE;;

let ODD_DOUBLE = prove
 (`!n. ODD(SUC(2 * n))`,
  REWRITE_TAC[ODD] THEN REWRITE_TAC[NOT_ODD; EVEN_DOUBLE]);;

export_thm ODD_DOUBLE;;

let EVEN_EXISTS_LEMMA = prove
 (`!n. (EVEN n ==> ?m. n = 2 * m) /\
       (~EVEN n ==> ?m. n = SUC(2 * m))`,
  INDUCT_TAC THEN REWRITE_TAC[EVEN] THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[MULT_CLAUSES];
    POP_ASSUM STRIP_ASSUME_TAC THEN CONJ_TAC THEN
    DISCH_THEN(ANTE_RES_THEN(X_CHOOSE_TAC `m:num`)) THENL
     [EXISTS_TAC `SUC m` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[MULT_2] THEN REWRITE_TAC[ADD_CLAUSES];
      EXISTS_TAC `m:num` THEN ASM_REWRITE_TAC[]]]);;

let EVEN_EXISTS = prove
 (`!n. EVEN n <=> ?m. n = 2 * m`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(SPEC_ALL EVEN_EXISTS_LEMMA)) THEN ASM_REWRITE_TAC[];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[EVEN_DOUBLE]]);;

export_thm EVEN_EXISTS;;

let ODD_EXISTS = prove
 (`!n. ODD n <=> ?m. n = SUC(2 * m)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2(SPEC_ALL EVEN_EXISTS_LEMMA)) THEN
    ASM_REWRITE_TAC[NOT_EVEN];
    POP_ASSUM(CHOOSE_THEN SUBST1_TAC) THEN REWRITE_TAC[ODD_DOUBLE]]);;

export_thm ODD_EXISTS;;

let EVEN_ODD_DECOMPOSITION = prove
 (`!n. (?k m. ODD m /\ (n = 2 EXP k * m)) <=> ~(n = 0)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  DISJ_CASES_TAC(SPEC `n:num` EVEN_OR_ODD) THENL
   [ALL_TAC; ASM_MESON_TAC[ODD; EXP; MULT_CLAUSES]] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EVEN_EXISTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[MULT_EQ_0] THENL
   [REWRITE_TAC[MULT_CLAUSES; LT] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
    REWRITE_TAC[EXP_EQ_0; MULT_EQ_0; TWO; NOT_SUC] THEN MESON_TAC[ODD];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))] THEN
    ASM_REWRITE_TAC[LT_MULT_RCANCEL; TWO; LT];
    ALL_TAC] THEN
  REWRITE_TAC[TWO; NOT_SUC] THEN REWRITE_TAC[GSYM TWO] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[EXP; MULT_ASSOC]);;

export_thm EVEN_ODD_DECOMPOSITION;;

(* ------------------------------------------------------------------------- *)
(* Cutoff subtraction, also defined recursively. (Not the HOL88 defn.)       *)
(* ------------------------------------------------------------------------- *)

logfile "natural-sub-def";;

let ADD_SUB =
  let SUB_DEF = new_recursive_definition num_RECURSION
    `(!m. m - 0 = m) /\
     (!m n. m - (SUC n) = PRE(m - n))` in
  let ADD_SUB_LEMMA = prove
    (`!m n. PRE (SUC m - n) = m - n`,
     GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[SUB_DEF; PRE]) in
  prove
  (`!m n. (m + n) - n = m`,
   GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[SUB_DEF; ADD_CLAUSES; ADD_SUB_LEMMA]);;

export_thm ADD_SUB;;

logfile "natural-sub-thm";;

let SUB_0 = prove
 (`!m. m - 0 = m`,
  GEN_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM ADD_0]))) THEN
  REWRITE_TAC [ADD_SUB]);;

export_thm SUB_0;;

let ADD_SUB2 = prove
 (`!m n. (m + n) - m = n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC ADD_SUB);;

export_thm ADD_SUB2;;

let SUB_ADD = prove
 (`!m n. n <= m ==> ((m - n) + n = m)`,
  REWRITE_TAC [LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2] THEN
  MATCH_ACCEPT_TAC ADD_SYM);;

export_thm SUB_ADD;;

let SUB_ADD2 = prove
 (`!m n. n <= m ==> (n + (m - n) = m)`,
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ACCEPT_TAC SUB_ADD);;

export_thm SUB_ADD2;;

let SUB_ADD_LCANCEL = prove
 (`!m n p. p <= n ==> (m + n) - (m + p) = n - p`,
  REWRITE_TAC [LE_EXISTS] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2; ADD_ASSOC]);;

export_thm SUB_ADD_LCANCEL;;

let SUB_ADD_RCANCEL = prove
 (`!m n p. n <= m ==> (m + p) - (n + p) = m - n`,
  ONCE_REWRITE_TAC[ADD_SYM] THEN MATCH_ACCEPT_TAC SUB_ADD_LCANCEL);;

export_thm SUB_ADD_RCANCEL;;

let SUB_SUB = prove
 (`!m n p. n + p <= m ==> m - (n + p) = (m - n) - p`,
  REWRITE_TAC [LE_EXISTS] THEN REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2] THEN
  REWRITE_TAC [GSYM ADD_ASSOC; ADD_SUB2]);;

export_thm SUB_ADD;;

let SUB_REFL = prove
 (`!n. n - n = 0`,
  GEN_TAC THEN
  CONV_TAC (LAND_CONV (LAND_CONV (ONCE_REWRITE_CONV [GSYM ADD_0]))) THEN
  REWRITE_TAC [ADD_SUB2]);;

export_thm SUB_REFL;;

let SUB_EQ_0 = prove
 (`!m n. n <= m ==> (m - n = 0 <=> m = n)`,
  REWRITE_TAC [LE_EXISTS] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2; EQ_ADD_LCANCEL_0]);;

export_thm SUB_EQ_0;;

let SUC_SUB1 = prove
 (`!n. SUC n - 1 = n`,
  REWRITE_TAC[ADD1; ADD_SUB]);;

export_thm SUC_SUB1;;

let SUB_SUC = prove
 (`!m n. n <= m ==> SUC m - SUC n = m - n`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`m:num`; `n:num`; `1`] SUB_ADD_RCANCEL) THEN
  ASM_REWRITE_TAC [ADD1]);;

export_thm SUB_SUC;;

let SUC_SUB = prove
 (`!m n. n <= m ==> SUC (m - n) = SUC m - n`,
  REWRITE_TAC [LE_EXISTS] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  ONCE_REWRITE_TAC [GSYM (CONJUNCT2 ADD)] THEN
  REWRITE_TAC [ADD_SUB]);;

export_thm SUC_SUB;;

let SUB_SUC_CANCEL = prove
 (`!m n. n < m ==> SUC (m - SUC n) = m - n`,
  INDUCT_TAC THENL
  [REWRITE_TAC [LT];
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LT_SUC_LE] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`m:num`; `n:num`] SUB_SUC) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC SUC_SUB THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUB_SUC_CANCEL;;

let SUB1 = prove
 (`!n. ~(n = 0) ==> PRE n = n - 1`,
  INDUCT_TAC THENL
  [REWRITE_TAC [];
   REWRITE_TAC [PRE; SUC_SUB1]]);;

export_thm SUB1;;

let SUB_SUC_PRE = prove
  (`!m n. n < m ==> m - SUC n = PRE (m - n)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`m:num`; `n:num`; `1`] SUB_SUB) THEN
   ASM_REWRITE_TAC [GSYM ADD1; GSYM LT_SUC_LE; LT_SUC] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC SUB1 THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [GSYM LE_SUC_LT; LE_EXISTS] THEN
   DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
   REWRITE_TAC [ADD1; GSYM ADD_ASSOC; ADD_SUB2] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   REWRITE_TAC [GSYM ADD1; NOT_SUC]);;

export_thm SUB_SUC_PRE;;

let SUB_PRESUC = prove
 (`!m n. n <= m ==> PRE (SUC m - n) = m - n`,
  GEN_TAC THEN INDUCT_TAC THENL
  [REWRITE_TAC [SUB_0; PRE];
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LE_SUC_LT] THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`m:num`; `n:num`] SUB_SUC_PRE) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC SUB_SUC THEN
   MATCH_MP_TAC LT_IMP_LE THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUB_PRESUC;;

let LEFT_SUB_DISTRIB = prove
 (`!m n p. p <= n ==> m * (n - p) = m * n - m * p`,
  REWRITE_TAC [LE_EXISTS] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2; LEFT_ADD_DISTRIB]);;

export_thm LEFT_SUB_DISTRIB;;

let RIGHT_SUB_DISTRIB = prove
 (`!m n p. n <= m ==> (m - n) * p = m * p - n * p`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN MATCH_ACCEPT_TAC LEFT_SUB_DISTRIB);;

export_thm RIGHT_SUB_DISTRIB;;

logfile "natural-div-thm";;

let EVEN_SUB = prove
 (`!m n. n <= m ==> (EVEN (m - n) <=> (EVEN(m) <=> EVEN(n)))`,
  REWRITE_TAC [LE_EXISTS] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [ADD_SUB2; EVEN_ADD] THEN
  BOOL_CASES_TAC `EVEN n` THEN
  REWRITE_TAC []);;

export_thm EVEN_SUB;;

let ODD_SUB = prove
 (`!m n. n <= m ==> (ODD (m - n) <=> ~(ODD m <=> ODD n))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`m:num`; `n:num`] EVEN_SUB) THEN
  ASM_REWRITE_TAC [GSYM NOT_EVEN] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
  BOOL_CASES_TAC `EVEN n` THEN
  REWRITE_TAC []);;

export_thm ODD_SUB;;

(* ------------------------------------------------------------------------- *)
(* The factorial function.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "natural-factorial-def";;

let (FACT_ZERO,FACT_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(FACT 0 = 1) /\
     (!n. FACT (SUC n) = (SUC n) * FACT(n))` in
  (CONJUNCT1 def, CONJUNCT2 def);;

export_thm FACT_ZERO;;
export_thm FACT_SUC;;

let FACT = CONJ FACT_ZERO FACT_SUC;;

logfile "natural-factorial-thm";;

let FACT_LT = prove
 (`!n. 0 < FACT n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[FACT; LT_MULT] THEN
  REWRITE_TAC[ONE; LT_0]);;

let FACT_LE = prove
 (`!n. 1 <= FACT n`,
  REWRITE_TAC[ONE; LE_SUC_LT; FACT_LT]);;

let FACT_NZ = prove
 (`!n. ~(FACT n = 0)`,
  REWRITE_TAC[GSYM LT_NZ; FACT_LT]);;

export_thm FACT_NZ;;

let FACT_MONO = prove
 (`!m n. m <= n ==> FACT m <= FACT n`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  SPEC_TAC(`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN
  REWRITE_TAC[FACT] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `FACT(m + d)` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(el 2 (CONJUNCTS MULT_CLAUSES))] THEN
  REWRITE_TAC[LE_MULT_RCANCEL] THEN
  REWRITE_TAC[ONE; LE_SUC; LE_0]);;

export_thm FACT_MONO;;

(* ------------------------------------------------------------------------- *)
(* More complicated theorems about exponential.                              *)
(* ------------------------------------------------------------------------- *)

logfile "natural-exp-thm";;

let EXP_LT_0 = prove
 (`!n x. 0 < x EXP n <=> ~(x = 0) \/ (n = 0)`,
  REWRITE_TAC[GSYM NOT_LE; LE; EXP_EQ_0; DE_MORGAN_THM]);;

export_thm EXP_LT_0;;

let LT_EXP = prove
 (`!x m n. x EXP m < x EXP n <=> 2 <= x /\ m < n \/
                                 (x = 0) /\ ~(m = 0) /\ (n = 0)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THENL
   [REWRITE_TAC[GSYM NOT_LT; TWO; ONE; LT] THEN
    SPEC_TAC (`n:num`,`n:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP; NOT_SUC; MULT_CLAUSES; LT] THEN
    SPEC_TAC (`m:num`,`m:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[EXP; MULT_CLAUSES; NOT_SUC; LT_REFL; LT] THEN
    REWRITE_TAC[ONE; LT_0]; ALL_TAC] THEN
  EQ_TAC THENL
   [CONV_TAC CONTRAPOS_CONV THEN
    REWRITE_TAC[NOT_LT; DE_MORGAN_THM; NOT_LE] THEN
    REWRITE_TAC[TWO; ONE; LT] THEN
    ASM_REWRITE_TAC[SYM ONE] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[EXP_ONE; LE_REFL] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
      REWRITE_RULE[LE_EXISTS]) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; EXP; LE_REFL] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `1 * x EXP (n + d)` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[MULT_CLAUSES];
      REWRITE_TAC[LE_MULT_RCANCEL] THEN
      DISJ1_TAC THEN UNDISCH_TAC `~(x = 0)` THEN
      CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
      REWRITE_TAC[ONE; LT]];
    STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o
      REWRITE_RULE[LT_EXISTS]) THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; EXP] THENL
     [MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `2 * x EXP m` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[MULT_2; LT_ADD; EXP_LT_0];
        ASM_REWRITE_TAC[LE_MULT_RCANCEL]];
      MATCH_MP_TAC LTE_TRANS THEN
      EXISTS_TAC `x EXP (m + SUC d)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_CLAUSES; EXP; MULT_ASSOC; LE_MULT_RCANCEL] THEN
      DISJ1_TAC THEN MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `x * 1` THEN CONJ_TAC THENL
       [REWRITE_TAC[MULT_CLAUSES; LE_REFL];
        REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
        UNDISCH_TAC `~(x = 0)` THEN
        CONV_TAC CONTRAPOS_CONV THEN REWRITE_TAC[NOT_LE] THEN
        REWRITE_TAC[ONE; LT]]]]);;

export_thm LT_EXP;;

let LE_EXP = prove
 (`!x m n. x EXP m <= x EXP n <=>
           if x = 0 then (m = 0) ==> (n = 0)
           else (x = 1) \/ m <= n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM NOT_LT; LT_EXP; DE_MORGAN_THM] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[TWO; LT; ONE] THEN
  CONV_TAC(EQT_INTRO o TAUT));;

export_thm LE_EXP;;

let EQ_EXP = prove
 (`!x m n. x EXP m = x EXP n <=>
           if x = 0 then (m = 0 <=> n = 0)
           else (x = 1) \/ m = n`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM LE_ANTISYM; LE_EXP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[LE_EXP] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONV_TAC TAUT);;

export_thm EQ_EXP;;

let EXP_MONO_LE_IMP = prove
 (`!x y n. x <= y ==> x EXP n <= y EXP n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[LE_MULT2; EXP; LE_REFL]);;

export_thm EXP_MONO_LE_IMP;;

let EXP_MONO_LT_IMP = prove
 (`!x y n. x < y /\ ~(n = 0) ==> x EXP n < y EXP n`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[NOT_SUC; EXP] THEN
  DISCH_TAC THEN MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `x * y EXP n` THEN
  ASM_SIMP_TAC[LT_IMP_LE; LE_MULT_LCANCEL; LT_MULT_RCANCEL; EXP_MONO_LE_IMP;
               EXP_EQ_0] THEN
  ASM_MESON_TAC[CONJUNCT1 LT]);;

export_thm EXP_MONO_LT_IMP;;

let EXP_MONO_LE = prove
 (`!x y n. x EXP n <= y EXP n <=> x <= y \/ n = 0`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[EXP; LE_REFL; EXP_MONO_LE_IMP] THEN
  ASM_MESON_TAC[NOT_LE; EXP_MONO_LT_IMP]);;

export_thm EXP_MONO_LE;;

let EXP_MONO_LT = prove
 (`!x y n. x EXP n < y EXP n <=> x < y /\ ~(n = 0)`,
  REWRITE_TAC[GSYM NOT_LE; EXP_MONO_LE; DE_MORGAN_THM]);;

export_thm EXP_MONO_LT;;

let EXP_MONO_EQ = prove
 (`!x y n. x EXP n = y EXP n <=> x = y \/ n = 0`,
  REWRITE_TAC[GSYM LE_ANTISYM; EXP_MONO_LE] THEN CONV_TAC TAUT);;

export_thm EXP_MONO_EQ;;

(* ------------------------------------------------------------------------- *)
(* Division and modulus, via existence proof of their basic property.        *)
(* ------------------------------------------------------------------------- *)

logfile "natural-div-def";;

let DIVMOD_EXIST_LEMMA = prove
 (`!m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\ r < n`,
  REPEAT STRIP_TAC THEN MP_TAC(SPEC `\r. ?q. m = q * n + r` num_WOP) THEN
  BETA_TAC THEN DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:num`; `0`]) THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:num` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `q:num`) MP_TAC) THEN
  DISCH_THEN(fun th ->
    MAP_EVERY EXISTS_TAC [`q:num`; `r:num`] THEN MP_TAC th) THEN
  CONV_TAC CONTRAPOS_CONV THEN ASM_REWRITE_TAC[NOT_LT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST_ALL_TAC o
    REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN EXISTS_TAC `d:num` THEN
  REWRITE_TAC[NOT_IMP; RIGHT_AND_EXISTS_THM] THEN
  EXISTS_TAC `q + 1` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_ASSOC; LT_ADDR] THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; LE]);;

let DIVMOD_EXIST_0_LEMMA = prove
 (`!m n. ?q r. if n = 0 then q = 0 /\ r = m
               else m = q * n + r /\ r < n`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_SIMP_TAC[DIVMOD_EXIST_LEMMA; RIGHT_EXISTS_AND_THM; EXISTS_REFL]);;

let DIVISION_0_LEMMA = new_specification ["DIV"; "MOD"]
  (REWRITE_RULE [SKOLEM_THM] DIVMOD_EXIST_0_LEMMA);;

let DIVISION_DEF_DIV = prove
 (`!m n. ~(n = 0) ==> m DIV n * n + m MOD n = m`,
  MESON_TAC[DIVISION_0_LEMMA]);;

export_thm DIVISION_DEF_DIV;;

let DIVISION_DEF_MOD = prove
 (`!m n. ~(n = 0) ==> m MOD n < n`,
  MESON_TAC[DIVISION_0_LEMMA]);;

export_thm DIVISION_DEF_MOD;;

let DIVISION = prove
 (`!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\ m MOD n < n`,
  MESON_TAC[DIVISION_DEF_DIV; DIVISION_DEF_MOD]);;

logfile "natural-div-thm";;

let DIVMOD_UNIQ_LEMMA = prove
 (`!m n q1 r1 q2 r2. ((m = q1 * n + r1) /\ r1 < n) /\
                     ((m = q2 * n + r2) /\ r2 < n)
                     ==> (q1 = q2) /\ (r1 = r2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `r1:num = r2` MP_TAC THENL
   [UNDISCH_TAC `m = q2 * n + r2` THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_THEN MP_TAC (SPECL [`q1:num`; `q2:num`] LE_CASES) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
    REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; EQ_ADD_LCANCEL] THENL
     [DISCH_TAC THEN UNDISCH_TAC `r1 < n`;
      DISCH_THEN(ASSUME_TAC o SYM) THEN UNDISCH_TAC `r2 < n`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
    SPEC_TAC(`d:num`,`d:num`) THEN INDUCT_TAC THEN
    REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES;
      GSYM NOT_LE; LE_ADD; GSYM ADD_ASSOC];
    DISCH_THEN SUBST_ALL_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN
    UNDISCH_TAC `m = q1 * n + r2` THEN
    ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_MULT_RCANCEL] THEN
    REPEAT (UNDISCH_TAC `r2 < n`) THEN
    ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[GSYM NOT_LE; LE_0]]);;

let DIVMOD_UNIQ_LEMMA2 = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC o GSYM) THEN
  MATCH_MP_TAC DIVMOD_UNIQ_LEMMA THEN
  MAP_EVERY EXISTS_TAC [`m:num`; `n:num`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC DIVISION THEN
  DISCH_TAC THEN UNDISCH_TAC `r < n` THEN
  ASM_REWRITE_TAC[GSYM NOT_LE; LE_0]);;

let MOD_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m MOD n = r)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP DIVMOD_UNIQ_LEMMA2 th]));;

export_thm MOD_UNIQ;;

let DIV_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP DIVMOD_UNIQ_LEMMA2 th]));;

export_thm DIV_UNIQ;;

let DIVMOD_UNIQ = prove
 (`!m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q) /\ (m MOD n = r)`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC
    (CONJ (SPECL [`m:num`; `n:num`; `q:num`; `r:num`] DIV_UNIQ)
          (SPECL [`m:num`; `n:num`; `q:num`; `r:num`] MOD_UNIQ)) THEN
  ASM_REWRITE_TAC []);;

let DIV_MULT,MOD_MULT = (CONJ_PAIR o prove)
 (`(!m n. ~(m = 0) ==> (m * n) DIV m = n) /\
   (!m n. ~(m = 0) ==> (m * n) MOD m = 0)`,
  SIMP_TAC[AND_FORALL_THM; TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; MULT_AC; LT_NZ]);;

export_thm DIV_MULT;;
export_thm MOD_MULT;;

let MOD_LT = prove
 (`!m n. m < n ==> (m MOD n = m)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

export_thm MOD_LT;;

let MOD_EQ = prove
 (`!m n p q. (m = n + q * p) ==> (m MOD p = n MOD p)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `p = 0` THENL
   [ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    DISCH_THEN SUBST1_TAC THEN REFL_TAC;
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOD_UNIQ THEN
    EXISTS_TAC `q + n DIV p` THEN
    POP_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM o SPEC `n:num`) THEN
    ASM_REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
    MATCH_ACCEPT_TAC ADD_SYM]);;

export_thm MOD_EQ;;

let DIV_LE = prove
 (`!m n. ~(n = 0) ==> m DIV n <= m`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [MATCH_MP DIVISION th]) THEN
  UNDISCH_TAC `~(n = 0)` THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; GSYM ADD_ASSOC; LE_ADD]);;

export_thm DIV_LE;;

let DIV_MUL_LE = prove
 (`!m n. n * (m DIV n) <= m`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `n = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LE_0] THEN
  POP_ASSUM(MP_TAC o SPEC `m:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1 th]) THEN
  REWRITE_TAC[LE_ADD; MULT_AC]);;

export_thm DIV_MUL_LE;;

let DIV_0,MOD_0 = (CONJ_PAIR o prove)
 (`(!n. ~(n = 0) ==> 0 DIV n = 0) /\
   (!n. ~(n = 0) ==> 0 MOD n = 0)`,
  SIMP_TAC[AND_FORALL_THM; TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`] THEN
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; LT_NZ]);;

export_thm DIV_0;;
export_thm MOD_0;;

let DIV_1,MOD_1 = (CONJ_PAIR o prove)
 (`(!n. n DIV 1 = n) /\ (!n. n MOD 1 = 0)`,
  SIMP_TAC[AND_FORALL_THM] THEN GEN_TAC THEN MATCH_MP_TAC DIVMOD_UNIQ THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN REWRITE_TAC[ONE; LT]);;

export_thm DIV_1;;
export_thm MOD_1;;

let DIV_LT = prove
 (`!m n. m < n ==> (m DIV n = 0)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m:num` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]);;

export_thm DIV_LT;;

let MOD_MOD = prove
 (`!m n p. ~(n * p = 0) ==> ((m MOD (n * p)) MOD n = m MOD n)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN STRIP_TAC THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
  EXISTS_TAC `m DIV (n * p) * p` THEN
  MP_TAC(SPECL [`m:num`; `n * p:num`] DIVISION) THEN
  ASM_REWRITE_TAC[MULT_EQ_0; MULT_AC; ADD_AC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]));;

export_thm MOD_MOD;;

let MOD_MOD_REFL = prove
 (`!m n. ~(n = 0) ==> ((m MOD n) MOD n = m MOD n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`m:num`; `n:num`; `1`] MOD_MOD) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; MULT_EQ_0] THEN
  REWRITE_TAC[ONE; NOT_SUC]);;

export_thm MOD_MOD_REFL;;

let DIV_MULT2 = prove
 (`!m n p. ~(m * p = 0) ==> ((m * n) DIV (m * p) = n DIV p)`,
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m * (n MOD p)` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; DIVISION] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `a * b * c:num = b * a * c`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC[GSYM DIVISION]);;

export_thm DIV_MULT2;;

let MOD_MULT2 = prove
 (`!m n p. ~(m * p = 0) ==> ((m * n) MOD (m * p) = m * n MOD p)`,
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `n DIV p` THEN
  ASM_SIMP_TAC[LT_MULT_LCANCEL; DIVISION] THEN
  ONCE_REWRITE_TAC[AC MULT_AC `a * b * c:num = b * a * c`] THEN
  REWRITE_TAC[GSYM LEFT_ADD_DISTRIB; EQ_MULT_LCANCEL] THEN
  ASM_SIMP_TAC[GSYM DIVISION]);;

export_thm MOD_MULT2;;

let MOD_EXISTS = prove
 (`!m n. (?q. m = n * q) <=> if n = 0 then (m = 0) else (m MOD n = 0)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MULT_CLAUSES] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOD_MULT] THEN
  EXISTS_TAC `m DIV n` THEN
  SUBGOAL_THEN `m = (m DIV n) * n + m MOD n`
   (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THENL
   [ASM_MESON_TAC[DIVISION]; ASM_REWRITE_TAC[ADD_CLAUSES; MULT_AC]]);;

export_thm MOD_EXISTS;;

let LE_RDIV_EQ = prove
 (`!a b n. ~(a = 0) ==> (n <= b DIV a <=> a * n <= b)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `a * (b DIV a)` THEN
    ASM_REWRITE_TAC[DIV_MUL_LE; LE_MULT_LCANCEL];
    SUBGOAL_THEN `a * n < a * (b DIV a + 1)` MP_TAC THENL
     [MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `(b DIV a) * a + b MOD a` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[DIVISION]; ALL_TAC] THEN
      SIMP_TAC[LEFT_ADD_DISTRIB; MULT_SYM; MULT_CLAUSES; LT_ADD_LCANCEL] THEN
      ASM_MESON_TAC[DIVISION];
      ASM_REWRITE_TAC[LT_MULT_LCANCEL; GSYM ADD1; LT_SUC_LE]]]);;

export_thm LE_RDIV_EQ;;

let LE_LDIV_EQ = prove
 (`!a b n. ~(a = 0) ==> (b DIV a <= n <=> b < a * (n + 1))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM NOT_LT] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM LE_SUC_LT] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN REWRITE_TAC[NOT_LT; NOT_LE; ADD1]);;

export_thm LE_LDIV_EQ;;

let LE_LDIV = prove
 (`!a b n. ~(a = 0) /\ b <= a * n ==> b DIV a <= n`,
  SIMP_TAC[LE_LDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  MESON_TAC[LT_ADD; LT_NZ; LET_TRANS]);;

export_thm LE_LDIV;;

let DIV_MONO = prove
 (`!m n p. ~(p = 0) /\ m <= n ==> m DIV p <= n DIV p`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_REFL] `(!k:num. k <= a ==> k <= b) ==> a <= b`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN ASM_MESON_TAC[LE_TRANS]);;

export_thm DIV_MONO;;

let DIV_MONO_LT = prove
 (`!m n p. ~(p = 0) /\ m + p <= n ==> m DIV p < n DIV p`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[ADD1; LE_SUC_LT; LE_REFL]
   `(!k:num. k <= a ==> k + 1 <= b) ==> a < b`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_MESON_TAC[LE_REFL; LE_TRANS; LE_ADD2; ADD_SYM]);;

export_thm DIV_MONO_LT;;

let DIV_EQ_0 = prove
 (`!m n. ~(n = 0) ==> ((m DIV n = 0) <=> m < n)`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o SPEC `m:num` o MATCH_MP DIVISION) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVISION];
    MATCH_MP_TAC DIV_UNIQ THEN EXISTS_TAC `m:num` THEN
    ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES]]);;

export_thm DIV_EQ_0;;

let MOD_EQ_0 = prove
 (`!m n. ~(n = 0) ==> ((m MOD n = 0) <=> (?q. m = q * n))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [FIRST_ASSUM(SUBST1_TAC o CONJUNCT1 o SPEC `m:num` o MATCH_MP DIVISION) THEN
    ASM_SIMP_TAC[MULT_CLAUSES; ADD_CLAUSES; DIVISION] THEN MESON_TAC[];
    MATCH_MP_TAC MOD_UNIQ THEN ASM_SIMP_TAC[ADD_CLAUSES; MULT_AC] THEN
    ASM_MESON_TAC[NOT_LE; CONJUNCT1 LE]]);;

export_thm MOD_EQ_0;;

let EVEN_MOD = prove
 (`!n. EVEN(n) <=> (n MOD 2 = 0)`,
  GEN_TAC THEN REWRITE_TAC[EVEN_EXISTS] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MATCH_MP_TAC(GSYM MOD_EQ_0) THEN REWRITE_TAC[TWO; NOT_SUC]);;

export_thm EVEN_MOD;;

let ODD_MOD = prove
 (`!n. ODD(n) <=> (n MOD 2 = 1)`,
  GEN_TAC THEN REWRITE_TAC[GSYM NOT_EVEN; EVEN_MOD] THEN
  SUBGOAL_THEN `n MOD 2 < 2` MP_TAC THENL
   [SIMP_TAC[DIVISION; TWO; NOT_SUC]; ALL_TAC] THEN
  SPEC_TAC(`n MOD 2`,`n:num`) THEN
  REWRITE_TAC[TWO; ONE; LT] THEN MESON_TAC[NOT_SUC]);;

export_thm ODD_MOD;;

let MOD_MULT_RMOD = prove
 (`!m n p. ~(n = 0) ==> ((m * (p MOD n)) MOD n = (m * p) MOD n)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
  EXISTS_TAC `m * p DIV n` THEN
  REWRITE_TAC[GSYM MULT_ASSOC; GSYM LEFT_ADD_DISTRIB] THEN
  REWRITE_TAC[EQ_MULT_LCANCEL] THEN DISJ2_TAC THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_SIMP_TAC[DIVISION]);;

export_thm MOD_MULT_RMOD;;

let MOD_MULT_LMOD = prove
 (`!m n p. ~(n = 0) ==> (((m MOD n) * p) MOD n = (m * p) MOD n)`,
  ONCE_REWRITE_TAC[MULT_SYM] THEN SIMP_TAC[MOD_MULT_RMOD]);;

export_thm MOD_MULT_LMOD;;

let MOD_MULT_MOD2 = prove
 (`!m n p. ~(n = 0) ==> (((m MOD n) * (p MOD n)) MOD n = (m * p) MOD n)`,
  SIMP_TAC[MOD_MULT_RMOD; MOD_MULT_LMOD]);;

export_thm MOD_MULT_MOD2;;

let MOD_EXP_MOD = prove
 (`!m n p. ~(n = 0) ==> (((m MOD n) EXP p) MOD n = (m EXP p) MOD n)`,
  REPEAT STRIP_TAC THEN SPEC_TAC(`p:num`,`p:num`) THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[EXP] THEN ASM_SIMP_TAC[MOD_MULT_LMOD] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `(m * ((m MOD n) EXP p) MOD n) MOD n` THEN CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_SIMP_TAC[MOD_MULT_RMOD]);;

export_thm MOD_EXP_MOD;;

let MOD_MULT_ADD = prove
 (`!m n p. (m * n + p) MOD n = p MOD n`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `m + p DIV n` THEN
  ASM_SIMP_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC; EQ_ADD_LCANCEL; DIVISION]);;

export_thm MOD_MULT_ADD;;

let DIV_MULT_ADD = prove
 (`!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `b MOD n` THEN
  REWRITE_TAC[RIGHT_ADD_DISTRIB; GSYM ADD_ASSOC] THEN
  ASM_MESON_TAC[DIVISION]);;

export_thm DIV_MULT_ADD;;

let MOD_ADD_MOD = prove
 (`!a b n. ~(n = 0) ==> ((a MOD n + b MOD n) MOD n = (a + b) MOD n)`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN
  EXISTS_TAC `a DIV n + b DIV n` THEN REWRITE_TAC[RIGHT_ADD_DISTRIB] THEN
  ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + (c + d) = (c + a) + (d + b)`] THEN
  BINOP_TAC THEN ASM_SIMP_TAC[DIVISION]);;

export_thm MOD_ADD_MOD;;

let DIV_ADD_MOD = prove
 (`!a b n. ~(n = 0)
           ==> (((a + b) MOD n = a MOD n + b MOD n) <=>
                ((a + b) DIV n = a DIV n + b DIV n))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th -> MAP_EVERY (MP_TAC o CONJUNCT1 o C SPEC th)
    [`a + b:num`; `a:num`; `b:num`]) THEN
  DISCH_THEN(fun th1 -> DISCH_THEN(fun th2 ->
    MP_TAC(MK_COMB(AP_TERM `(+)` th2,th1)))) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (funpow 2 LAND_CONV) [th]) THEN
  ONCE_REWRITE_TAC[AC ADD_AC `(a + b) + c + d = (a + c) + (b + d)`] THEN
  REWRITE_TAC[GSYM RIGHT_ADD_DISTRIB] THEN
  DISCH_THEN(fun th -> EQ_TAC THEN DISCH_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[EQ_ADD_RCANCEL; EQ_ADD_LCANCEL; EQ_MULT_RCANCEL] THEN
  REWRITE_TAC[EQ_SYM_EQ]);;

export_thm DIV_ADD_MOD;;

let DIV_REFL = prove
 (`!n. ~(n = 0) ==> (n DIV n = 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC DIV_UNIQ THEN
  EXISTS_TAC `0` THEN REWRITE_TAC[ADD_CLAUSES; MULT_CLAUSES] THEN
  POP_ASSUM MP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[LT_0]);;

export_thm DIV_REFL;;

let MOD_REFL = prove
 (`!n. ~(n = 0) ==> (n MOD n = 0)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOD_UNIQ THEN
  EXISTS_TAC `1` THEN
  ASM_REWRITE_TAC [ONE_MULT; LT_NZ; ADD_0]);;

export_thm MOD_REFL;;

let MOD_LE = prove
 (`!m n. ~(n = 0) ==> m MOD n <= m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV
   [MATCH_MP DIVISION th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN REWRITE_TAC[LE_ADD]);;

export_thm MOD_LE;;

let DIV_MONO2 = prove
 (`!m n p. ~(p = 0) /\ p <= m ==> n DIV m <= n DIV p`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `m * n DIV m` THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN ONCE_REWRITE_TAC[MULT_SYM] THEN
  MP_TAC(SPECL [`n:num`; `m:num`] DIVISION) THEN ASM_MESON_TAC[LE_ADD; LE]);;

export_thm DIV_MONO2;;

let DIV_LE_EXCLUSION = prove
 (`!a b c d. ~(b = 0) /\ b * c < (a + 1) * d ==> c DIV d <= a DIV b`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `d = 0` THEN
  ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_REFL] `(!k:num. k <= a ==> k <= b) ==> a <= b`) THEN
  X_GEN_TAC `k:num` THEN
  SUBGOAL_THEN `b * d * k <= b * c ==> (b * k) * d < (a + 1) * d` MP_TAC THENL
   [ASM_MESON_TAC[LET_TRANS; MULT_AC]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_IMP THEN
  ASM_SIMP_TAC[LE_MULT_LCANCEL; LT_MULT_RCANCEL; LE_RDIV_EQ] THEN
  REWRITE_TAC[GSYM ADD1; LT_SUC_LE]);;

export_thm DIV_LE_EXCLUSION;;

let DIV_EQ_EXCLUSION = prove
 (`!a b c d.
     b * c < (a + 1) * d /\ a * d < (c + 1) * b ==> (a DIV b = c DIV d)`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `b = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
  ASM_CASES_TAC `d = 0` THEN ASM_REWRITE_TAC[MULT_CLAUSES; LT] THEN
  ASM_MESON_TAC[MULT_SYM; LE_ANTISYM; DIV_LE_EXCLUSION]);;

export_thm DIV_EQ_EXCLUSION;;

let MULT_DIV_LE = prove
 (`!m n p. ~(p = 0) ==> m * (n DIV p) <= (m * n) DIV p`,
  REPEAT GEN_TAC THEN SIMP_TAC[LE_RDIV_EQ] THEN
  DISCH_THEN(MP_TAC o SPEC `n:num` o MATCH_MP DIVISION) THEN
  DISCH_THEN(fun th ->
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [CONJUNCT1 th]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN REWRITE_TAC[MULT_AC; LE_ADD]);;

export_thm MULT_DIV_LE;;

let DIV_DIV = prove
 (`!m n p. ~(n * p = 0) ==> ((m DIV n) DIV p = m DIV (n * p))`,
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k. k <= m <=> k <= n) ==> m = n`) THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; MULT_EQ_0; MULT_ASSOC]);;

export_thm DIV_DIV;;

let DIV_MOD = prove
 (`!m n p. ~(n * p = 0) ==> ((m DIV n) MOD p = (m MOD (n * p)) DIV n)`,
  REWRITE_TAC[MULT_EQ_0; DE_MORGAN_THM] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(MESON[LE_ANTISYM] `(!k. k <= m <=> k <= n) ==> m = n`) THEN
  X_GEN_TAC `k:num` THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `k + p * ((m DIV n) DIV p) <= (m DIV n)` THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`m DIV n`; `p:num`] DIVISION) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL [`m:num`; `n * p:num`] DIVISION) THEN
    ASM_SIMP_TAC[LE_RDIV_EQ; MULT_EQ_0; DIV_DIV; LEFT_ADD_DISTRIB]] THEN
  REWRITE_TAC[MULT_AC] THEN MESON_TAC[ADD_SYM; MULT_SYM; LE_ADD_RCANCEL]);;

export_thm DIV_MOD;;

let MOD_MOD_EXP_MIN = prove
 (`!x p m n. ~(p = 0)
             ==> x MOD (p EXP m) MOD (p EXP n) = x MOD (p EXP (MIN m n))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MIN] THEN
  ASM_CASES_TAC `m:num <= n` THEN ASM_REWRITE_TAC[] THENL
   [FIRST_X_ASSUM(CHOOSE_THEN SUBST1_TAC o GEN_REWRITE_RULE I [LE_EXISTS]) THEN
    MATCH_MP_TAC MOD_LT THEN MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `p EXP m` THEN
    ASM_SIMP_TAC[DIVISION; EXP_EQ_0; LE_EXP; LE_ADD];
    SUBGOAL_THEN `?d. m = n + d` (CHOOSE_THEN SUBST1_TAC) THENL
     [ASM_MESON_TAC[LE_CASES; LE_EXISTS];
      ASM_SIMP_TAC[EXP_ADD; MOD_MOD; MULT_EQ_0; EXP_EQ_0]]]);;

export_thm MOD_MOD_EXP_MIN;;

(* ------------------------------------------------------------------------- *)
(* Crude but useful conversion for cancelling down equations.                *)
(* ------------------------------------------------------------------------- *)

let NUM_CANCEL_CONV =
  let rec minter i l1' l2' l1 l2 =
    if l1 = [] then (i,l1',l2'@l2)
    else if l2 = [] then (i,l1@l1',l2') else
    let h1 = hd l1 and h2 = hd l2 in
    if h1 = h2 then minter (h1::i) l1' l2' (tl l1) (tl l2)
    else if h1 < h2 then minter i (h1::l1') l2' (tl l1) l2
    else minter i l1' (h2::l2') l1 (tl l2) in
  let add_tm = `(+)` and eq_tm = `(=) :num->num->bool` in
  let EQ_ADD_LCANCEL_0' =
    GEN_REWRITE_RULE (funpow 2 BINDER_CONV o LAND_CONV) [EQ_SYM_EQ]
      EQ_ADD_LCANCEL_0 in
  let AC_RULE = AC ADD_AC in
  fun tm ->
    let l,r = dest_eq tm in
    let lats = sort (<=) (binops `(+)` l)
    and rats = sort (<=) (binops `(+)` r) in
    let i,lats',rats' = minter [] [] [] lats rats in
    let l' = list_mk_binop add_tm (i @ lats')
    and r' = list_mk_binop add_tm (i @ rats') in
    let lth = AC_RULE (mk_eq(l,l'))
    and rth = AC_RULE (mk_eq(r,r')) in
    let eth = MK_COMB(AP_TERM eq_tm lth,rth) in
    GEN_REWRITE_RULE (RAND_CONV o REPEATC)
      [EQ_ADD_LCANCEL; EQ_ADD_LCANCEL_0; EQ_ADD_LCANCEL_0'] eth;;

(* ------------------------------------------------------------------------- *)
(* This is handy for easing MATCH_MP on inequalities.                        *)
(* ------------------------------------------------------------------------- *)

let LE_IMP =
  let pth = PURE_ONCE_REWRITE_RULE[IMP_CONJ] LE_TRANS in
  fun th -> GEN_ALL(MATCH_MP pth (SPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Binder for "the minimal n such that".                                     *)
(* ------------------------------------------------------------------------- *)

logfile "natural-order-min-max-def";;

parse_as_binder "minimal";;

let minimal = new_definition
  `!P. (minimal) (P:num->bool) = @n. P n /\ !m. m < n ==> ~(P m)`;;

let MINIMAL = prove
 (`!P. (?n. P n) <=> P((minimal) P) /\ (!m. m < (minimal) P ==> ~(P m))`,
  GEN_TAC THEN REWRITE_TAC[minimal] THEN CONV_TAC(RAND_CONV SELECT_CONV) THEN
  REWRITE_TAC[GSYM num_WOP]);;

export_thm MINIMAL;;

logfile "natural-order-min-max-thm";;

let MAX_REFL = prove
 (`!n. MAX n n = n`,
  REWRITE_TAC [MAX; LE_REFL]);;

export_thm MAX_REFL;;

let MAX_COMM = prove
 (`!m n. MAX m n = MAX n m`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MAX] THEN
  REPEAT COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [GSYM LE_ANTISYM];
   REFL_TAC;
   REFL_TAC;
   MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
   ASM_REWRITE_TAC []]);;

export_thm MAX_COMM;;

let LE_MAX1 = prove
 (`!m n. m <= MAX m n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MAX] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [LE_REFL]);;

export_thm LE_MAX1;;

let LE_MAX2 = prove
 (`!m n. n <= MAX m n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [MAX_COMM] THEN
  MATCH_ACCEPT_TAC LE_MAX1);;

export_thm LE_MAX2;;

let MAX_L0 = prove
 (`!n. MAX 0 n = n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MAX; LE_0; LE_REFL]);;

export_thm MAX_L0;;

let MAX_R0 = prove
 (`!n. MAX n 0 = n`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [MAX_COMM] THEN
  MATCH_ACCEPT_TAC MAX_L0);;

export_thm MAX_R0;;

let MIN_REFL = prove
 (`!n. MIN n n = n`,
  REWRITE_TAC [MIN; LE_REFL]);;

export_thm MIN_REFL;;

let MIN_COMM = prove
 (`!m n. MIN m n = MIN n m`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MIN] THEN
  REPEAT COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [GSYM LE_ANTISYM];
   REFL_TAC;
   REFL_TAC;
   MP_TAC (SPECL [`m:num`; `n:num`] LE_CASES) THEN
   ASM_REWRITE_TAC []]);;

export_thm MIN_COMM;;

let MIN_LE2 = prove
 (`!m n. MIN m n <= n`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MIN] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [LE_REFL]);;

export_thm MIN_LE2;;

let MIN_LE1 = prove
 (`!m n. MIN m n <= m`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [MIN_COMM] THEN
  MATCH_ACCEPT_TAC MIN_LE2);;

export_thm MIN_LE1;;

let MIN_L0 = prove
 (`!n. MIN 0 n = 0`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MIN; LE_0]);;

export_thm MIN_L0;;

let MIN_R0 = prove
 (`!n. MIN n 0 = 0`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [MIN_COMM] THEN
  MATCH_ACCEPT_TAC MIN_L0);;

export_thm MIN_R0;;

logfile_end ();;

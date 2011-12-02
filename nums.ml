(* ========================================================================= *)
(* The axiom of infinity; construction of the natural numbers.               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "pair.ml";;

(* ------------------------------------------------------------------------- *)
(* Declare a new type "ind" of individuals.                                  *)
(* ------------------------------------------------------------------------- *)

new_type ("ind",0);;

(* ------------------------------------------------------------------------- *)
(* We assert the axiom of infinity as in HOL88, but then we can forget it!   *)
(* ------------------------------------------------------------------------- *)

logfile "function-def";;

let ONE_ONE = new_definition
  `!(f:A->B). ONE_ONE f = !x1 x2. (f x1 = f x2) ==> (x1 = x2)`;;

export_thm ONE_ONE;;

let ONTO = new_definition
  `!(f:A->B). ONTO f = !y. ?x. y = f x`;;

export_thm ONTO;;

logfile "axiom-infinity";;

let INFINITY_AX =
  let axiom =
      let ty0 = mk_type ("ind",[]) in
      let ty1 = mk_fun_ty ty0 ty0 in
      let ty2 = mk_type ("bool",[]) in
      let ty3 = mk_fun_ty ty1 ty2 in
      let ty4 = mk_fun_ty ty2 ty2 in
      let ty5 = mk_fun_ty ty2 ty4 in
      let ty6 = mk_fun_ty ty0 ty2 in
      let tm0 = mk_var ("a",ty3) in
      let tm1 = mk_var ("b",ty4) in
      let tm2 = mk_var ("c",ty2) in
      let tm3 = mk_var ("d",ty2) in
      let tm4 = mk_abs (tm3,tm3) in
      let tm5 = mk_eq (tm4,tm4) in
      let tm6 = mk_abs (tm2,tm5) in
      let tm7 = mk_eq (tm1,tm6) in
      let tm8 = mk_abs (tm1,tm7) in
      let tm9 = mk_var ("e",ty2) in
      let tm10 = mk_var ("f",ty2) in
      let tm11 = mk_var ("g",ty2) in
      let tm12 = mk_var ("h",ty2) in
      let tm13 = mk_var ("i",ty2) in
      let tm14 = mk_var ("j",ty5) in
      let tm15 = mk_comb (tm14,tm12) in
      let tm16 = mk_comb (tm15,tm13) in
      let tm17 = mk_abs (tm14,tm16) in
      let tm18 = mk_var ("k",ty5) in
      let tm19 = mk_comb (tm18,tm5) in
      let tm20 = mk_comb (tm19,tm5) in
      let tm21 = mk_abs (tm18,tm20) in
      let tm22 = mk_eq (tm17,tm21) in
      let tm23 = mk_abs (tm13,tm22) in
      let tm24 = mk_abs (tm12,tm23) in
      let tm25 = mk_comb (tm24,tm10) in
      let tm26 = mk_comb (tm25,tm11) in
      let tm27 = mk_eq (tm26,tm10) in
      let tm28 = mk_abs (tm11,tm27) in
      let tm29 = mk_abs (tm10,tm28) in
      let tm30 = mk_var ("l",ty3) in
      let tm31 = mk_var ("m",ty1) in
      let tm32 = mk_abs (tm31,tm5) in
      let tm33 = mk_eq (tm30,tm32) in
      let tm34 = mk_abs (tm30,tm33) in
      let tm35 = mk_var ("n",ty1) in
      let tm36 = mk_comb (tm0,tm35) in
      let tm37 = mk_comb (tm29,tm36) in
      let tm38 = mk_comb (tm37,tm9) in
      let tm39 = mk_abs (tm35,tm38) in
      let tm40 = mk_comb (tm34,tm39) in
      let tm41 = mk_comb (tm29,tm40) in
      let tm42 = mk_comb (tm41,tm9) in
      let tm43 = mk_abs (tm9,tm42) in
      let tm44 = mk_comb (tm8,tm43) in
      let tm45 = mk_abs (tm0,tm44) in
      let tm46 = mk_var ("o",ty1) in
      let tm47 = mk_var ("p",ty6) in
      let tm48 = mk_var ("q",ty0) in
      let tm49 = mk_abs (tm48,tm5) in
      let tm50 = mk_eq (tm47,tm49) in
      let tm51 = mk_abs (tm47,tm50) in
      let tm52 = mk_var ("r",ty0) in
      let tm53 = mk_var ("s",ty0) in
      let tm54 = mk_comb (tm46,tm52) in
      let tm55 = mk_comb (tm46,tm53) in
      let tm56 = mk_eq (tm54,tm55) in
      let tm57 = mk_comb (tm29,tm56) in
      let tm58 = mk_eq (tm52,tm53) in
      let tm59 = mk_comb (tm57,tm58) in
      let tm60 = mk_abs (tm53,tm59) in
      let tm61 = mk_comb (tm51,tm60) in
      let tm62 = mk_abs (tm52,tm61) in
      let tm63 = mk_comb (tm51,tm62) in
      let tm64 = mk_comb (tm24,tm63) in
      let tm65 = mk_var ("t",ty2) in
      let tm66 = mk_comb (tm29,tm65) in
      let tm67 = mk_comb (tm8,tm4) in
      let tm68 = mk_comb (tm66,tm67) in
      let tm69 = mk_abs (tm65,tm68) in
      let tm70 = mk_var ("u",ty0) in
      let tm71 = mk_var ("v",ty6) in
      let tm72 = mk_var ("w",ty2) in
      let tm73 = mk_var ("x",ty0) in
      let tm74 = mk_comb (tm71,tm73) in
      let tm75 = mk_comb (tm29,tm74) in
      let tm76 = mk_comb (tm75,tm72) in
      let tm77 = mk_abs (tm73,tm76) in
      let tm78 = mk_comb (tm51,tm77) in
      let tm79 = mk_comb (tm29,tm78) in
      let tm80 = mk_comb (tm79,tm72) in
      let tm81 = mk_abs (tm72,tm80) in
      let tm82 = mk_comb (tm8,tm81) in
      let tm83 = mk_abs (tm71,tm82) in
      let tm84 = mk_var ("y",ty0) in
      let tm85 = mk_comb (tm46,tm84) in
      let tm86 = mk_eq (tm70,tm85) in
      let tm87 = mk_abs (tm84,tm86) in
      let tm88 = mk_comb (tm83,tm87) in
      let tm89 = mk_abs (tm70,tm88) in
      let tm90 = mk_comb (tm51,tm89) in
      let tm91 = mk_comb (tm69,tm90) in
      let tm92 = mk_comb (tm64,tm91) in
      let tm93 = mk_abs (tm46,tm92) in
      let tm94 = mk_comb (tm45,tm93) in
      new_axiom tm94
  in
  prove
    (`?(f:ind->ind). ONE_ONE f /\ ~(ONTO f)`,
     PURE_REWRITE_TAC
       [EXISTS_DEF; FORALL_DEF; IMP_DEF; AND_DEF; T_DEF; NOT_DEF;
        F_DEF; ONE_ONE; ONTO] THEN
     ACCEPT_TAC axiom);;

export_thm INFINITY_AX;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce constants.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "natural-def";;

let IND_SUC_0_EXISTS = prove
 (`?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\ (!x. ~(f x = z))`,
  X_CHOOSE_TAC `f:ind->ind` INFINITY_AX THEN EXISTS_TAC `f:ind->ind` THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[ONE_ONE; ONTO] THEN MESON_TAC[]);;

let IND_SUC_SPEC =
  let th1 = new_definition
   `IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\
                                (!x. ~(f x = z))` in
  let th2 = REWRITE_RULE[GSYM th1] (SELECT_RULE IND_SUC_0_EXISTS) in
  let th3 = new_definition
   `IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\
                    (!x. ~(IND_SUC x = z))` in
  REWRITE_RULE[GSYM th3] (SELECT_RULE th2);;

let IND_SUC_INJ,IND_SUC_0 = CONJ_PAIR IND_SUC_SPEC;;

(* ------------------------------------------------------------------------- *)
(* Carve out the natural numbers inductively.                                *)
(* ------------------------------------------------------------------------- *)

let NUM_REP_RULES,NUM_REP_INDUCT,NUM_REP_CASES =
  new_inductive_definition
   `NUM_REP IND_0 /\
    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))`;;

let num_tydef = new_basic_type_definition
  "num" ("mk_num","dest_num")
    (CONJUNCT1 NUM_REP_RULES);;

let ZERO_DEF = new_definition
 `_0 = mk_num IND_0`;;

let SUC_DEF = new_definition
 `SUC n = mk_num(IND_SUC(dest_num n))`;;

(* ------------------------------------------------------------------------- *)
(* Distinctness and injectivity of constructors.                             *)
(* ------------------------------------------------------------------------- *)

let NOT_SUC = prove
 (`!n. ~(SUC n = _0)`,
  REWRITE_TAC[SUC_DEF; ZERO_DEF] THEN
  MESON_TAC[NUM_REP_RULES; fst num_tydef; snd num_tydef; IND_SUC_0]);;

export_thm NOT_SUC;;

let SUC_INJ = prove
 (`!m n. SUC m = SUC n <=> m = n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUC_DEF] THEN
  EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(MP_TAC o AP_TERM `dest_num`) THEN
  SUBGOAL_THEN `!p. NUM_REP (IND_SUC (dest_num p))` MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC (CONJUNCT2 NUM_REP_RULES); ALL_TAC] THEN
  REWRITE_TAC[fst num_tydef; snd num_tydef] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[IND_SUC_INJ] THEN
  DISCH_THEN(MP_TAC o AP_TERM `mk_num`) THEN
  REWRITE_TAC[fst num_tydef]);;

export_thm SUC_INJ;;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_INDUCTION = prove
 (`!P. P(_0) /\ (!n. P(n) ==> P(SUC n)) ==> !n. P n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `\i. NUM_REP i /\ P(mk_num i):bool` NUM_REP_INDUCT) THEN
  ASM_REWRITE_TAC[GSYM ZERO_DEF; NUM_REP_RULES] THEN
  W(C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
   [REPEAT STRIP_TAC THENL
     [MATCH_MP_TAC(CONJUNCT2 NUM_REP_RULES) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `mk_num(IND_SUC i) = SUC(mk_num i)` SUBST1_TAC THENL
       [REWRITE_TAC[SUC_DEF] THEN REPEAT AP_TERM_TAC THEN
        CONV_TAC SYM_CONV THEN REWRITE_TAC[GSYM(snd num_tydef)] THEN
        FIRST_ASSUM MATCH_ACCEPT_TAC;
        FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC]];
    DISCH_THEN(MP_TAC o SPEC `dest_num n`) THEN
    REWRITE_TAC[fst num_tydef; snd num_tydef]]);;

export_thm num_INDUCTION;;

(* ------------------------------------------------------------------------- *)
(* Recursion.                                                                *)
(* ------------------------------------------------------------------------- *)

logfile "natural-thm";;

let num_Axiom = prove
 (`!(e:A) f. ?!fn. (fn _0 = e) /\
                   (!n. fn (SUC n) = f (fn n) n)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [(MP_TAC o prove_inductive_relations_exist)
      `PRG _0 e /\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))` THEN
    DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o GSYM)) THEN
    SUBGOAL_THEN `!n:num. ?!y:A. PRG n y` MP_TAC THENL
     [MATCH_MP_TAC num_INDUCTION THEN REPEAT STRIP_TAC THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC BINDER_CONV [GSYM th]) THEN
      REWRITE_TAC[GSYM NOT_SUC; NOT_SUC; SUC_INJ; EXISTS_UNIQUE_REFL] THEN
      REWRITE_TAC[UNWIND_THM1] THEN
      UNDISCH_TAC `?!y. PRG (n:num) (y:A)` THEN
      REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `y:A`) ASSUME_TAC) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [MAP_EVERY EXISTS_TAC [`(f:A->num->A) y n`; `y:A`];
        AP_THM_TAC THEN AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[UNIQUE_SKOLEM_ALT] THEN
      DISCH_THEN(X_CHOOSE_THEN `fn:num->A` (ASSUME_TAC o GSYM)) THEN
      EXISTS_TAC `fn:num->A` THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT2) THEN
      FIRST_ASSUM(fun th -> GEN_REWRITE_TAC I [GSYM th]) THEN REFL_TAC];
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    MATCH_MP_TAC num_INDUCTION THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

export_thm num_Axiom;;

(* ------------------------------------------------------------------------- *)
(* The basic numeral tag; rewrite existing instances of "_0".                *)
(* ------------------------------------------------------------------------- *)

let NUMERAL =
  let OPENTHEORY_NUMERAL_DEF = new_basic_definition
        `NUMERAL = \n. (n : num)` in
  let () = delete_const_definition ["NUMERAL"] in
  let () = delete_proof OPENTHEORY_NUMERAL_DEF in
  prove
  (`!(n:num). NUMERAL n = n`,
   REWRITE_TAC [OPENTHEORY_NUMERAL_DEF]);;

let [NOT_SUC; num_INDUCTION; num_Axiom] =
  let th = prove(`_0 = 0`,REWRITE_TAC[NUMERAL]) in
  map (GEN_REWRITE_RULE DEPTH_CONV [th])
    [NOT_SUC; num_INDUCTION; num_Axiom];;

(* ------------------------------------------------------------------------- *)
(* Induction tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let (INDUCT_TAC:tactic) =
  MATCH_MP_TAC num_INDUCTION THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN DISCH_TAC];;

let num_RECURSION =
  let avs = fst(strip_forall(concl num_Axiom)) in
  GENL avs (EXISTENCE (SPECL avs num_Axiom));;

(* ------------------------------------------------------------------------- *)
(* Cases theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let num_CASES = prove
 (`!m. (m = 0) \/ (?n. m = SUC n)`,
  INDUCT_TAC THEN MESON_TAC[]);;

export_thm num_CASES;;

(* ------------------------------------------------------------------------- *)
(* Augmenting inductive type store.                                          *)
(* ------------------------------------------------------------------------- *)

let num_RECURSION_STD = prove
 (`!e:Z f. ?fn. (fn 0 = e) /\ (!n. fn (SUC n) = f n (fn n))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`e:Z`; `(\z n. (f:num->Z->Z) n z)`] num_RECURSION) THEN
  REWRITE_TAC[]);;

inductive_type_store :=
 ("num",(2,num_INDUCTION,num_RECURSION_STD))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* "Bitwise" binary representation of numerals.                              *)
(* ------------------------------------------------------------------------- *)

logfile "natural-numeral";;

let (BIT0_ZERO,BIT0_SUC) =
  let def = new_definition
    `BIT0 = @fn. fn 0 = 0 /\ (!n. fn (SUC n) = SUC (SUC (fn n)))`
  and th = BETA_RULE(ISPECL [`0`; `\m n:num. SUC (SUC m)`] num_RECURSION) in
  CONJ_PAIR (REWRITE_RULE [GSYM def] (SELECT_RULE th));;

export_thm BIT0_ZERO;;
export_thm BIT0_SUC;;

let BIT0_DEF = CONJ BIT0_ZERO BIT0_SUC;;

let BIT1_DEF = new_definition
 `!n. BIT1 n = SUC (BIT0 n)`;;

export_thm BIT1_DEF;;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on numerals.                                            *)
(* ------------------------------------------------------------------------- *)

let mk_numeral =
  let Z = mk_const("_0",[])
  and BIT0 = mk_const("BIT0",[])
  and BIT1 = mk_const("BIT1",[])
  and NUMERAL = mk_const("NUMERAL",[])
  and zero = num_0 in
  let rec mk_num n =
    if n =/ num_0 then Z else
    mk_comb((if mod_num n num_2 =/ num_0 then BIT0 else BIT1),
            mk_num(quo_num n num_2)) in
  fun n -> if n </ zero then failwith "mk_numeral: negative argument"
           else mk_comb(NUMERAL,mk_num n);;

let mk_small_numeral n = mk_numeral(Int n);;

let dest_small_numeral t = Num.int_of_num(dest_numeral t);;

let is_numeral = can dest_numeral;;

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(*                                                                           *)
(* This is put here because we use numerals as tags to force different       *)
(* constants specified with equivalent theorems to have different underlying *)
(* definitions, ensuring that there are no provable equalities between them  *)
(* and so in some sense the constants are "underspecified" as the user might *)
(* want for some applications.                                               *)
(* ------------------------------------------------------------------------- *)

let the_specifications = ref [];;

let new_specification =
  let check_distinct l =
    try itlist (fun t res -> if mem t res then fail() else t::res) l []; true
    with Failure _ -> false in
  let specify n name th =
    let ntm = mk_numeral n in
    let gv = genvar(type_of ntm) in
    let th0 = CONV_RULE(REWR_CONV SKOLEM_THM) (GEN gv th) in
    let th1 = CONV_RULE(RATOR_CONV (REWR_CONV EXISTS_THM) THENC
                        BETA_CONV) th0 in
    let l,r = dest_comb(concl th1) in
    let rn = mk_comb(r,ntm) in
    let ty = type_of rn in
    let th2 = new_definition(mk_eq(mk_var(name,ty),rn)) in
    GEN_REWRITE_RULE ONCE_DEPTH_CONV [GSYM th2]
     (SPEC ntm (CONV_RULE BETA_CONV th1)) in
  let rec specifies n names th =
    match names with
      [] -> th
    | name::onames -> let th' = specify n name th in
                      specifies (n +/ Int 1) onames th' in
  let specification_counter = ref(Int 0) in
  fun names th ->
    let asl,c = dest_thm th in
    if not (asl = []) then
      failwith "new_specification: Assumptions not allowed in theorem" else
    if not (frees c = []) then
      failwith "new_specification: Free variables in predicate" else
    let avs = fst(strip_exists c) in
    if length names = 0 or length names > length avs then
      failwith "new_specification: Unsuitable number of constant names" else
    if not (check_distinct names) then
      failwith "new_specification: Constant names not distinct"
    else
      try let sth = snd(find (fun ((names',th'),sth') ->
                               names' = names & aconv (concl th') (concl th))
                             (!the_specifications)) in
          warn true ("Benign respecification"); sth
      with Failure _ ->
          let sth = specifies (!specification_counter) names th in
          the_specifications := ((names,th),sth)::(!the_specifications);
          specification_counter := !specification_counter +/ Int(length names);
          sth;;

logfile_end ();;

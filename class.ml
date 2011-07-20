(* ========================================================================= *)
(* Extensional, classical reasoning with AC starts now!                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "ind_defs.ml";;

(* ------------------------------------------------------------------------- *)
(* Eta-axiom, corresponding conversion, and extensionality.                  *)
(* ------------------------------------------------------------------------- *)

logfile "axiom-extensionality";;

let ETA_AX =
  let axiom =
      let ty0 = mk_vartype "A" in
      let ty1 = mk_vartype "B" in
      let ty2 = mk_fun_ty ty0 ty1 in
      let ty3 = mk_type ("bool",[]) in
      let ty4 = mk_fun_ty ty2 ty3 in
      let tm0 = mk_var ("a",ty4) in
      let tm1 = mk_var ("b",ty2) in
      let tm2 = mk_var ("c",ty3) in
      let tm3 = mk_abs (tm2,tm2) in
      let tm4 = mk_eq (tm3,tm3) in
      let tm5 = mk_abs (tm1,tm4) in
      let tm6 = mk_eq (tm0,tm5) in
      let tm7 = mk_abs (tm0,tm6) in
      let tm8 = mk_var ("d",ty2) in
      let tm9 = mk_var ("e",ty0) in
      let tm10 = mk_comb (tm8,tm9) in
      let tm11 = mk_abs (tm9,tm10) in
      let tm12 = mk_eq (tm11,tm8) in
      let tm13 = mk_abs (tm8,tm12) in
      let tm14 = mk_comb (tm7,tm13) in
      new_axiom tm14
  in
  prove
    (`!(t:A->B). (\x. t x) = t`,
     PURE_REWRITE_TAC [FORALL_DEF; T_DEF] THEN
     ACCEPT_TAC axiom);;

export_thm ETA_AX;;

let ETA_CONV =
  let t = `t:A->B` in
  let pth = prove(`(\x. (t:A->B) x) = t`,MATCH_ACCEPT_TAC ETA_AX) in
  fun tm ->
    try let bv,bod = dest_abs tm in
        let l,r = dest_comb bod in
        if r = bv & not (vfree_in bv l) then
          TRANS (REFL tm) (PINST [type_of bv,aty; type_of bod,bty] [l,t] pth)
        else fail()
    with Failure _ -> failwith "ETA_CONV";;

logfile "bool-ext";;

let EQ_EXT = prove
 (`!(f:A->B) g. (!x. f x = g x) ==> f = g`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o ABS `x:A` o SPEC `x:A`) THEN
  REWRITE_TAC[ETA_AX]);;

export_thm EQ_EXT;;

let FUN_EQ_THM = prove
 (`!(f:A->B) g. f = g <=> (!x. f x = g x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN SUBST1_TAC THEN GEN_TAC THEN REFL_TAC;
    MATCH_ACCEPT_TAC EQ_EXT]);;

export_thm FUN_EQ_THM;;

(* ------------------------------------------------------------------------- *)
(* Indefinite descriptor (giving AC).                                        *)
(* ------------------------------------------------------------------------- *)

logfile "axiom-choice";;

new_constant("@",`:(A->bool)->A`);;

parse_as_binder "@";;

let is_select = is_binder "@";;
let dest_select = dest_binder "@";;
let mk_select = mk_binder "@";;

let SELECT_AX =
  let axiom =
      let ty0 = mk_vartype "A" in
      let ty1 = mk_type ("bool",[]) in
      let ty2 = mk_fun_ty ty0 ty1 in
      let ty3 = mk_fun_ty ty2 ty1 in
      let ty4 = mk_fun_ty ty1 ty1 in
      let ty5 = mk_fun_ty ty1 ty4 in
      let tm0 = mk_var ("a",ty3) in
      let tm1 = mk_var ("b",ty2) in
      let tm2 = mk_var ("c",ty1) in
      let tm3 = mk_abs (tm2,tm2) in
      let tm4 = mk_eq (tm3,tm3) in
      let tm5 = mk_abs (tm1,tm4) in
      let tm6 = mk_eq (tm0,tm5) in
      let tm7 = mk_abs (tm0,tm6) in
      let tm8 = mk_var ("d",ty2) in
      let tm9 = mk_var ("e",ty2) in
      let tm10 = mk_var ("f",ty0) in
      let tm11 = mk_abs (tm10,tm4) in
      let tm12 = mk_eq (tm9,tm11) in
      let tm13 = mk_abs (tm9,tm12) in
      let tm14 = mk_var ("g",ty0) in
      let tm15 = mk_var ("h",ty1) in
      let tm16 = mk_var ("i",ty1) in
      let tm17 = mk_var ("j",ty1) in
      let tm18 = mk_var ("k",ty1) in
      let tm19 = mk_var ("l",ty5) in
      let tm20 = mk_comb (tm19,tm17) in
      let tm21 = mk_comb (tm20,tm18) in
      let tm22 = mk_abs (tm19,tm21) in
      let tm23 = mk_var ("m",ty5) in
      let tm24 = mk_comb (tm23,tm4) in
      let tm25 = mk_comb (tm24,tm4) in
      let tm26 = mk_abs (tm23,tm25) in
      let tm27 = mk_eq (tm22,tm26) in
      let tm28 = mk_abs (tm18,tm27) in
      let tm29 = mk_abs (tm17,tm28) in
      let tm30 = mk_comb (tm29,tm15) in
      let tm31 = mk_comb (tm30,tm16) in
      let tm32 = mk_eq (tm31,tm15) in
      let tm33 = mk_abs (tm16,tm32) in
      let tm34 = mk_abs (tm15,tm33) in
      let tm35 = mk_comb (tm8,tm14) in
      let tm36 = mk_comb (tm34,tm35) in
      let tm37 = mk_const ("@",[]) in
      let tm38 = mk_comb (tm37,tm8) in
      let tm39 = mk_comb (tm8,tm38) in
      let tm40 = mk_comb (tm36,tm39) in
      let tm41 = mk_abs (tm14,tm40) in
      let tm42 = mk_comb (tm13,tm41) in
      let tm43 = mk_abs (tm8,tm42) in
      let tm44 = mk_comb (tm7,tm43) in
      new_axiom tm44
  in
  prove
    (`!p (x:A). p x ==> p ((@) p)`,
     PURE_REWRITE_TAC [FORALL_DEF; IMP_DEF; AND_DEF; T_DEF] THEN
     ACCEPT_TAC axiom);;

export_thm SELECT_AX;;

(* ------------------------------------------------------------------------- *)
(* Useful for compatibility. (The old EXISTS_DEF.)                           *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let EXISTS_THM = prove
 (`(?) = \P:A->bool. P ((@) P)`,
  MATCH_MP_TAC EQ_EXT THEN BETA_TAC THEN X_GEN_TAC `P:A->bool` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN MP_TAC) THEN MATCH_ACCEPT_TAC SELECT_AX;
    DISCH_TAC THEN EXISTS_TAC `((@) P):A` THEN POP_ASSUM ACCEPT_TAC]);;

export_thm EXISTS_THM;;

(* ------------------------------------------------------------------------- *)
(* Rules and so on for the select operator.                                  *)
(* ------------------------------------------------------------------------- *)

let SELECT_RULE =
  let P = `P:A->bool` in
  let pth = prove
   (`(?) (P:A->bool) ==> P((@) P)`,
    SIMP_TAC[SELECT_AX; ETA_AX]) in
  fun th ->
    try let abs = rand(concl th) in
        let ty = type_of(bndvar abs) in
        CONV_RULE BETA_CONV (MP (PINST [ty,aty] [abs,P] pth) th)
    with Failure _ -> failwith "SELECT_RULE";;

let SELECT_CONV =
  let P = `P:A->bool` in
  let pth = prove
   (`(P:A->bool)((@) P) = (?) P`,
    REWRITE_TAC[EXISTS_THM] THEN BETA_TAC THEN REFL_TAC) in
   fun tm ->
     try let is_epsok t = is_select t &
                          let bv,bod = dest_select t in
                          aconv tm (vsubst [t,bv] bod) in
         let pickeps = find_term is_epsok tm in
         let abs = rand pickeps in
         let ty = type_of (bndvar abs) in
         CONV_RULE (LAND_CONV BETA_CONV) (PINST [ty,aty] [abs,P] pth)
     with Failure _ -> failwith "SELECT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Some basic theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let SELECT_REFL = prove
 (`!x:A. (@y. y = x) = x`,
  GEN_TAC THEN CONV_TAC SELECT_CONV THEN
  EXISTS_TAC `x:A` THEN REFL_TAC);;

export_thm SELECT_REFL;;

let SELECT_UNIQUE = prove
 (`!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
  ASM_REWRITE_TAC[SELECT_REFL]);;

export_thm SELECT_UNIQUE;;

extend_basic_rewrites [SELECT_REFL];;

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(* ------------------------------------------------------------------------- *)

let the_specifications = ref [];;

let new_specification =
  let SEL_RULE =
    CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV) in
  let check_distinct l =
    try itlist (fun t res -> if mem t res then fail() else t::res) l []; true
    with Failure _ -> false in
  let specify name th =
    let th1 = SEL_RULE th in
    let l,r = dest_comb(concl th1) in
    let ty = type_of r in
    let th2 = new_definition(mk_eq(mk_var(name,ty),r)) in
    CONV_RULE BETA_CONV (EQ_MP (AP_TERM l (SYM th2)) th1) in
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
          let sth = rev_itlist specify names th in
          the_specifications := ((names,th),sth)::(!the_specifications); sth;;

(* ------------------------------------------------------------------------- *)
(* Now we can derive type definitions from existence; check benignity.       *)
(* ------------------------------------------------------------------------- *)

let the_type_definitions = ref ([]:((string*string*string)*(thm*thm))list);;

let new_type_definition tyname (absname,repname) th =
  try let th',tth' = assoc (tyname,absname,repname) (!the_type_definitions) in
      if concl th' <> concl th then failwith "" else
      (warn true "Benign redefinition of type"; tth')
  with Failure _ ->
    let th0 =
     CONV_RULE (RATOR_CONV (REWR_CONV EXISTS_THM) THENC BETA_CONV) th in
    let th1,th2 = new_basic_type_definition tyname (absname,repname) th0 in
    let tth = CONJ (GEN_ALL th1)
                   (GEN_ALL (CONV_RULE(LAND_CONV (TRY_CONV BETA_CONV)) th2)) in
    the_type_definitions := ((tyname,absname,repname),(th,tth))::
                            (!the_type_definitions);
    tth;;

(* ------------------------------------------------------------------------- *)
(* Derive excluded middle (the proof is from Beeson's book).                 *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let EXCLUDED_MIDDLE = prove
 (`!t. t \/ ~t`,
  GEN_TAC THEN SUBGOAL_THEN
   `(((@x. (x <=> F) \/ t) <=> F) \/ t) /\ (((@x. (x <=> T) \/ t) <=> T) \/ t)`
  MP_TAC THENL
   [CONJ_TAC THEN CONV_TAC SELECT_CONV THENL
     [EXISTS_TAC `F`; EXISTS_TAC `T`] THEN
    DISJ1_TAC THEN REFL_TAC;
    DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    TRY(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN
    DISJ2_TAC THEN DISCH_TAC THEN MP_TAC(ITAUT `~(T <=> F)`) THEN
    PURE_ONCE_ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[ITAUT `p \/ T <=> T`]]);;

export_thm EXCLUDED_MIDDLE;;

let BOOL_CASES_AX = prove
 (`!t. (t <=> T) \/ (t <=> F)`,
  GEN_TAC THEN DISJ_CASES_TAC(SPEC `t:bool` EXCLUDED_MIDDLE) THEN
  ASM_REWRITE_TAC[]);;

export_thm BOOL_CASES_AX;;

(* ------------------------------------------------------------------------- *)
(* Classically based tactics. (See also COND_CASES_TAC later on.)            *)
(* ------------------------------------------------------------------------- *)

let BOOL_CASES_TAC p = STRUCT_CASES_TAC (SPEC p BOOL_CASES_AX);;

let ASM_CASES_TAC t = DISJ_CASES_TAC(SPEC t EXCLUDED_MIDDLE);;

(* ------------------------------------------------------------------------- *)
(* Set up a reasonable tautology checker for classical logic.                *)
(* ------------------------------------------------------------------------- *)

let TAUT =
  let PROP_REWRITE_TAC = REWRITE_TAC[] in
  let RTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty & can (find_term is_var) t & free_in t w in
    (PROP_REWRITE_TAC THEN
     W((fun t1 t2 -> t1 THEN t2) (REWRITE_TAC[]) o BOOL_CASES_TAC o
       hd o sort free_in o find_terms ok o snd)) (asl,w) in
  let TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN REPEAT RTAUT_TAC in
  fun tm -> prove(tm,TAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A few useful classical tautologies.                                       *)
(* ------------------------------------------------------------------------- *)

let DE_MORGAN_THM = TAUT
  `!t1 t2. (~(t1 /\ t2) <=> ~t1 \/ ~t2) /\ (~(t1 \/ t2) <=> ~t1 /\ ~t2)`;;

export_thm DE_MORGAN_THM;;

let NOT_CLAUSES =
  TAUT `(!t. ~ ~t <=> t) /\ (~T <=> F) /\ (~F <=> T)`;;

export_thm NOT_CLAUSES;;

let NOT_IMP = TAUT `!t1 t2. ~(t1 ==> t2) <=> t1 /\ ~t2`;;

export_thm NOT_IMP;;

let CONTRAPOS_THM = TAUT `!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)`;;

export_thm CONTRAPOS_THM;;

extend_basic_rewrites [CONJUNCT1 NOT_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Some classically based rules.                                             *)
(* ------------------------------------------------------------------------- *)

let CCONTR =
  let P = `P:bool` in
  let pth = TAUT `(~P ==> F) ==> P` in
  fun tm th ->
    try let tm' = mk_neg tm in
        MP (INST [tm,P] pth) (DISCH tm' th)
    with Failure _ -> failwith "CCONTR";;

let CONTRAPOS_CONV =
  let a = `a:bool` and b = `b:bool` in
  let pth = TAUT `(a ==> b) <=> (~b ==> ~a)` in
  fun tm ->
    try let P,Q = dest_imp tm in
        INST [P,a; Q,b] pth
    with Failure _ -> failwith "CONTRAPOS_CONV";;

(* ------------------------------------------------------------------------- *)
(* A classicalal "refutation" tactic.                                        *)
(* ------------------------------------------------------------------------- *)

let REFUTE_THEN =
  let f_tm = `F`
  and conv =
    let pth = TAUT `p <=> ~p ==> F` in
    REWR_CONV pth in
  fun ttac (asl,w as gl) ->
    if w = f_tm then ALL_TAC gl
    else if is_neg w then DISCH_THEN ttac gl
    else (CONV_TAC conv THEN DISCH_THEN ttac) gl;;

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let NOT_EXISTS_THM = prove
 (`!P. ~(?x:A. P x) <=> (!x. ~(P x))`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~(?x:A. P x)` THEN
    REWRITE_TAC[] THEN EXISTS_TAC `x:A` THEN POP_ASSUM ACCEPT_TAC;
    DISCH_THEN(CHOOSE_THEN MP_TAC) THEN ASM_REWRITE_TAC[]]);;

export_thm NOT_EXISTS_THM;;

let EXISTS_NOT_THM = prove
 (`!P. (?x:A. ~(P x)) <=> ~(!x. P x)`,
  ONCE_REWRITE_TAC[TAUT `(a <=> ~b) <=> (~a <=> b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM]);;

export_thm EXISTS_NOT_THM;;

let NOT_FORALL_THM = prove
 (`!P. ~(!x. P x) <=> (?x:A. ~(P x))`,
  MATCH_ACCEPT_TAC(GSYM EXISTS_NOT_THM));;

export_thm NOT_FORALL_THM;;

let FORALL_NOT_THM = prove
 (`!P. (!x. ~(P x)) <=> ~(?x:A. P x)`,
  MATCH_ACCEPT_TAC(GSYM NOT_EXISTS_THM));;

export_thm FORALL_NOT_THM;;

(* ------------------------------------------------------------------------- *)
(* Expand quantification over Booleans.                                      *)
(* ------------------------------------------------------------------------- *)

let FORALL_BOOL_THM = prove
  (`!P. (!b. P b) <=> P T /\ P F`,
   GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
   GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN ASM_REWRITE_TAC[]);;

export_thm FORALL_BOOL_THM;;

let EXISTS_BOOL_THM = prove
 (`!P. (?b. P b) <=> P T \/ P F`,
  GEN_TAC THEN MATCH_MP_TAC(TAUT `(~p <=> ~q) ==> (p <=> q)`) THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM; FORALL_BOOL_THM]);;

export_thm EXISTS_BOOL_THM;;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

let LEFT_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P x \/ Q) <=> (!x. P x) \/ Q`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; DE_MORGAN_THM; LEFT_EXISTS_AND_THM]);;

export_thm LEFT_FORALL_OR_THM;;

let RIGHT_FORALL_OR_THM = prove
 (`!P Q. (!x:A. P \/ Q x) <=> P \/ (!x. Q x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_FORALL_THM; DE_MORGAN_THM; RIGHT_EXISTS_AND_THM]);;

export_thm RIGHT_FORALL_OR_THM;;

let LEFT_OR_FORALL_THM = prove
 (`!P Q. (!x:A. P x) \/ Q <=> (!x. P x \/ Q)`,
  MATCH_ACCEPT_TAC(GSYM LEFT_FORALL_OR_THM));;

export_thm LEFT_OR_FORALL_THM;;

let RIGHT_OR_FORALL_THM = prove
 (`!P Q. P \/ (!x:A. Q x) <=> (!x. P \/ Q x)`,
  MATCH_ACCEPT_TAC(GSYM RIGHT_FORALL_OR_THM));;

export_thm RIGHT_OR_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let LEFT_IMP_FORALL_THM = prove
 (`!P Q. ((!x:A. P x) ==> Q) <=> (?x. P x ==> Q)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_IMP; LEFT_AND_FORALL_THM]);;

export_thm LEFT_IMP_FORALL_THM;;

let LEFT_EXISTS_IMP_THM = prove
 (`!P Q. (?x. P x ==> Q) <=> ((!x:A. P x) ==> Q)`,
  MATCH_ACCEPT_TAC(GSYM LEFT_IMP_FORALL_THM));;

export_thm LEFT_EXISTS_IMP_THM;;

let RIGHT_IMP_EXISTS_THM = prove
 (`!P Q. (P ==> ?x:A. Q x) <=> (?x:A. P ==> Q x)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[TAUT `(a <=> b) <=> (~a <=> ~b)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM; NOT_IMP; RIGHT_AND_FORALL_THM]);;

export_thm RIGHT_IMP_EXISTS_THM;;

let RIGHT_EXISTS_IMP_THM = prove
 (`!P Q. (?x:A. P ==> Q x) <=> (P ==> ?x:A. Q x)`,
  MATCH_ACCEPT_TAC(GSYM RIGHT_IMP_EXISTS_THM));;

export_thm RIGHT_EXISTS_IMP_THM;;

(* ------------------------------------------------------------------------- *)
(* The conditional.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "bool-def";;

let COND_DEF = new_definition
  `COND = \t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\
                          ((t <=> F) ==> (x = t2))`;;

export_thm COND_DEF;;

logfile "bool-class";;

let COND_CLAUSES = prove
 (`!(t1:A) t2. ((if T then t1 else t2) = t1) /\
               ((if F then t1 else t2) = t2)`,
  REWRITE_TAC[COND_DEF]);;

export_thm COND_CLAUSES;;

let is_cond tm =
  try fst(dest_const(rator(rator (rator tm)))) = "COND"
  with Failure _ -> false;;

let mk_cond (b,x,y) =
  try let c = mk_const("COND",[type_of x,aty]) in
      mk_comb(mk_comb(mk_comb(c,b),x),y)
  with Failure _ -> failwith "mk_cond";;

let dest_cond tm =
  try let tm1,y = dest_comb tm in
      let tm2,x = dest_comb tm1 in
      let c,b = dest_comb tm2 in
      if fst(dest_const c) = "COND" then (b,(x,y)) else fail()
  with Failure _ -> failwith "dest_cond";;

extend_basic_rewrites [COND_CLAUSES];;

logfile "bool-class";;

let COND_EXPAND = prove
 (`!b t1 t2. (if b then t1 else t2) <=> (~b \/ t1) /\ (b \/ t2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  REWRITE_TAC[]);;

export_thm COND_EXPAND;;

let COND_ID = prove
 (`!b (t:A). (if b then t else t) = t`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

export_thm COND_ID;;

let COND_RAND = prove
 (`!b (f:A->B) x y. f (if b then x else y) = (if b then f x else f y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

export_thm COND_RAND;;

let COND_RATOR = prove
 (`!b (f:A->B) g x. (if b then f else g)(x) = (if b then f x else g x)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

export_thm COND_RATOR;;

let COND_ABS = prove
 (`!b (f:A->B) g. (\x. if b then f x else g x) = (if b then f else g)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[ETA_AX]);;

export_thm COND_ABS;;

(* ------------------------------------------------------------------------- *)
(* Redefine TAUT to freeze in the rewrites including COND.                   *)
(* ------------------------------------------------------------------------- *)

let TAUT =
  let PROP_REWRITE_TAC = REWRITE_TAC[] in
  let RTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty & can (find_term is_var) t & free_in t w in
    (PROP_REWRITE_TAC THEN
     W((fun t1 t2 -> t1 THEN t2) (REWRITE_TAC[]) o BOOL_CASES_TAC o
       hd o sort free_in o find_terms ok o snd)) (asl,w) in
  let TAUT_TAC = REPEAT(GEN_TAC ORELSE CONJ_TAC) THEN REPEAT RTAUT_TAC in
  fun tm -> prove(tm,TAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

let MONO_COND = prove
 (`!b A B C D.
     (A ==> B) /\ (C ==> D) ==>
     (if b then A else C) ==> (if b then B else D)`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN BOOL_CASES_TAC `b:bool` THEN
  ASM_REWRITE_TAC[]);;

export_thm MONO_COND;;

monotonicity_theorems := MONO_COND::(!monotonicity_theorems);;

(* ------------------------------------------------------------------------- *)
(* Tactic for splitting over an arbitrarily chosen conditional.              *)
(* ------------------------------------------------------------------------- *)

let COND_ELIM_THM = prove
 (`!P c x y.
     (P:A->bool) (if c then x else y) <=> (c ==> P x) /\ (~c ==> P y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `c:bool` THEN REWRITE_TAC[]);;

export_thm COND_ELIM_THM;;

let COND_ELIM_CONV = HIGHER_REWRITE_CONV[COND_ELIM_THM] true;;

let (COND_CASES_TAC :tactic) =
  let pth = TAUT `~ ~ p <=> p` in
  let DENEG_RULE = GEN_REWRITE_RULE I [pth] in
  CONV_TAC COND_ELIM_CONV THEN CONJ_TAC THENL
    [DISCH_THEN(fun th -> ASSUME_TAC th THEN SUBST1_TAC(EQT_INTRO th));
     DISCH_THEN(fun th -> try let th' = DENEG_RULE th in
                              ASSUME_TAC th' THEN SUBST1_TAC(EQT_INTRO th')
                          with Failure _ ->
                              ASSUME_TAC th THEN SUBST1_TAC(EQF_INTRO th))];;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let SKOLEM_THM = prove
 (`!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))`,
  REPEAT(STRIP_TAC ORELSE EQ_TAC) THENL
   [EXISTS_TAC `\x:A. @y:B. P x y` THEN GEN_TAC THEN
    BETA_TAC THEN CONV_TAC SELECT_CONV;
    EXISTS_TAC `(y:A->B) x`] THEN
  POP_ASSUM MATCH_ACCEPT_TAC);;

export_thm SKOLEM_THM;;

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intutionistically and intensionally.                 *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_ALT = prove
 (`!P:A->B->bool. (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y)`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT; SKOLEM_THM]);;

export_thm UNIQUE_SKOLEM_ALT;;

(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

let UNIQUE_SKOLEM_THM = prove
 (`!P. (!x:A. ?!y:B. P x y) <=> (?!f. !x. P x (f x))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM; SKOLEM_THM; FORALL_AND_THM] THEN
  EQ_TAC THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[FUN_EQ_THM] THEN
    X_GEN_TAC `x:A` THEN FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x:A` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`x:A`; `y1:B`; `y2:B`] THEN STRIP_TAC THEN
    FIRST_ASSUM(X_CHOOSE_TAC `f:A->B`) THEN
    SUBGOAL_THEN `(\z. if z = x then y1 else (f:A->B) z) =
                  (\z. if z = x then y2 else (f:A->B) z)` MP_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      REPEAT STRIP_TAC THEN BETA_TAC THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(MP_TAC o C AP_THM `x:A`) THEN REWRITE_TAC[]]]);;

export_thm UNIQUE_SKOLEM_THM;;

(* ------------------------------------------------------------------------- *)
(* Extend default congruences for contextual rewriting.                      *)
(* ------------------------------------------------------------------------- *)

let COND_CONG =
  TAUT `(g = g') ==>
        (g' ==> ((t:A) = t')) ==>
        (~g' ==> (e = e')) ==>
        ((if g then t else e) = (if g' then t' else e'))` in
  extend_basic_congs [COND_CONG];;

let COND_EQ_CLAUSE = prove
 (`(if (x:A) = x then (y:B) else z) = y`,
  REWRITE_TAC[]) in
 extend_basic_rewrites [COND_EQ_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* We can now treat "bool" as an enumerated type for some purposes.          *)
(* ------------------------------------------------------------------------- *)

logfile "bool-class";;

let bool_INDUCT = prove
 (`!P. P F /\ P T ==> !x. P x`,
  REPEAT STRIP_TAC THEN DISJ_CASES_TAC(SPEC `x:bool` BOOL_CASES_AX) THEN
  ASM_REWRITE_TAC[]);;

export_thm bool_INDUCT;;

let bool_RECURSION = prove
 (`!a b:A. ?f. f F = a /\ f T = b`,
  REPEAT GEN_TAC THEN EXISTS_TAC `\x. if x then b:A else a` THEN
  REWRITE_TAC[]);;

export_thm bool_RECURSION;;

let inductive_type_store = ref
 ["bool",(2,bool_INDUCT,bool_RECURSION)];;

logfile_end ();;

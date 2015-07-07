(* ========================================================================= *)
(* Additional theorems, mainly about quantifiers, and additional tactics.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

needs "simp.ml";;

(* ------------------------------------------------------------------------- *)
(* More stuff about equality.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "bool-int";;

let EQ_REFL = prove
 (`!x:A. x = x`,
  GEN_TAC THEN REFL_TAC);;

export_thm EQ_REFL;;

let REFL_CLAUSE = prove
 (`!x:A. (x = x) <=> T`,
  GEN_TAC THEN MATCH_ACCEPT_TAC(EQT_INTRO(SPEC_ALL EQ_REFL)));;

let EQ_SYM = prove
 (`!(x:A) y. (x = y) ==> (y = x)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ACCEPT_TAC o SYM));;

export_thm EQ_SYM;;

let EQ_SYM_EQ = prove
 (`!(x:A) y. (x = y) <=> (y = x)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN MATCH_ACCEPT_TAC EQ_SYM);;

export_thm EQ_SYM_EQ;;

let EQ_TRANS = prove
 (`!(x:A) y z. (x = y) /\ (y = z) ==> (x = z)`,
  REPEAT STRIP_TAC THEN PURE_ASM_REWRITE_TAC[] THEN REFL_TAC);;

export_thm EQ_TRANS;;

(* ------------------------------------------------------------------------- *)
(* The following is a common special case of ordered rewriting.              *)
(* ------------------------------------------------------------------------- *)

let AC acsuite = EQT_ELIM o PURE_REWRITE_CONV[acsuite; REFL_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* A couple of theorems about beta reduction.                                *)
(* ------------------------------------------------------------------------- *)

let BETA_THM = prove
 (`!(f:A->B) y. (\x. (f:A->B) x) y = f y`,
  REPEAT GEN_TAC THEN BETA_TAC THEN REFL_TAC);;

export_thm BETA_THM;;

let ABS_SIMP = prove
 (`!(t1:A) (t2:B). (\x. t1) t2 = t1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[BETA_THM; REFL_CLAUSE]);;

export_thm ABS_SIMP;;

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)

let CONJ_ASSOC' = prove
 (`!t1 t2 t3. (t1 /\ t2) /\ t3 <=> t1 /\ (t2 /\ t3)`,
  ITAUT_TAC);;

export_thm CONJ_ASSOC';;

let CONJ_ASSOC = GSYM CONJ_ASSOC';;

let CONJ_SYM = prove
 (`!t1 t2. t1 /\ t2 <=> t2 /\ t1`,
  ITAUT_TAC);;

export_thm CONJ_SYM;;

let CONJ_REFL = prove
 (`!t. t /\ t <=> t`,
  ITAUT_TAC);;

export_thm CONJ_REFL;;

let CONJ_ACI =
  let th1 = CONJ_SYM
  and th2 = CONJ_ASSOC'
  and th3 = prove
    (`!p q r. p /\ (q /\ r) <=> q /\ (p /\ r)`,
     REPEAT GEN_TAC THEN
     PURE_REWRITE_TAC [CONJ_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC CONJ_SYM)
  and th4 = CONJ_REFL
  and th5 = prove
    (`!p q. p /\ (p /\ q) <=> p /\ q`,
     REPEAT GEN_TAC THEN
     PURE_REWRITE_TAC [CONJ_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC CONJ_REFL) in
  prove
   (`!p q r.
       (p /\ q <=> q /\ p) /\
       ((p /\ q) /\ r <=> p /\ (q /\ r)) /\
       (p /\ (q /\ r) <=> q /\ (p /\ r)) /\
       (p /\ p <=> p) /\
       (p /\ (p /\ q) <=> p /\ q)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th1;
     MATCH_ACCEPT_TAC th2;
     MATCH_ACCEPT_TAC th3;
     MATCH_ACCEPT_TAC th4;
     MATCH_ACCEPT_TAC th5]);;

let DISJ_ASSOC' = prove
 (`!t1 t2 t3. (t1 \/ t2) \/ t3 <=> t1 \/ (t2 \/ t3)`,
  ITAUT_TAC);;

export_thm DISJ_ASSOC';;

let DISJ_ASSOC = GSYM DISJ_ASSOC';;

let DISJ_SYM = prove
 (`!t1 t2. t1 \/ t2 <=> t2 \/ t1`,
  ITAUT_TAC);;

export_thm DISJ_SYM;;

let DISJ_REFL = prove
 (`!t. t \/ t <=> t`,
  ITAUT_TAC);;

export_thm DISJ_REFL;;

let DISJ_ACI =
  let th1 = DISJ_SYM
  and th2 = DISJ_ASSOC'
  and th3 = prove
    (`!p q r. p \/ (q \/ r) <=> q \/ (p \/ r)`,
     REPEAT GEN_TAC THEN
     PURE_REWRITE_TAC [DISJ_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC DISJ_SYM)
  and th4 = DISJ_REFL
  and th5 = prove
    (`!p q. p \/ (p \/ q) <=> p \/ q`,
     REPEAT GEN_TAC THEN
     PURE_REWRITE_TAC [DISJ_ASSOC] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_ACCEPT_TAC DISJ_REFL) in
  prove
   (`!p q r.
       (p \/ q <=> q \/ p) /\
       ((p \/ q) \/ r <=> p \/ (q \/ r)) /\
       (p \/ (q \/ r) <=> q \/ (p \/ r)) /\
       (p \/ p <=> p) /\
       (p \/ (p \/ q) <=> p \/ q)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC th1;
     MATCH_ACCEPT_TAC th2;
     MATCH_ACCEPT_TAC th3;
     MATCH_ACCEPT_TAC th4;
     MATCH_ACCEPT_TAC th5]);;

let IMP_REFL = ITAUT `!t. t ==> t`;;

export_thm IMP_REFL;;

let IMP_IMP = prove
 (`!p q r. p ==> q ==> r <=> p /\ q ==> r`,
  ITAUT_TAC);;

export_thm IMP_IMP;;

let IMP_CONJ = GSYM IMP_IMP;;

let IMP_CONJ_ALT = prove
 (`!p q r. p /\ q ==> r <=> q ==> p ==> r`,
  ITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)

let LEFT_OR_DISTRIB = prove
 (`!p q r. p /\ (q \/ r) <=> p /\ q \/ p /\ r`,
  ITAUT_TAC);;

export_thm LEFT_OR_DISTRIB;;

let RIGHT_OR_DISTRIB = prove
 (`!p q r. (p \/ q) /\ r <=> p /\ r \/ q /\ r`,
  ITAUT_TAC);;

export_thm RIGHT_OR_DISTRIB;;

let LEFT_AND_DISTRIB = prove
 (`!p q r. p \/ (q /\ r) <=> (p \/ q) /\ (p \/ r)`,
  ITAUT_TAC);;

export_thm LEFT_AND_DISTRIB;;

let RIGHT_AND_DISTRIB = prove
 (`!p q r. (p /\ q) \/ r <=> (p \/ r) /\ (q \/ r)`,
  ITAUT_TAC);;

export_thm RIGHT_AND_DISTRIB;;

let IMP_AND_DISTRIB = prove
 (`!p q r. (p ==> q /\ r) <=> (p ==> q) /\ (p ==> r)`,
  ITAUT_TAC);;

export_thm IMP_AND_DISTRIB;;

let OR_IMP_DISTRIB = prove
 (`!p q r. (p \/ q ==> r) <=> (p ==> r) /\ (q ==> r)`,
  ITAUT_TAC);;

export_thm OR_IMP_DISTRIB;;

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)

let FORALL_SIMP = prove
 (`!t. (!x:A. t) = t`,
  ITAUT_TAC);;

export_thm FORALL_SIMP;;

let EXISTS_SIMP = prove
 (`!t. (?x:A. t) = t`,
  ITAUT_TAC);;

export_thm EXISTS_SIMP;;

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)

let EQ_IMP = ITAUT `!a b. (a <=> b) ==> a ==> b`;;

export_thm EQ_IMP;;

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

let TRUE_EQ_THM = ITAUT `!t. ((T <=> t) <=> t)`;;

export_thm TRUE_EQ_THM;;

let EQ_TRUE_THM = ITAUT `!t. ((t <=> T) <=> t)`;;

export_thm EQ_TRUE_THM;;

let FALSE_EQ_THM = ITAUT `!t. ((F <=> t) <=> ~t)`;;

export_thm FALSE_EQ_THM;;

let EQ_FALSE_THM = ITAUT `!t. ((t <=> F) <=> ~t)`;;

export_thm EQ_FALSE_THM;;

let EQ_CLAUSES = prove
  (`!t. ((T <=> t) <=> t) /\ ((t <=> T) <=> t) /\
        ((F <=> t) <=> ~t) /\ ((t <=> F) <=> ~t)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC TRUE_EQ_THM;
     MATCH_ACCEPT_TAC EQ_TRUE_THM;
     MATCH_ACCEPT_TAC FALSE_EQ_THM;
     MATCH_ACCEPT_TAC EQ_FALSE_THM]);;

let NOT_TRUE_THM = ITAUT `~T <=> F`;;

export_thm NOT_TRUE_THM;;

let NOT_FALSE_THM = ITAUT `~F <=> T`;;

export_thm NOT_FALSE_THM;;

let NOT_CLAUSES_WEAK = prove
  (`(~T <=> F) /\ (~F <=> T)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC NOT_TRUE_THM;
     MATCH_ACCEPT_TAC NOT_FALSE_THM]);;

let TRUE_AND_THM = ITAUT `!t. (T /\ t <=> t)`;;

export_thm TRUE_AND_THM;;

let AND_TRUE_THM = ITAUT `!t. (t /\ T <=> t)`;;

export_thm AND_TRUE_THM;;

let FALSE_AND_THM = ITAUT `!t. (F /\ t <=> F)`;;

export_thm FALSE_AND_THM;;

let AND_FALSE_THM = ITAUT `!t. (t /\ F <=> F)`;;

export_thm AND_FALSE_THM;;

let AND_CLAUSES = prove
  (`!t. (T /\ t <=> t) /\ (t /\ T <=> t) /\ (F /\ t <=> F) /\
        (t /\ F <=> F) /\ (t /\ t <=> t)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC TRUE_AND_THM;
     MATCH_ACCEPT_TAC AND_TRUE_THM;
     MATCH_ACCEPT_TAC FALSE_AND_THM;
     MATCH_ACCEPT_TAC AND_FALSE_THM;
     MATCH_ACCEPT_TAC CONJ_REFL]);;

let TRUE_OR_THM = ITAUT `!t. (T \/ t <=> T)`;;

export_thm TRUE_OR_THM;;

let OR_TRUE_THM = ITAUT `!t. (t \/ T <=> T)`;;

export_thm OR_TRUE_THM;;

let FALSE_OR_THM = ITAUT `!t. (F \/ t <=> t)`;;

export_thm FALSE_OR_THM;;

let OR_FALSE_THM = ITAUT `!t. (t \/ F <=> t)`;;

export_thm OR_FALSE_THM;;

let OR_CLAUSES = prove
  (`!t. (T \/ t <=> T) /\ (t \/ T <=> T) /\ (F \/ t <=> t) /\
        (t \/ F <=> t) /\ (t \/ t <=> t)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC TRUE_OR_THM;
     MATCH_ACCEPT_TAC OR_TRUE_THM;
     MATCH_ACCEPT_TAC FALSE_OR_THM;
     MATCH_ACCEPT_TAC OR_FALSE_THM;
     MATCH_ACCEPT_TAC DISJ_REFL]);;

let TRUE_IMP_THM = ITAUT `!t. (T ==> t <=> t)`;;

export_thm TRUE_IMP_THM;;

let IMP_TRUE_THM = ITAUT `!t. (t ==> T <=> T)`;;

export_thm IMP_TRUE_THM;;

let FALSE_IMP_THM = ITAUT `!t. (F ==> t <=> T)`;;

export_thm FALSE_IMP_THM;;

let IMP_FALSE_THM = ITAUT `!t. (t ==> F <=> ~t)`;;

export_thm IMP_FALSE_THM;;

let IMP_REFL_CLAUSE = prove
  (`!t. (t ==> t <=> T)`,
   GEN_TAC THEN
   PURE_REWRITE_TAC [IMP_REFL] THEN
   MATCH_ACCEPT_TAC EQ_REFL);;

let IMP_CLAUSES = prove
 (`!t. (T ==> t <=> t) /\ (t ==> T <=> T) /\ (F ==> t <=> T) /\
       (t ==> t <=> T) /\ (t ==> F <=> ~t)`,
    REPEAT GEN_TAC THEN
    REPEAT CONJ_TAC THENL
    [MATCH_ACCEPT_TAC TRUE_IMP_THM;
     MATCH_ACCEPT_TAC IMP_TRUE_THM;
     MATCH_ACCEPT_TAC FALSE_IMP_THM;
     MATCH_ACCEPT_TAC IMP_REFL_CLAUSE;
     MATCH_ACCEPT_TAC IMP_FALSE_THM]);;

extend_basic_rewrites
  [REFL_CLAUSE;
   EQ_CLAUSES;
   NOT_CLAUSES_WEAK;
   AND_CLAUSES;
   OR_CLAUSES;
   IMP_CLAUSES;
   FORALL_SIMP;
   EXISTS_SIMP;
   BETA_THM;
   let IMP_EQ_CLAUSE = prove
    (`(((x:A) = x) ==> p) <=> p`,
     REWRITE_TAC[EQT_INTRO(SPEC_ALL EQ_REFL); IMP_CLAUSES]) in
   IMP_EQ_CLAUSE];;

extend_basic_congs
  [ITAUT `(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')`];;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_THM = prove
 (`!p. (?!x:A. p x) <=> (?x. p x) /\ (!x x'. p x /\ p x' ==> (x = x'))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_DEF]);;

export_thm EXISTS_UNIQUE_THM;;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

let EXISTS_REFL = prove
 (`!a:A. ?x. x = a`,
  GEN_TAC THEN EXISTS_TAC `a:A` THEN REFL_TAC);;

export_thm EXISTS_REFL;;

let EXISTS_REFL' = ONCE_REWRITE_RULE [EQ_SYM_EQ] EXISTS_REFL;;

let EXISTS_UNIQUE_REFL = prove
 (`!a:A. ?!x. x = a`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  REPEAT(EQ_TAC ORELSE STRIP_TAC) THENL
   [EXISTS_TAC `a:A`; ASM_REWRITE_TAC[]] THEN
  REFL_TAC);;

export_thm EXISTS_UNIQUE_REFL;;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

let UNWIND_THM1 = prove
 (`!p (a:A). (?x. a = x /\ p x) <=> p a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN (CONJUNCTS_THEN2 SUBST1_TAC ACCEPT_TAC));
    DISCH_TAC THEN EXISTS_TAC `a:A` THEN
    CONJ_TAC THEN TRY(FIRST_ASSUM MATCH_ACCEPT_TAC) THEN
    REFL_TAC]);;

export_thm UNWIND_THM1;;

let UNWIND_THM2 = prove
 (`!p (a:A). (?x. x = a /\ p x) <=> p a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC UNWIND_THM1);;

export_thm UNWIND_THM2;;

let FORALL_UNWIND_THM2 = prove
 (`!p (a:A). (!x. x = a ==> p x) <=> p a`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    DISCH_TAC THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[]]);;

export_thm FORALL_UNWIND_THM2;;

let FORALL_UNWIND_THM1 = prove
 (`!p (a:A). (!x. a = x ==> p x) <=> p a`,
  REPEAT GEN_TAC THEN CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV SYM_CONV)) THEN
  MATCH_ACCEPT_TAC FORALL_UNWIND_THM2);;

export_thm FORALL_UNWIND_THM1;;

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

let SWAP_FORALL_THM = prove
 (`!p:A->B->bool. (!x y. p x y) <=> (!y x. p x y)`,
  ITAUT_TAC);;

export_thm SWAP_FORALL_THM;;

let SWAP_EXISTS_THM = prove
 (`!p:A->B->bool. (?x y. p x y) <=> (?y x. p x y)`,
  ITAUT_TAC);;

export_thm SWAP_EXISTS_THM;;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

let FORALL_AND_THM = prove
 (`!p q. (!x:A. p x /\ q x) <=> (!x. p x) /\ (!x. q x)`,
  ITAUT_TAC);;

export_thm FORALL_AND_THM;;

let AND_FORALL_THM = prove
 (`!p q. (!x. p x) /\ (!x. q x) <=> (!x:A. p x /\ q x)`,
  ITAUT_TAC);;

export_thm AND_FORALL_THM;;

let LEFT_AND_FORALL_THM = prove
 (`!p q. (!x:A. p x) /\ q <=> (!x:A. p x /\ q)`,
  ITAUT_TAC);;

export_thm LEFT_AND_FORALL_THM;;

let RIGHT_AND_FORALL_THM = prove
 (`!p q. p /\ (!x:A. q x) <=> (!x. p /\ q x)`,
  ITAUT_TAC);;

export_thm RIGHT_AND_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let EXISTS_OR_THM = prove
 (`!p q. (?x:A. p x \/ q x) <=> (?x. p x) \/ (?x. q x)`,
  ITAUT_TAC);;

export_thm EXISTS_OR_THM;;

let OR_EXISTS_THM = prove
 (`!p q. (?x. p x) \/ (?x. q x) <=> (?x:A. p x \/ q x)`,
  ITAUT_TAC);;

export_thm OR_EXISTS_THM;;

let LEFT_OR_EXISTS_THM = prove
 (`!p q. (?x. p x) \/ q <=> (?x:A. p x \/ q)`,
  ITAUT_TAC);;

export_thm LEFT_OR_EXISTS_THM;;

let RIGHT_OR_EXISTS_THM = prove
 (`!p q. p \/ (?x. q x) <=> (?x:A. p \/ q x)`,
  ITAUT_TAC);;

export_thm RIGHT_OR_EXISTS_THM;;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let LEFT_EXISTS_AND_THM = prove
 (`!p q. (?x:A. p x /\ q) <=> (?x:A. p x) /\ q`,
  ITAUT_TAC);;

export_thm LEFT_EXISTS_AND_THM;;

let RIGHT_EXISTS_AND_THM = prove
 (`!p q. (?x:A. p /\ q x) <=> p /\ (?x:A. q x)`,
  ITAUT_TAC);;

export_thm RIGHT_EXISTS_AND_THM;;

let TRIV_EXISTS_AND_THM = prove
 (`!p q. (?x:A. p /\ q) <=> (?x:A. p) /\ (?x:A. q)`,
  ITAUT_TAC);;

export_thm TRIV_EXISTS_AND_THM;;

let LEFT_AND_EXISTS_THM = prove
 (`!p q. (?x:A. p x) /\ q <=> (?x:A. p x /\ q)`,
  ITAUT_TAC);;

export_thm LEFT_AND_EXISTS_THM;;

let RIGHT_AND_EXISTS_THM = prove
 (`!p q. p /\ (?x:A. q x) <=> (?x:A. p /\ q x)`,
  ITAUT_TAC);;

export_thm RIGHT_AND_EXISTS_THM;;

let TRIV_AND_EXISTS_THM = prove
 (`!p q. (?x:A. p) /\ (?x:A. q) <=> (?x:A. p /\ q)`,
  ITAUT_TAC);;

export_thm TRIV_AND_EXISTS_THM;;

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

let TRIV_FORALL_OR_THM = prove
 (`!p q. (!x:A. p \/ q) <=> (!x:A. p) \/ (!x:A. q)`,
  ITAUT_TAC);;

export_thm TRIV_FORALL_OR_THM;;

let TRIV_OR_FORALL_THM = prove
 (`!p q. (!x:A. p) \/ (!x:A. q) <=> (!x:A. p \/ q)`,
  ITAUT_TAC);;

export_thm TRIV_OR_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let RIGHT_IMP_FORALL_THM = prove
 (`!p q. (p ==> !x:A. q x) <=> (!x. p ==> q x)`,
  ITAUT_TAC);;

export_thm RIGHT_IMP_FORALL_THM;;

let RIGHT_FORALL_IMP_THM = prove
 (`!p q. (!x. p ==> q x) <=> (p ==> !x:A. q x)`,
  ITAUT_TAC);;

export_thm RIGHT_FORALL_IMP_THM;;

let LEFT_IMP_EXISTS_THM = prove
 (`!p q. ((?x:A. p x) ==> q) <=> (!x. p x ==> q)`,
  ITAUT_TAC);;

export_thm LEFT_IMP_EXISTS_THM;;

let LEFT_FORALL_IMP_THM = prove
 (`!p q. (!x. p x ==> q) <=> ((?x:A. p x) ==> q)`,
  ITAUT_TAC);;

export_thm LEFT_FORALL_IMP_THM;;

let TRIV_FORALL_IMP_THM = prove
 (`!p q. (!x:A. p ==> q) <=> ((?x:A. p) ==> (!x:A. q))`,
  ITAUT_TAC);;

export_thm TRIV_FORALL_IMP_THM;;

let TRIV_EXISTS_IMP_THM = prove
 (`!p q. (?x:A. p ==> q) <=> ((!x:A. p) ==> (?x:A. q))`,
  ITAUT_TAC);;

export_thm TRIV_EXISTS_IMP_THM;;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for logical operations w.r.t. implication.          *)
(* ------------------------------------------------------------------------- *)

let MONO_AND =
    ITAUT
      `!p1 p2 q1 q2.
         (p1 ==> p2) /\ (q1 ==> q2) ==> (p1 /\ q1 ==> p2 /\ q2)`;;

export_thm MONO_AND;;

let MONO_OR =
    ITAUT
      `!p1 p2 q1 q2.
         (p1 ==> p2) /\ (q1 ==> q2) ==> (p1 \/ q1 ==> p2 \/ q2)`;;

export_thm MONO_OR;;

let MONO_IMP =
    ITAUT
      `!p1 p2 q1 q2.
         (p2 ==> p1) /\ (q1 ==> q2) ==> ((p1 ==> q1) ==> (p2 ==> q2))`;;

export_thm MONO_IMP;;

let MONO_NOT = ITAUT `!p q. (q ==> p) ==> (~p ==> ~q)`;;

export_thm MONO_NOT;;

let MONO_FORALL = prove
 (`!p q. (!x:A. p x ==> q x) ==> ((!x. p x) ==> (!x. q x))`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

export_thm MONO_FORALL;;

let MONO_EXISTS = prove
 (`!p q. (!x:A. p x ==> q x) ==> ((?x. p x) ==> (?x. q x))`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
  EXISTS_TAC `x:A` THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

export_thm MONO_EXISTS;;

(* ------------------------------------------------------------------------- *)
(* A generic "without loss of generality" lemma for symmetry.                *)
(* ------------------------------------------------------------------------- *)

let WLOG_RELATION = prove
 (`!r p. (!x y : A. p x y ==> p y x) /\
         (!x y. r x y \/ r y x) /\
         (!x y. r x y ==> p x y)
         ==> !x y. p x y`,
  REPEAT GEN_TAC THEN DISCH_THEN
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_SIMP_TAC[]);;

export_thm WLOG_RELATION;;

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)

let EXISTS_UNIQUE_ALT = prove
 (`!p:A->bool. (?!x. p x) <=> (?x. !y. p y <=> (x = y))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:A`) ASSUME_TAC) THEN
    EXISTS_TAC `x:A` THEN GEN_TAC THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM MATCH_ACCEPT_TAC];
    DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN
    ASM_REWRITE_TAC[GSYM EXISTS_REFL] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (SUBST1_TAC o SYM)) THEN REFL_TAC]);;

export_thm EXISTS_UNIQUE_ALT;;

let EXISTS_UNIQUE = prove
 (`!p:A->bool. (?!x. p x) <=> (?x. p x /\ !y. p y ==> (y = x))`,
  GEN_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o BINDER_CONV)
   [ITAUT `(a <=> b) <=> (a ==> b) /\ (b ==> a)`] THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN
  REWRITE_TAC[FORALL_AND_THM] THEN SIMP_TAC[] THEN
  REWRITE_TAC[LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  REWRITE_TAC[CONJ_ACI]);;

export_thm EXISTS_UNIQUE;;

(* ------------------------------------------------------------------------- *)
(* DESTRUCT_TAC, FIX_TAC, INTRO_TAC and HYP_TAC, giving more brief and       *)
(* elegant ways of naming introduced variables and assumptions (from Marco   *)
(* Maggesi).                                                                 *)
(* ------------------------------------------------------------------------- *)

let DESTRUCT_TAC,FIX_TAC,INTRO_TAC,HYP_TAC =
  (* ---------------------------------------------------------------------- *)
  (* Like GEN_TAC but fails instead of generating a primed variant when the *)
  (* variable occurs free in the context.                                   *)
  (* ---------------------------------------------------------------------- *)
  let (PURE_GEN_TAC: tactic) =
    fun (asl,w) ->
      try let x = fst(dest_forall w) in
          let avoids = itlist (union o thm_frees o snd) asl (frees w) in
          if mem x avoids then fail() else X_GEN_TAC x (asl,w)
      with Failure _ -> failwith "PURE_GEN_TAC"
  (* ---------------------------------------------------------------------- *)
  (* Like X_GEN_TAC but needs only the name of the variable, not the type.  *)
  (* ---------------------------------------------------------------------- *)
  and (NAME_GEN_TAC: string -> tactic) =
    fun s gl ->
      let ty = (snd o dest_var o fst o dest_forall o snd) gl  in
      X_GEN_TAC (mk_var(s,ty)) gl
  and OBTAIN_THEN v ttac th =
    let ty = (snd o dest_var o fst o dest_exists o concl) th in
    X_CHOOSE_THEN (mk_var(v,ty)) ttac th
  and CONJ_LIST_TAC = end_itlist (fun t1 t2 -> CONJ_TAC THENL [t1; t2])
  and NUM_DISJ_TAC n =
    if n <= 0 then failwith "NUM_DISJ_TAC" else
    REPLICATE_TAC (n-1) DISJ2_TAC THEN REPEAT DISJ1_TAC
  and NAME_PULL_FORALL_CONV =
    let SWAP_FORALL_CONV = REWR_CONV SWAP_FORALL_THM
    and AND_FORALL_CONV = GEN_REWRITE_CONV I [AND_FORALL_THM]
    and RIGHT_IMP_FORALL_CONV = GEN_REWRITE_CONV I [RIGHT_IMP_FORALL_THM] in
    fun s ->
      let rec PULL_FORALL tm =
          if is_forall tm then
            if name_of(fst(dest_forall tm)) = s then REFL tm else
              (BINDER_CONV PULL_FORALL THENC SWAP_FORALL_CONV) tm
          else if is_imp tm then
            (RAND_CONV PULL_FORALL THENC RIGHT_IMP_FORALL_CONV) tm
          else if is_conj tm then
            (BINOP_CONV PULL_FORALL THENC AND_FORALL_CONV) tm
          else
            fail () in
      PULL_FORALL in
  let pa_ident p = function
      Ident s::rest when p s -> s,rest
    | _ -> raise Noparse in
  let pa_label = pa_ident isalnum
  and pa_var = pa_ident isalpha in
  let fix_tac =
    let fix_var v = CONV_TAC (NAME_PULL_FORALL_CONV v) THEN PURE_GEN_TAC
    and fix_rename =
      function u,[v] -> CONV_TAC (NAME_PULL_FORALL_CONV v) THEN NAME_GEN_TAC u
             | u,_   -> NAME_GEN_TAC u in
    let vars =
      let pa_rename =
        let oname = possibly (a(Ident "/") ++ pa_var >> snd) in
        (a(Resword "[") ++ pa_var >> snd) ++ oname ++ a(Resword "]") >> fst in
      many (pa_rename >> fix_rename || pa_var >> fix_var) >> EVERY
    and star = possibly (a (Ident "*") >> K ()) in
    vars ++ star >> function tac,[] -> tac | tac,_ -> tac THEN REPEAT GEN_TAC
  and destruct_tac =
    let OBTAINL_THEN : string list -> thm_tactical =
      EVERY_TCL o map OBTAIN_THEN in
    let rec destruct inp = disj inp
    and disj inp =
      let DISJ_CASES_LIST = end_itlist DISJ_CASES_THEN2 in
      (listof conj (a(Resword "|")) "Disjunction" >> DISJ_CASES_LIST) inp
    and conj inp = (atleast 1 atom >> end_itlist CONJUNCTS_THEN2) inp
    and obtain inp =
      let obtain_prfx =
        let var_list = atleast 1 pa_var in
        (a(Ident "@") ++ var_list >> snd) ++ a(Resword ".") >> fst in
      (obtain_prfx ++ destruct >> uncurry OBTAINL_THEN) inp
    and atom inp =
      let label =
        function Ident "_"::res -> K ALL_TAC,res
               | Ident "+"::res -> MP_TAC,res
               | Ident s::res when isalnum s -> LABEL_TAC s,res
               | _ -> raise Noparse
      and paren =
        (a(Resword "(") ++ destruct >> snd) ++ a(Resword ")") >> fst in
      (obtain || label || paren) inp in
    destruct in
  let intro_tac =
    let number = function
        Ident s::rest ->
          (try check ((<=) 1) (int_of_string s), rest
           with Failure _ -> raise Noparse)
      | _ -> raise Noparse
    and pa_fix = a(Ident "!") ++ fix_tac >> snd
    and pa_dest = destruct_tac >> DISCH_THEN in
    let pa_prefix =
      elistof (pa_fix || pa_dest) (a(Resword ";")) "Prefix intro pattern" in
    let rec pa_intro toks =
      (pa_prefix ++ possibly pa_postfix >> uncurry (@) >> EVERY) toks
    and pa_postfix toks = (pa_conj || pa_disj) toks
    and pa_conj toks =
      let conjs =
        listof pa_intro (a(Ident "&")) "Intro pattern" >> CONJ_LIST_TAC in
      ((a(Resword "{") ++ conjs >> snd) ++ a(Resword "}") >> fst) toks
    and pa_disj toks =
      let disj = number >> NUM_DISJ_TAC in
      ((a(Ident "#") ++ disj >> snd) ++ pa_intro >> uncurry (THEN)) toks in
    pa_intro in
  let hyp_tac rule =
    let pa_action = function
        Resword ":" :: rest -> REMOVE_THEN,rest
      | Resword "->" :: rest -> USE_THEN,rest
      | _ -> raise Noparse in
    pa_label ++ possibly (pa_action ++ destruct_tac) >>
    (function
       | lbl,[action,tac] -> action lbl (tac o rule)
       | lbl,_ -> REMOVE_THEN lbl (LABEL_TAC lbl o rule)) in
  let DESTRUCT_TAC s =
    let tac,rest =
      (fix "Destruct pattern" destruct_tac o lex o explode) s in
    if rest=[] then tac else failwith "Garbage after destruct pattern"
  and INTRO_TAC s =
    let tac,rest =
      (fix "Introduction pattern" intro_tac o lex o explode) s in
    if rest=[] then tac else failwith "Garbage after intro pattern"
  and FIX_TAC s =
    let tac,rest = (fix_tac o lex o explode) s in
    if rest=[] then tac else failwith "FIX_TAC: invalid pattern"
  and HYP_TAC s rule =
    let tac,rest = (hyp_tac rule o lex o explode) s in
    if rest=[] then tac else failwith "HYP_TAC: invalid pattern" in
  DESTRUCT_TAC,FIX_TAC,INTRO_TAC,HYP_TAC;;

let CLAIM_TAC s tm = SUBGOAL_THEN tm (DESTRUCT_TAC s);;

logfile_end ();;

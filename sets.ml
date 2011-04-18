(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "int.ml";;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

logfile "set-def";;

let set_exists = prove
  (`?p : A -> bool. (\x. T) p`,
   EXISTS_TAC `p : A -> bool` THEN
   REWRITE_TAC []);;

let set_tybij =
    REWRITE_RULE []
      (new_type_definition
        "set" ("GSPEC","dest_set") set_exists);;

let IN_DEF = new_definition
  `!P x. (x : A) IN P <=> dest_set P x`;;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

let EXTENSION_IMP = prove
 (`!s t. (!x:A. x IN s <=> x IN t) ==> s = t`,
  REWRITE_TAC[IN_DEF; GSYM FUN_EQ_THM] THEN
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM (CONJUNCT1 set_tybij)] THEN
  ASM_REWRITE_TAC []);;

export_thm EXTENSION_IMP;;

let EXTENSION = prove
 (`!s t. (s = t) <=> !x:A. x IN s <=> x IN t`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN (fun th -> REWRITE_TAC [th]);
   MATCH_ACCEPT_TAC EXTENSION_IMP]);;

export_thm EXTENSION;;

(* ------------------------------------------------------------------------- *)
(* General set-comprehension specification.                                  *)
(* ------------------------------------------------------------------------- *)

let SETSPEC = new_definition
  `!v P t. SETSPEC (v:A) P t <=> P /\ (v = t)`;;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_THM = prove
 (`!P (x:A). x IN GSPEC (\v. P (SETSPEC v)) <=> P (\p t. p /\ (x = t))`,
  REWRITE_TAC[IN_DEF; set_tybij] THEN
  REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [FUN_EQ_THM; SETSPEC]);;

export_thm IN_ELIM_THM;;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

let EMPTY = new_definition
  `EMPTY = { x:A | F }`;;

export_thm EMPTY;;

let INSERT = new_definition
  `!x s. x INSERT s = { y:A | y = x \/ y IN s }`;;

export_thm INSERT;;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

let UNIV = new_definition
  `UNIV = { x:A | T }`;;

export_thm UNIV;;

let UNION = new_definition
  `!s t. s UNION t = {x:A | x IN s \/ x IN t}`;;

export_thm UNION;;

let UNIONS = new_definition
  `!s. UNIONS s = {x:A | ?u. u IN s /\ x IN u}`;;

export_thm UNIONS;;

let INTER = new_definition
  `!s t. s INTER t = {x:A | x IN s /\ x IN t}`;;

export_thm INTER;;

let INTERS = new_definition
  `!s. INTERS s = {x:A | !u. u IN s ==> x IN u}`;;

export_thm INTERS;;

let DIFF = new_definition
  `!s t. s DIFF t =  {x:A | x IN s /\ ~(x IN t)}`;;

export_thm DIFF;;

let DELETE = new_definition
  `!s x. s DELETE x = {y:A | y IN s /\ ~(y = x)}`;;

export_thm DELETE;;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

let SUBSET = new_definition
  `!s t. s SUBSET t <=> !x:A. x IN s ==> x IN t`;;

export_thm SUBSET;;

let PSUBSET = new_definition
  `!s t. (s : A set) PSUBSET t <=> s SUBSET t /\ ~(s = t)`;;

export_thm PSUBSET;;

let DISJOINT = new_definition
  `!s t. DISJOINT (s : A set) t <=> (s INTER t = EMPTY)`;;

export_thm DISJOINT;;

let SING = new_definition
  `!s. SING s = ?x:A. s = {x}`;;

export_thm SING;;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

let IMAGE = new_definition
  `!f s. IMAGE (f:A->B) s = { y | ?x. x IN s /\ (y = f x)}`;;

export_thm IMAGE;;

let INJ = new_definition
  `!f s t.
     INJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y))`;;

export_thm INJ;;

let SURJ = new_definition
  `!f s t.
     SURJ (f:A->B) s t <=>
     (!x. x IN s ==> (f x) IN t) /\
     (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))`;;

export_thm SURJ;;

let BIJ = new_definition
  `!f s t. BIJ (f:A->B) s t <=> INJ f s t /\ SURJ f s t`;;

export_thm BIJ;;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = new_definition
  `!s. CHOICE s = @x:A. x IN s`;;

let CHOICE = prove
 (`!s : A set. ~(s = EMPTY) ==> (CHOICE s) IN s`,
  REWRITE_TAC
    [CHOICE_DEF; EXTENSION; EMPTY; IN_ELIM_THM; NOT_FORALL_THM; EXISTS_THM]);;

export_thm CHOICE;;

let REST = new_definition
  `!s. REST (s : A set) = s DELETE (CHOICE s)`;;

export_thm REST;;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let IN_ELIM = prove
 (`!p (x:A). x IN GSPEC (\v. ?y. SETSPEC v (p y) y) <=> p x`,
  REWRITE_TAC[IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC []]);;

export_thm IN_ELIM;;

let NOT_IN_EMPTY = prove
 (`!x:A. ~(x IN EMPTY)`,
  REWRITE_TAC[IN_ELIM; EMPTY]);;

export_thm NOT_IN_EMPTY;;

let IN_UNIV = prove
 (`!x:A. x IN UNIV`,
  REWRITE_TAC[IN_ELIM; UNIV]);;

export_thm IN_UNIV;;

let IN_UNION = prove
 (`!s t (x:A). x IN (s UNION t) <=> x IN s \/ x IN t`,
  REWRITE_TAC[IN_ELIM; UNION]);;

export_thm IN_UNION;;

let IN_UNIONS = prove
 (`!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM; UNIONS]);;

export_thm IN_UNIONS;;

let IN_INTER = prove
 (`!s t (x:A). x IN (s INTER t) <=> x IN s /\ x IN t`,
  REWRITE_TAC[IN_ELIM; INTER]);;

export_thm IN_INTER;;

let IN_INTERS = prove
 (`!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t`,
  REWRITE_TAC[IN_ELIM; INTERS]);;

export_thm IN_INTERS;;

let IN_DIFF = prove
 (`!s t (x:A). x IN (s DIFF t) <=> x IN s /\ ~(x IN t)`,
  REWRITE_TAC[IN_ELIM; DIFF]);;

export_thm IN_DIFF;;

let IN_INSERT = prove
 (`!x:A. !y s. x IN (y INSERT s) <=> (x = y) \/ x IN s`,
  REWRITE_TAC[IN_ELIM; INSERT]);;

export_thm IN_INSERT;;

let IN_DELETE = prove
 (`!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\ ~(x = y)`,
  REWRITE_TAC[IN_ELIM; DELETE]);;

export_thm IN_DELETE;;

let IN_SING = prove
 (`!x y. x IN {y:A} <=> (x = y)`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

export_thm IN_SING;;

let IN_IMAGE = prove
 (`!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\ x IN s`,
  ONCE_REWRITE_TAC[CONJ_SYM] THEN REWRITE_TAC[IN_ELIM; IMAGE]);;

export_thm IN_IMAGE;;

let IN_REST = prove
 (`!x:A. !s. x IN (REST s) <=> x IN s /\ ~(x = CHOICE s)`,
  REWRITE_TAC[REST; IN_DELETE]);;

export_thm IN_REST;;

let FORALL_IN_INSERT = prove
 (`!P a s. (!x. (x:A) IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x)`,
  REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `a:A`) THEN
    REWRITE_TAC [];
    FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm FORALL_IN_INSERT;;

let EXISTS_IN_INSERT = prove
 (`!P a s. (?x. (x:A) IN (a INSERT s) /\ P x) <=> P a \/ ?x. x IN s /\ P x`,
  REWRITE_TAC[IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [DISJ1_TAC THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISJ2_TAC THEN
    EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `a:A` THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC []]]);;

export_thm EXISTS_IN_INSERT;;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let SET_TAC =
  let PRESET_TAC =
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT COND_CASES_TAC THEN
    REWRITE_TAC[EXTENSION; SUBSET; PSUBSET; DISJOINT; SING] THEN
    REWRITE_TAC[NOT_IN_EMPTY; IN_UNIV; IN_UNION; IN_INTER; IN_DIFF; IN_INSERT;
                IN_DELETE; IN_REST; IN_INTERS; IN_UNIONS; IN_IMAGE;
                IN_ELIM_THM] in
  fun ths ->
    (if ths = [] then ALL_TAC else MP_TAC(end_itlist CONJ ths)) THEN
    PRESET_TAC THEN
    MESON_TAC[];;

let SET_RULE tm = prove(tm,SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

let NOT_EQUAL_SETS = prove
 (`!s : A set. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC (TAUT `!x y. (x <=> ~y) ==> (~x <=> y)`) THEN
  REWRITE_TAC [NOT_EXISTS_THM; TAUT `!x y. ~(x <=> ~y) <=> (y <=> x)`] THEN
  MATCH_ACCEPT_TAC EXTENSION);;

export_thm NOT_EQUAL_SETS;;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let MEMBER_NOT_EMPTY = prove
 (`!s : A set. (?x. x IN s) <=> ~(s = EMPTY)`,
  REWRITE_TAC [NOT_EQUAL_SETS; NOT_IN_EMPTY]);;

export_thm MEMBER_NOT_EMPTY;;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let UNIV_NOT_EMPTY = prove
 (`~(UNIV : A set = EMPTY)`,
  REWRITE_TAC [GSYM MEMBER_NOT_EMPTY; IN_UNIV]);;

export_thm UNIV_NOT_EMPTY;;

let EMPTY_NOT_UNIV = prove
 (`~(EMPTY : A set = UNIV)`,
  ACCEPT_TAC (GSYM UNIV_NOT_EMPTY));;

export_thm EMPTY_NOT_UNIV;;

let EQ_UNIV = prove
 (`!s. (!x:A. x IN s) <=> (s = UNIV)`,
  REWRITE_TAC [EXTENSION; IN_UNIV]);;

export_thm EQ_UNIV;;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

let SUBSET_TRANS = prove
 (`!(s : A set) t u. s SUBSET t /\ t SUBSET u ==> s SUBSET u`,
  REWRITE_TAC [SUBSET] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM ACCEPT_TAC);;

export_thm SUBSET_TRANS;;

let SUBSET_REFL = prove
 (`!s : A set. s SUBSET s`,
  REWRITE_TAC [SUBSET]);;

export_thm SUBSET_REFL;;

let SUBSET_ANTISYM = prove
 (`!(s : A set) t. s SUBSET t /\ t SUBSET s ==> s = t`,
  REWRITE_TAC [EXTENSION; SUBSET] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [FIRST_ASSUM MATCH_ACCEPT_TAC;
   FIRST_ASSUM MATCH_ACCEPT_TAC]);;

export_thm SUBSET_ANTISYM;;

let SUBSET_ANTISYM_EQ = prove
 (`!(s : A set) t. s SUBSET t /\ t SUBSET s <=> s = t`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC SUBSET_ANTISYM;
   DISCH_THEN (fun th -> REWRITE_TAC [th; SUBSET_REFL])]);;

export_thm SUBSET_ANTISYM_EQ;;

let EMPTY_SUBSET = prove
 (`!s : A set. EMPTY SUBSET s`,
  REWRITE_TAC [SUBSET; NOT_IN_EMPTY]);;

export_thm EMPTY_SUBSET;;

let SUBSET_EMPTY = prove
 (`!s : A set. s SUBSET EMPTY <=> (s = EMPTY)`,
  REWRITE_TAC [SUBSET; NOT_IN_EMPTY; EXTENSION]);;

export_thm SUBSET_EMPTY;;

let SUBSET_UNIV = prove
 (`!s : A set. s SUBSET UNIV`,
  REWRITE_TAC [SUBSET; IN_UNIV]);;

export_thm SUBSET_UNIV;;

let UNIV_SUBSET = prove
 (`!s : A set. UNIV SUBSET s <=> (s = UNIV)`,
  REWRITE_TAC [SUBSET; IN_UNIV; EXTENSION]);;

export_thm UNIV_SUBSET;;

let SING_SUBSET = prove
 (`!s x. {x} SUBSET s <=> (x:A) IN s`,
  REWRITE_TAC [SUBSET; IN_SING] THEN
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN MATCH_MP_TAC THEN
   REFL_TAC;
   STRIP_TAC THEN
   GEN_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SING_SUBSET;;

let SUBSET_RESTRICT = prove
 (`!s P. {x | (x:A) IN s /\ P x} SUBSET s`,
  REWRITE_TAC [SUBSET; IN_ELIM] THEN
  REPEAT STRIP_TAC);;

export_thm SUBSET_RESTRICT;;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

let PSUBSET_TRANS = prove
 (`!(s : A set) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_thm PSUBSET_TRANS;;

let PSUBSET_SUBSET_TRANS = prove
 (`!(s:A->bool) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_thm PSUBSET_SUBSET_TRANS;;

let SUBSET_PSUBSET_TRANS = prove
 (`!(s:A->bool) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  SET_TAC[]);;

export_thm SUBSET_PSUBSET_TRANS;;

let PSUBSET_IRREFL = prove
 (`!s:A->bool. ~(s PSUBSET s)`,
  SET_TAC[]);;

export_thm PSUBSET_IRREFL;;

let NOT_PSUBSET_EMPTY = prove
 (`!s:A->bool. ~(s PSUBSET EMPTY)`,
  SET_TAC[]);;

export_thm NOT_PSUBSET_EMPTY;;

let NOT_UNIV_PSUBSET = prove
 (`!s:A->bool. ~(UNIV PSUBSET s)`,
  SET_TAC[]);;

export_thm NOT_UNIV_PSUBSET;;

let PSUBSET_UNIV = prove
 (`!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)`,
  SET_TAC[]);;

export_thm PSUBSET_UNIV;;

let PSUBSET_ALT = prove
 (`!s t:A->bool. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`,
  REWRITE_TAC[PSUBSET] THEN SET_TAC[]);;

export_thm PSUBSET_ALT;;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let UNION_ASSOC = prove
 (`!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)`,
  SET_TAC[]);;

export_thm UNION_ASSOC;;

let UNION_IDEMPOT = prove
 (`!s:A->bool. s UNION s = s`,
  SET_TAC[]);;

export_thm UNION_IDEMPOT;;

let UNION_COMM = prove
 (`!(s:A->bool) t. s UNION t = t UNION s`,
  SET_TAC[]);;

export_thm UNION_COMM;;

let SUBSET_UNION = prove
 (`(!s:A->bool. !t. s SUBSET (s UNION t)) /\
   (!s:A->bool. !t. s SUBSET (t UNION s))`,
  SET_TAC[]);;

export_thm SUBSET_UNION;;

let SUBSET_UNION_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)`,
  SET_TAC[]);;

export_thm SUBSET_UNION_ABSORPTION;;

let UNION_EMPTY = prove
 (`(!s:A->bool. EMPTY UNION s = s) /\
   (!s:A->bool. s UNION EMPTY = s)`,
  SET_TAC[]);;

export_thm UNION_EMPTY;;

let UNION_UNIV = prove
 (`(!s:A->bool. UNIV UNION s = UNIV) /\
   (!s:A->bool. s UNION UNIV = UNIV)`,
  SET_TAC[]);;

export_thm UNION_UNIV;;

let EMPTY_UNION = prove
 (`!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`,
  SET_TAC[]);;

export_thm EMPTY_UNION;;

let UNION_SUBSET = prove
 (`!s t u. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
  SET_TAC[]);;

export_thm UNION_SUBSET;;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let INTER_ASSOC = prove
 (`!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)`,
  SET_TAC[]);;

export_thm INTER_ASSOC;;

let INTER_IDEMPOT = prove
 (`!s:A->bool. s INTER s = s`,
  SET_TAC[]);;

export_thm INTER_IDEMPOT;;

let INTER_COMM = prove
 (`!(s:A->bool) t. s INTER t = t INTER s`,
  SET_TAC[]);;

export_thm INTER_COMM;;

let INTER_SUBSET = prove
 (`(!s:A->bool. !t. (s INTER t) SUBSET s) /\
   (!s:A->bool. !t. (t INTER s) SUBSET s)`,
  SET_TAC[]);;

export_thm INTER_SUBSET;;

let SUBSET_INTER_ABSORPTION = prove
 (`!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)`,
  SET_TAC[]);;

export_thm SUBSET_INTER_ABSORPTION;;

let INTER_EMPTY = prove
 (`(!s:A->bool. EMPTY INTER s = EMPTY) /\
   (!s:A->bool. s INTER EMPTY = EMPTY)`,
  SET_TAC[]);;

export_thm INTER_EMPTY;;

let INTER_UNIV = prove
 (`(!s:A->bool. UNIV INTER s = s) /\
   (!s:A->bool. s INTER UNIV = s)`,
  SET_TAC[]);;

export_thm INTER_UNIV;;

let SUBSET_INTER = prove
 (`!s t u. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,
  SET_TAC[]);;

export_thm SUBSET_INTER;;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNION_OVER_INTER = prove
 (`!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  SET_TAC[]);;

export_thm UNION_OVER_INTER;;

let INTER_OVER_UNION = prove
 (`!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  SET_TAC[]);;

export_thm INTER_OVER_UNION;;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let IN_DISJOINT = prove
 (`!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`,
  SET_TAC[]);;

export_thm IN_DISJOINT;;

let DISJOINT_SYM = prove
 (`!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s`,
  SET_TAC[]);;

export_thm DISJOINT_SYM;;

let DISJOINT_EMPTY = prove
 (`!s:A->bool. DISJOINT EMPTY s /\ DISJOINT s EMPTY`,
  SET_TAC[]);;

export_thm DISJOINT_EMPTY;;

let DISJOINT_EMPTY_REFL = prove
 (`!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)`,
  SET_TAC[]);;

export_thm DISJOINT_EMPTY_REFL;;

let DISJOINT_UNION = prove
 (`!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`,
  SET_TAC[]);;

export_thm DISJOINT_UNION;;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_EMPTY = prove
 (`!s:A->bool. s DIFF EMPTY = s`,
  SET_TAC[]);;

export_thm DIFF_EMPTY;;

let EMPTY_DIFF = prove
 (`!s:A->bool. EMPTY DIFF s = EMPTY`,
  SET_TAC[]);;

export_thm EMPTY_DIFF;;

let DIFF_UNIV = prove
 (`!s:A->bool. s DIFF UNIV = EMPTY`,
  SET_TAC[]);;

export_thm DIFF_UNIV;;

let DIFF_DIFF = prove
 (`!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t`,
  SET_TAC[]);;

export_thm DIFF_DIFF;;

let DIFF_EQ_EMPTY = prove
 (`!s:A->bool. s DIFF s = EMPTY`,
  SET_TAC[]);;

export_thm DIFF_EQ_EMPTY;;

let SUBSET_DIFF = prove
 (`!s t. (s DIFF t) SUBSET s`,
  SET_TAC[]);;

export_thm SUBSET_DIFF;;

(* ------------------------------------------------------------------------- *)
(* Insertsion and deletion.                                                  *)
(* ------------------------------------------------------------------------- *)

let COMPONENT = prove
 (`!x:A. !s. x IN (x INSERT s)`,
  SET_TAC[]);;

export_thm COMPONENT;;

let DECOMPOSITION = prove
 (`!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN EXISTS_TAC `s DELETE x:A` THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_thm DECOMPOSITION;;

let SET_CASES = prove
 (`!s:A->bool. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`,
  MESON_TAC[MEMBER_NOT_EMPTY; DECOMPOSITION]);;

export_thm SET_CASES;;

let ABSORPTION = prove
 (`!x:A. !s. x IN s <=> (x INSERT s = s)`,
  SET_TAC[]);;

export_thm ABSORPTION;;

let INSERT_INSERT = prove
 (`!x:A. !s. x INSERT (x INSERT s) = x INSERT s`,
  SET_TAC[]);;

export_thm INSERT_INSERT;;

let INSERT_COMM = prove
 (`!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
  SET_TAC[]);;

export_thm INSERT_COMM;;

let INSERT_UNIV = prove
 (`!x:A. x INSERT UNIV = UNIV`,
  SET_TAC[]);;

export_thm INSERT_UNIV;;

let NOT_INSERT_EMPTY = prove
 (`!x:A. !s. ~(x INSERT s = EMPTY)`,
  SET_TAC[]);;

export_thm NOT_INSERT_EMPTY;;

let NOT_EMPTY_INSERT = prove
 (`!x:A. !s. ~(EMPTY = x INSERT s)`,
  SET_TAC[]);;

export_thm NOT_EMPTY_INSERT;;

let INSERT_UNION = prove
 (`!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_thm INSERT_UNION;;

let INSERT_UNION_EQ = prove
 (`!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`,
  SET_TAC[]);;

export_thm INSERT_UNION_EQ;;

let INSERT_INTER = prove
 (`!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_thm INSERT_INTER;;

let DISJOINT_INSERT = prove
 (`!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\ ~(x IN t)`,
  SET_TAC[]);;

export_thm DISJOINT_INSERT;;

let INSERT_SUBSET = prove
 (`!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`,
  SET_TAC[]);;

export_thm INSERT_SUBSET;;

let SUBSET_INSERT = prove
 (`!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`,
  SET_TAC[]);;

export_thm SUBSET_INSERT;;

let INSERT_DIFF = prove
 (`!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_thm INSERT_DIFF;;

let INSERT_AC = prove
 (`(x INSERT (y INSERT s) = y INSERT (x INSERT s)) /\
   (x INSERT (x INSERT s) = x INSERT s)`,
  REWRITE_TAC[INSERT_COMM; INSERT_INSERT]);;

export_thm INSERT_AC;;

let INTER_ACI = prove
 (`(p INTER q = q INTER p) /\
   ((p INTER q) INTER r = p INTER q INTER r) /\
   (p INTER q INTER r = q INTER p INTER r) /\
   (p INTER p = p) /\
   (p INTER p INTER q = p INTER q)`,
  SET_TAC[]);;

export_thm INTER_ACI;;

let UNION_ACI = prove
 (`(p UNION q = q UNION p) /\
   ((p UNION q) UNION r = p UNION q UNION r) /\
   (p UNION q UNION r = q UNION p UNION r) /\
   (p UNION p = p) /\
   (p UNION p UNION q = p UNION q)`,
  SET_TAC[]);;

export_thm UNION_ACI;;

let DELETE_NON_ELEMENT = prove
 (`!x:A. !s. ~(x IN s) <=> (s DELETE x = s)`,
  SET_TAC[]);;

export_thm DELETE_NON_ELEMENT;;

let IN_DELETE_EQ = prove
 (`!s x. !x':A.
     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))`,
  SET_TAC[]);;

export_thm IN_DELETE_EQ;;

let EMPTY_DELETE = prove
 (`!x:A. EMPTY DELETE x = EMPTY`,
  SET_TAC[]);;

export_thm EMPTY_DELETE;;

let DELETE_DELETE = prove
 (`!x:A. !s. (s DELETE x) DELETE x = s DELETE x`,
  SET_TAC[]);;

export_thm DELETE_DELETE;;

let DELETE_COMM = prove
 (`!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`,
  SET_TAC[]);;

export_thm DELETE_COMM;;

let DELETE_SUBSET = prove
 (`!x:A. !s. (s DELETE x) SUBSET s`,
  SET_TAC[]);;

export_thm DELETE_SUBSET;;

let SUBSET_DELETE = prove
 (`!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\ (s SUBSET t)`,
  SET_TAC[]);;

export_thm SUBSET_DELETE;;

let SUBSET_INSERT_DELETE = prove
 (`!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`,
  SET_TAC[]);;

export_thm SUBSET_INSERT_DELETE;;

let DIFF_INSERT = prove
 (`!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`,
  SET_TAC[]);;

export_thm DIFF_INSERT;;

let PSUBSET_INSERT_SUBSET = prove
 (`!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`,
  SET_TAC[]);;

export_thm PSUBSET_INSERT_SUBSET;;

let PSUBSET_MEMBER = prove
 (`!s:A->bool. !t. s PSUBSET t <=> (s SUBSET t /\ ?y. y IN t /\ ~(y IN s))`,
  SET_TAC[]);;

export_thm PSUBSET_MEMBER;;

let DELETE_INSERT = prove
 (`!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  POP_ASSUM MP_TAC THEN SET_TAC[]);;

export_thm DELETE_INSERT;;

let INSERT_DELETE = prove
 (`!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`,
  SET_TAC[]);;

export_thm INSERT_DELETE;;

let DELETE_INTER = prove
 (`!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`,
  SET_TAC[]);;

export_thm DELETE_INTER;;

let DISJOINT_DELETE_SYM = prove
 (`!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s`,
  SET_TAC[]);;

export_thm DISJOINT_DELETE_SYM;;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNIONS_0 = prove
 (`UNIONS {} = {}`,
  SET_TAC[]);;

export_thm UNIONS_0;;

let UNIONS_1 = prove
 (`UNIONS {s} = s`,
  SET_TAC[]);;

export_thm UNIONS_1;;

let UNIONS_2 = prove
 (`UNIONS {s,t} = s UNION t`,
  SET_TAC[]);;

export_thm UNIONS_2;;

let UNIONS_INSERT = prove
 (`UNIONS (s INSERT u) = s UNION (UNIONS u)`,
  SET_TAC[]);;

export_thm UNIONS_INSERT;;

let FORALL_IN_UNIONS = prove
 (`!P s. (!x. x IN UNIONS s ==> P x) <=> !t x. t IN s /\ x IN t ==> P x`,
  SET_TAC[]);;

export_thm FORALL_IN_UNIONS;;

let EXISTS_IN_UNIONS = prove
 (`!P s. (?x. x IN UNIONS s /\ P x) <=> (?t x. t IN s /\ x IN t /\ P x)`,
  SET_TAC[]);;

export_thm EXISTS_IN_UNIONS;;

let EMPTY_UNIONS = prove
 (`!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}`,
  SET_TAC[]);;

export_thm EMPTY_UNIONS;;

let INTER_UNIONS = prove
 (`(!s t. UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\
   (!s t. t INTER UNIONS s = UNIONS {t INTER x | x IN s})`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[IN_INTER]);;

export_thm INTER_UNIONS;;

let UNIONS_SUBSET = prove
 (`!f t. UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`,
  SET_TAC[]);;

export_thm UNIONS_SUBSET;;

let SUBSET_UNIONS = prove
 (`!f g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`,
  SET_TAC[]);;

export_thm SUBSET_UNIONS;;

let UNIONS_UNION = prove
 (`!s t. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)`,
  SET_TAC[]);;

export_thm UNIONS_UNION;;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTERS_0 = prove
 (`INTERS {} = (:A)`,
  SET_TAC[]);;

export_thm INTERS_0;;

let INTERS_1 = prove
 (`INTERS {s} = s`,
  SET_TAC[]);;

export_thm INTERS_1;;

let INTERS_2 = prove
 (`INTERS {s,t} = s INTER t`,
  SET_TAC[]);;

export_thm INTERS_2;;

let INTERS_INSERT = prove
 (`INTERS (s INSERT u) = s INTER (INTERS u)`,
  SET_TAC[]);;

export_thm INTERS_INSERT;;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_CLAUSES = prove
 (`(IMAGE f {} = {}) /\
   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))`,
  REWRITE_TAC[IMAGE; IN_ELIM_THM; NOT_IN_EMPTY; IN_INSERT; EXTENSION] THEN
  MESON_TAC[]);;

export_thm IMAGE_CLAUSES;;

let IMAGE_UNION = prove
 (`!f s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION] THEN MESON_TAC[]);;

export_thm IMAGE_UNION;;

let IMAGE_ID = prove
 (`!s. IMAGE (\x. x) s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNWIND_THM1]);;

export_thm IMAGE_ID;;

let IMAGE_I = prove
 (`!s. IMAGE I s = s`,
  REWRITE_TAC[I_DEF; IMAGE_ID]);;

export_thm IMAGE_I;;

let IMAGE_o = prove
 (`!f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN MESON_TAC[]);;

export_thm IMAGE_o;;

let IMAGE_SUBSET = prove
 (`!f s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN MESON_TAC[]);;

export_thm IMAGE_SUBSET;;

let IMAGE_INTER_INJ = prove
 (`!f s t. (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER] THEN MESON_TAC[]);;

export_thm IMAGE_INTER_INJ;;

let IMAGE_DIFF_INJ = prove
 (`!f s t. (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF] THEN MESON_TAC[]);;

export_thm IMAGE_DIFF_INJ;;

let IMAGE_DELETE_INJ = prove
 (`!f s a. (!x. (f(x) = f(a)) ==> (x = a))
           ==> (IMAGE f (s DELETE a) = (IMAGE f s) DELETE (f a))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DELETE] THEN MESON_TAC[]);;

export_thm IMAGE_DELETE_INJ;;

let IMAGE_EQ_EMPTY = prove
 (`!f s. (IMAGE f s = {}) <=> (s = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE] THEN MESON_TAC[]);;

export_thm IMAGE_EQ_EMPTY;;

let FORALL_IN_IMAGE = prove
 (`!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

export_thm FORALL_IN_IMAGE;;

let EXISTS_IN_IMAGE = prove
 (`!f s. (?y. y IN IMAGE f s /\ P y) <=> ?x. x IN s /\ P(f x)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

export_thm EXISTS_IN_IMAGE;;

let SUBSET_IMAGE = prove
 (`!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[IMAGE_SUBSET]] THEN
  DISCH_TAC THEN EXISTS_TAC `{x | x IN t /\ (f:A->B) x IN s}` THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  MESON_TAC[]);;

export_thm SUBSET_IMAGE;;

let EXISTS_SUBSET_IMAGE = prove
 (`!P f s.
    (?t. t SUBSET IMAGE f s /\ P t) <=> (?t. t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[SUBSET_IMAGE] THEN MESON_TAC[]);;

export_thm EXISTS_SUBSET_IMAGE;;

let IMAGE_CONST = prove
 (`!s c. IMAGE (\x. c) s = if s = {} then {} else {c}`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_SING] THEN
  ASM_MESON_TAC[MEMBER_NOT_EMPTY]);;

export_thm IMAGE_CONST;;

let SIMPLE_IMAGE = prove
 (`!f s. {f x | x IN s} = IMAGE f s`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]);;

export_thm SIMPLE_IMAGE;;

let SIMPLE_IMAGE_GEN = prove
 (`!f p. {f x | P x} = IMAGE f {x | P x}`,
  SET_TAC[]);;

export_thm SIMPLE_IMAGE_GEN;;

let IMAGE_UNIONS = prove
 (`!f s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`,
  ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_IMAGE] THEN
  MESON_TAC[]);;

export_thm IMAGE_UNIONS;;

let FUN_IN_IMAGE = prove
 (`!f s x. x IN s ==> f(x) IN IMAGE f s`,
  SET_TAC[]);;

export_thm FUN_IN_IMAGE;;

let SURJECTIVE_IMAGE_EQ = prove
 (`!s t. (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
         ==> IMAGE f s = t`,
  SET_TAC[]);;

export_thm SURJECTIVE_IMAGE_EQ;;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EMPTY_GSPEC = prove
 (`{x | F} = {}`,
  SET_TAC[]);;

export_thm EMPTY_GSPEC;;

let SING_GSPEC = prove
 (`(!a. {x | x = a} = {a}) /\
   (!a. {x | a = x} = {a})`,
  SET_TAC[]);;

export_thm SING_GSPEC;;

let IN_ELIM_PAIR_THM = prove
 (`!P a b. (a,b) IN {(x,y) | P x y} <=> P a b`,
  REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[PAIR_EQ]);;

export_thm IN_ELIM_PAIR_THM;;

let SET_PAIR_THM = prove
 (`!P. {p | P p} = {(a,b) | P(a,b)}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_ELIM_PAIR_THM]);;

export_thm SET_PAIR_THM;;

let FORALL_IN_GSPEC = prove
 (`(!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\
   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>
          (!x y. P x y ==> Q(f x y))) /\
   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>
          (!w x y. P w x y ==> Q(f w x y)))`,
  SET_TAC[]);;

export_thm FORALL_IN_GSPEC;;

let EXISTS_IN_GSPEC = prove
 (`(!P f. (?z. z IN {f x | P x} /\ Q z) <=> (?x. P x /\ Q(f x))) /\
   (!P f. (?z. z IN {f x y | P x y} /\ Q z) <=>
          (?x y. P x y /\ Q(f x y))) /\
   (!P f. (?z. z IN {f w x y | P w x y} /\ Q z) <=>
          (?w x y. P w x y /\ Q(f w x y)))`,
  SET_TAC[]);;

export_thm EXISTS_IN_GSPEC;;

let SET_PROVE_CASES = prove
 (`!P:(A->bool)->bool.
       P {} /\ (!a s. ~(a IN s) ==> P(a INSERT s))
       ==> !s. P s`,
  MESON_TAC[SET_CASES]);;

export_thm SET_PROVE_CASES;;

let UNIONS_IMAGE = prove
 (`!f s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

export_thm UNIONS_IMAGE;;

let INTERS_IMAGE = prove
 (`!f s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`,
  REPEAT GEN_TAC THEN  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

export_thm INTERS_IMAGE;;

let UNIONS_GSPEC = prove
 (`(!P f. UNIONS {f x | P x} = {a | ?x. P x /\ a IN (f x)}) /\
   (!P f. UNIONS {f x y | P x y} = {a | ?x y. P x y /\ a IN (f x y)}) /\
   (!P f. UNIONS {f x y z | P x y z} =
            {a | ?x y z. P x y z /\ a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

export_thm UNIONS_GSPEC;;

let INTERS_GSPEC = prove
 (`(!P f. INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\
   (!P f. INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\
   (!P f. INTERS {f x y z | P x y z} =
                {a | !x y z. P x y z ==> a IN (f x y z)})`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]);;

export_thm INTERS_GSPEC;;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "set-finite-def";;

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY:A->bool) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

export_thm FINITE_RULES;;
export_thm FINITE_INDUCT;;
export_thm FINITE_CASES;;

let INFINITE = new_definition
  `INFINITE (s:A->bool) <=> ~(FINITE s)`;;

export_thm INFINITE;;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

logfile "set-finite-thm";;

let FINITE_INDUCT_STRONG = prove
 (`!P:(A->bool)->bool.
        P {} /\ (!x s. P s /\ ~(x IN s) /\ FINITE s ==> P(x INSERT s))
        ==> !s. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:A->bool. FINITE s ==> FINITE s /\ P s` MP_TAC THENL
   [ALL_TAC; MESON_TAC[]] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN ASM_SIMP_TAC[FINITE_RULES] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `x:A INSERT s = s` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

export_thm FINITE_INDUCT_STRONG;;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

let FINITE_EMPTY = prove
 (`FINITE {}`,
  REWRITE_TAC[FINITE_RULES]);;

export_thm FINITE_EMPTY;;

let FINITE_SUBSET = prove
 (`!(s:A->bool) t. FINITE t /\ s SUBSET t ==> FINITE s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [MESON_TAC[SUBSET_EMPTY; FINITE_RULES]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  X_GEN_TAC `t:A->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE((x:A) INSERT (t DELETE x))` ASSUME_TAC THENL
   [MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t SUBSET (x:A INSERT u)` THEN SET_TAC[];
    ASM_CASES_TAC `x:A IN t` THENL
     [SUBGOAL_THEN `x:A INSERT (t DELETE x) = t` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `x:A IN t` THEN SET_TAC[]; ASM_REWRITE_TAC[]];
      FIRST_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `t SUBSET x:A INSERT u` THEN
      UNDISCH_TAC `~(x:A IN t)` THEN SET_TAC[]]]);;

export_thm FINITE_SUBSET;;

let FINITE_UNION_IMP = prove
 (`!(s:A->bool) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN `!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)`
  (fun th -> REWRITE_TAC[th]) THENL
   [SET_TAC[];
    MESON_TAC[FINITE_RULES]]);;

export_thm FINITE_UNION_IMP;;

let FINITE_UNION = prove
 (`!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(s:A->bool) UNION t` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_ACCEPT_TAC FINITE_UNION_IMP]);;

export_thm FINITE_UNION;;

let FINITE_INTER = prove
 (`!(s:A->bool) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`,
  MESON_TAC[INTER_SUBSET; FINITE_SUBSET]);;

export_thm FINITE_INTER;;

let FINITE_INSERT = prove
 (`!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `x:A INSERT s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC(CONJUNCT2 FINITE_RULES) THEN
    ASM_REWRITE_TAC[]]);;

export_thm FINITE_INSERT;;

let FINITE_SING = prove
 (`!a. FINITE {a}`,
  REWRITE_TAC[FINITE_INSERT; FINITE_RULES]);;

export_thm FINITE_SING;;

let FINITE_DELETE_IMP = prove
 (`!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

export_thm FINITE_DELETE_IMP;;

let FINITE_DELETE = prove
 (`!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[FINITE_DELETE_IMP] THEN
  ASM_CASES_TAC `x:A IN s` THENL
   [SUBGOAL_THEN `s = x INSERT (s DELETE x:A)`
    (fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[FINITE_INSERT] THEN POP_ASSUM MP_TAC THEN SET_TAC[];
    SUBGOAL_THEN `s DELETE x:A = s` (fun th -> REWRITE_TAC[th]) THEN
    POP_ASSUM MP_TAC THEN SET_TAC[]]);;

export_thm FINITE_DELETE;;

let FINITE_FINITE_UNIONS = prove
 (`!s. FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; UNIONS_0; UNIONS_INSERT] THEN
  REWRITE_TAC[FINITE_UNION; FINITE_RULES] THEN MESON_TAC[]);;

export_thm FINITE_FINITE_UNIONS;;

let FINITE_IMAGE_EXPAND = prove
 (`!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
  REWRITE_TAC[NOT_IN_EMPTY; REWRITE_RULE[] EMPTY_GSPEC; FINITE_RULES] THEN
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[FINITE_UNION; FINITE_INSERT; FINITE_RULES]]);;

export_thm FINITE_IMAGE_EXPAND;;

let FINITE_IMAGE = prove
 (`!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`,
  REWRITE_TAC[IMAGE; FINITE_IMAGE_EXPAND]);;

export_thm FINITE_IMAGE;;

let FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f:A->B) A s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                  FINITE A ==> FINITE {x | x IN s /\ f(x) IN A}`,
  GEN_TAC THEN ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN GEN_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x IN EMPTY} = EMPTY`
    SUBST1_TAC THEN REWRITE_TAC[FINITE_RULES] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]; ALL_TAC] THEN
  X_GEN_TAC `y:B` THEN X_GEN_TAC `t:B->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `{x | x IN s /\ (f:A->B) x IN (y INSERT t)} =
                if (?x. x IN s /\ (f x = y))
                then (@x. x IN s /\ (f x = y)) INSERT {x | x IN s /\ f x IN t}
                else {x | x IN s /\ f x IN t}`
  SUBST1_TAC THENL
   [ALL_TAC; COND_CASES_TAC THEN ASM_REWRITE_TAC[FINITE_INSERT]] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  FIRST_ASSUM(MP_TAC o SELECT_RULE) THEN
  ABBREV_TAC `z = @x. x IN s /\ ((f:A->B) x = y)` THEN
  ASM_MESON_TAC[]);;

export_thm FINITE_IMAGE_INJ_GENERAL;;

let FINITE_FINITE_PREIMAGE_GENERAL = prove
 (`!f:A->B s t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | x IN s /\ f(x) = y})
        ==> FINITE {x | x IN s /\ f(x) IN t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN s /\ (f:A->B)(x) IN t} =
    UNIONS (IMAGE (\a. {x | x IN s /\ f x = a}) t)`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN SET_TAC[];
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]]);;

export_thm FINITE_FINITE_PREIMAGE_GENERAL;;

let FINITE_FINITE_PREIMAGE = prove
 (`!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`,
  REPEAT GEN_TAC THEN MP_TAC
   (ISPECL [`f:A->B`; `(:A)`; `t:B->bool`] FINITE_FINITE_PREIMAGE_GENERAL) THEN
  REWRITE_TAC[IN_UNIV]);;

export_thm FINITE_FINITE_PREIMAGE;;

let FINITE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[IMP_IMP] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]);;

export_thm FINITE_IMAGE_INJ_EQ;;

let FINITE_IMAGE_INJ = prove
 (`!(f:A->B) A. (!x y. (f(x) = f(y)) ==> (x = y)) /\
                FINITE A ==> FINITE {x | f(x) IN A}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`f:A->B`; `A:B->bool`; `UNIV:A->bool`]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);;

export_thm FINITE_IMAGE_INJ;;

let INFINITE_IMAGE_INJ = prove
 (`!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{x | f(x) IN IMAGE (f:A->B) s}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IMAGE] THEN MESON_TAC[]]);;

export_thm INFINITE_IMAGE_INJ;;

let INFINITE_NONEMPTY = prove
 (`!s. INFINITE(s) ==> ~(s = EMPTY)`,
  MESON_TAC[INFINITE; FINITE_RULES]);;

export_thm INFINITE_NONEMPTY;;

let INFINITE_DIFF_FINITE = prove
 (`!s:A->bool t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC(TAUT `(b /\ ~c ==> ~a) ==> a /\ b ==> c`) THEN
  REWRITE_TAC[INFINITE] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(t:A->bool) UNION (s DIFF t)` THEN
  ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[]);;

export_thm INFINITE_DIFF_FINITE;;

let FINITE_SUBSET_IMAGE = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[FINITE_IMAGE; IMAGE_SUBSET]] THEN
  STRIP_TAC THEN
  EXISTS_TAC `IMAGE (\y. @x. x IN s /\ ((f:A->B)(x) = y)) t` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[EXTENSION; SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_IMAGE]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN X_GEN_TAC `y:B` THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN ONCE_REWRITE_TAC[CONJ_SYM] THEN
  REWRITE_TAC[UNWIND_THM2; GSYM CONJ_ASSOC] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

export_thm FINITE_SUBSET_IMAGE;;

let EXISTS_FINITE_SUBSET_IMAGE = prove
 (`!P f s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ P t) <=>
    (?t. FINITE t /\ t SUBSET s /\ P (IMAGE f t))`,
  REWRITE_TAC[FINITE_SUBSET_IMAGE; CONJ_ASSOC] THEN MESON_TAC[]);;

export_thm EXISTS_FINITE_SUBSET_IMAGE;;

let FINITE_SUBSET_IMAGE_IMP = prove
 (`!f:A->B s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`,
  MESON_TAC[SUBSET_REFL; FINITE_SUBSET_IMAGE]);;

export_thm FINITE_SUBSET_IMAGE_IMP;;

let FINITE_DIFF = prove
 (`!s t. FINITE s ==> FINITE(s DIFF t)`,
  MESON_TAC[FINITE_SUBSET; SUBSET_DIFF]);;

export_thm FINITE_DIFF;;

let FINITE_RESTRICT = prove
 (`!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\ P x}`,
  MESON_TAC[SUBSET_RESTRICT; FINITE_SUBSET]);;

export_thm FINITE_RESTRICT;;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

logfile "set-fold-def";;

let FINREC = new_recursive_definition num_RECURSION
  `(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

let FINREC_1_LEMMA = prove
 (`!f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)`,
  REWRITE_TAC[FINREC] THEN
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN ABS_TAC THEN SET_TAC[]);;

let FINREC_SUC_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`,
  let lem = prove(`s DELETE (x:A) DELETE y = s DELETE y DELETE x`,SET_TAC[]) in
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC_1_LEMMA] THEN REWRITE_TAC[FINREC] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `b:B` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:A` MP_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `c:B` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `FINREC (f:A->B->B) b (s DELETE y) c (SUC n)` THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(f:A->B->B) y v` THEN ASM_REWRITE_TAC[FINREC] THEN
      CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`y:A`; `v:B`] THEN
        ONCE_REWRITE_TAC[lem] THEN ASM_REWRITE_TAC[IN_DELETE];
        FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let FINREC_UNIQUE_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    REWRITE_TAC[FINREC] THEN MESON_TAC[NOT_IN_EMPTY];
    IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN REPEAT GEN_TAC THEN
    DISCH_THEN(fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC th) THEN
    DISCH_THEN(CONJUNCTS_THEN (ANTE_RES_THEN ASSUME_TAC)) THEN
    REWRITE_TAC[FINREC] THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

let FINREC_EXISTS_LEMMA = prove
 (`!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`,
  let lem = prove(`~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)`,SET_TAC[]) in
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:B`; `0`] THEN REWRITE_TAC[FINREC];
    MAP_EVERY EXISTS_TAC [`(f:A->B->B) x a`; `SUC n`] THEN
    REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [`x:A`; `a:B`] THEN
    FIRST_ASSUM(fun th -> ASM_REWRITE_TAC[MATCH_MP lem th; IN_INSERT])]);;

let FINREC_FUN_LEMMA = prove
 (`!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\s:A. @a:B. ?n:C. R s a n` THEN
  REPEAT STRIP_TAC THEN BETA_TAC THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN ASM_MESON_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SELECT_CONV THEN
    ASM_MESON_TAC[]]);;

let FINREC_FUN = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !s x. FINITE s /\ x IN s
                      ==> (g s = f x (g (s DELETE x)))`,
  REPEAT STRIP_TAC THEN IMP_RES_THEN MP_TAC FINREC_UNIQUE_LEMMA THEN
  DISCH_THEN(MP_TAC o SPEC `b:B`) THEN DISCH_THEN
   (MP_TAC o CONJ (SPECL [`f:A->B->B`; `b:B`] FINREC_EXISTS_LEMMA)) THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINREC_FUN_LEMMA) THEN
  DISCH_THEN(X_CHOOSE_TAC `g:(A->bool)->B`) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `FINITE(EMPTY:A->bool)`
    (ANTE_RES_THEN (fun th -> GEN_REWRITE_TAC I [GSYM th])) THENL
     [REWRITE_TAC[FINITE_RULES];
      EXISTS_TAC `0` THEN REWRITE_TAC[FINREC]];
    REPEAT STRIP_TAC THEN
    ANTE_RES_THEN MP_TAC (ASSUME `FINITE(s:A->bool)`) THEN
    DISCH_THEN(ASSUME_TAC o GSYM) THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o SPEC `(g:(A->bool)->B) s`) THEN
    REWRITE_TAC[] THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    INDUCT_TAC THENL
     [ASM_REWRITE_TAC[FINREC] THEN DISCH_TAC THEN UNDISCH_TAC `x:A IN s` THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY];
      IMP_RES_THEN ASSUME_TAC FINREC_SUC_LEMMA THEN
      DISCH_THEN(ANTE_RES_THEN (MP_TAC o SPEC `x:A`)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:B` (CONJUNCTS_THEN ASSUME_TAC)) THEN
      SUBGOAL_THEN `(g (s DELETE x:A) = w:B)` SUBST1_TAC THENL
       [SUBGOAL_THEN `FINITE(s DELETE x:A)` MP_TAC THENL
         [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          DISCH_THEN(ANTE_RES_THEN (MP_TAC o GSYM)) THEN
          DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
          EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[]];
        ASM_REWRITE_TAC[]]]]);;

let SET_RECURSION_LEMMA = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:B` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A->bool)->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:(A->bool)->B` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THENL
   [AP_TERM_TAC THEN REWRITE_TAC[GSYM ABSORPTION] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `FINITE(x:A INSERT s) /\ x IN (x INSERT s)` MP_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[FINITE_RULES];
      DISCH_THEN(ANTE_RES_THEN SUBST1_TAC) THEN
      REPEAT AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]]);;

let ITSET = new_definition
  `ITSET f s b =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

let FINITE_RECURSION = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f (x INSERT s) b =
                       if x IN s then ITSET f s b
                                 else f x (ITSET f s b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITSET] THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
  ASM_REWRITE_TAC[]);;

export_thm FINITE_RECURSION;;

logfile "set-fold-thm";;

let FINITE_RECURSION_DELETE = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f {} b = b) /\
            !x s. FINITE s
                  ==> (ITSET f s b =
                       if x IN s then f x (ITSET f (s DELETE x) b)
                                 else ITSET f (s DELETE x) b)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP FINITE_RECURSION) THEN
  DISCH_THEN(STRIP_ASSUME_TAC o SPEC `b:B`) THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN s` THEN ASM_REWRITE_TAC[] THENL
   [DISCH_THEN(MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
    DISCH_THEN(ANTE_RES_THEN MP_TAC o SPEC `x:A`) THEN
    DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
    REWRITE_TAC[IN_DELETE] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN UNDISCH_TAC `x:A IN s` THEN SET_TAC[];
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

export_thm FINITE_RECURSION_DELETE;;

let ITSET_EQ = prove
 (`!s f g b. FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
             (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
             (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
             ==> (ITSET f s b = ITSET g s b)`,
  ONCE_REWRITE_TAC[IMP_CONJ] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[FINITE_RECURSION; NOT_IN_EMPTY; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[RIGHT_IMP_FORALL_THM]) THEN
  ASM_MESON_TAC[]);;

export_thm ITSET_EQ;;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-def";;

let CARD = new_definition
 `CARD s = ITSET (\x n. SUC n) s 0`;;

export_thm CARD;;

logfile "set-size-thm";;

let CARD_CLAUSES = prove
 (`(CARD ({}:A->bool) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`,
  MP_TAC(ISPECL [`\(x:A) n. SUC n`; `0`] FINITE_RECURSION) THEN
  REWRITE_TAC[CARD]);;

export_thm CARD_CLAUSES;;

let CARD_UNION = prove
 (`!(s:A->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; CARD_CLAUSES; INTER_EMPTY; ADD_CLAUSES] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `s:A->bool` THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:A INSERT s) UNION t = x INSERT (s UNION t)`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((s:A->bool) UNION t) /\ FINITE s`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FINITE_UNION_IMP THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool`] (CONJUNCT2 CARD_CLAUSES)) THEN
  MP_TAC(ISPECL [`x:A`; `s:A->bool UNION t`] (CONJUNCT2 CARD_CLAUSES)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:A IN (s UNION t))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION] THEN
    UNDISCH_TAC `(x:A INSERT s) INTER t = EMPTY` THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ASM_REWRITE_TAC[SUC_INJ; ADD_CLAUSES] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `x:A INSERT s INTER t = EMPTY` THEN SET_TAC[]]);;

export_thm CARD_UNION;;

let CARD_DELETE = prove
 (`!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SUBGOAL_THEN `s = x:A INSERT (s DELETE x)`
     (fun th -> GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [th])
    THENL [UNDISCH_TAC `x:A IN s` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_DELETE; IN_DELETE] THEN ARITH_TAC;
    AP_TERM_TAC THEN UNDISCH_TAC `~(x:A IN s)` THEN SET_TAC[]]);;

export_thm CARD_DELETE;;

let CARD_UNION_EQ = prove
 (`!s t u. FINITE u /\ (s INTER t = {}) /\ (s UNION t = u)
           ==> (CARD s + CARD t = CARD u)`,
  MESON_TAC[CARD_UNION; FINITE_SUBSET; SUBSET_UNION]);;

export_thm CARD_UNION_EQ;;

let CARD_DIFF = prove
 (`!s t. FINITE s /\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ARITH_RULE `a + b:num = c ==> a = c - b`) THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]);;

export_thm CARD_DIFF;;

let CARD_EQ_0 = prove
 (`!s. FINITE s ==> ((CARD s = 0) <=> (s = {}))`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_INSERT_EMPTY; NOT_SUC]);;

export_thm CARD_EQ_0;;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = prove
 (`!P. P {} /\
       (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (P(s DELETE x) ==> P s))
       ==> !s:A->bool. FINITE s ==> P s`,
  GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(s:A->bool)` THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!s. FINITE s /\ ~(s = {}) ==> ?x:A. x IN s /\ (P(s DELETE x) ==> P s)` THEN
  DISCH_THEN(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (x:A)`) THEN
  ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; CARD_EQ_0;
               ARITH_RULE `n - 1 < n <=> ~(n = 0)`]);;

export_thm FINITE_INDUCT_DELETE;;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-def";;

let HAS_SIZE = new_definition
  `s HAS_SIZE n <=> FINITE s /\ (CARD s = n)`;;

export_thm HAS_SIZE;;

logfile "set-size-thm";;

let HAS_SIZE_CARD = prove
 (`!s n. s HAS_SIZE n ==> (CARD s = n)`,
  SIMP_TAC[HAS_SIZE]);;

export_thm HAS_SIZE_CARD;;

let HAS_SIZE_0 = prove
 (`!(s:A->bool) n. s HAS_SIZE 0 <=> (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  EQ_TAC THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[FINITE_RULES; CARD_CLAUSES] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1) THEN
  SPEC_TAC(`s:A->bool`,`s:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
  ASM_REWRITE_TAC[NOT_SUC]);;

export_thm HAS_SIZE_0;;

let HAS_SIZE_SUC = prove
 (`!(s:A->bool) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES; FINITE_RULES; NOT_IN_EMPTY; NOT_SUC] THEN
  REWRITE_TAC[FINITE_DELETE] THEN
  ASM_CASES_TAC `FINITE(s:A->bool)` THEN
  ASM_REWRITE_TAC[NOT_FORALL_THM; MEMBER_NOT_EMPTY] THEN
  EQ_TAC THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_REWRITE_TAC[SUC_INJ] THEN MESON_TAC[]];
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    DISCH_THEN(X_CHOOSE_TAC `a:A`) THEN
    MP_TAC(ISPECL [`a:A`; `s DELETE a:A`] (CONJUNCT2 CARD_CLAUSES)) THEN
    ASM_REWRITE_TAC[FINITE_DELETE; IN_DELETE] THEN
    SUBGOAL_THEN `a INSERT (s DELETE a:A) = s` SUBST1_TAC THENL
     [UNDISCH_TAC `a:A IN s` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

export_thm HAS_SIZE_SUC;;

let HAS_SIZE_UNION = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
             ==> (s UNION t) HAS_SIZE (m + n)`,
  SIMP_TAC[HAS_SIZE; FINITE_UNION; DISJOINT; CARD_UNION]);;

export_thm HAS_SIZE_UNION;;

let HAS_SIZE_DIFF = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
             ==> (s DIFF t) HAS_SIZE (m - n)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF]);;

export_thm HAS_SIZE_DIFF;;

let HAS_SIZE_UNIONS = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CARD_CLAUSES] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0; EMPTY_UNIONS] THEN
    REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `m:num`; `n:num`] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}`] THEN
  REWRITE_TAC[ARITH_RULE `SUC a * b = b + a * b`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC[IN_INSERT] THEN
  REWRITE_TAC[SET_RULE
   `DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x`] THEN
  ASM_SIMP_TAC[IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
  ASM_MESON_TAC[IN_INSERT]);;

export_thm HAS_SIZE_UNIONS;;

let FINITE_HAS_SIZE = prove
 (`!s. FINITE s <=> s HAS_SIZE CARD s`,
  REWRITE_TAC[HAS_SIZE]);;

export_thm FINITE_HAS_SIZE;;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CLAUSES = prove
 (`(s HAS_SIZE 0 <=> (s = {})) /\
   (s HAS_SIZE (SUC n) <=>
        ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,
  let lemma = SET_RULE `a IN s ==> (s = a INSERT (s DELETE a))` in
  REWRITE_TAC[HAS_SIZE_0] THEN REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
    MESON_TAC[lemma; IN_DELETE];
    SIMP_TAC[LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;

export_thm HAS_SIZE_CLAUSES;;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = prove
   (`(~(a IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`,
    SET_TAC[])
  and qth = prove
   (`((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
     ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
      (?a s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))`,
    REWRITE_TAC[HAS_SIZE_CLAUSES] THEN MESON_TAC[]) in
  let qconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 qth]
  and qconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 qth]
  and rconv_0 = GEN_REWRITE_CONV I [CONJUNCT1 pth]
  and rconv_1 = GEN_REWRITE_CONV I [CONJUNCT2 pth] in
  let rec EXISTS_HAS_SIZE_AND_CONV tm =
   (qconv_0 ORELSEC
    (BINDER_CONV(LAND_CONV(RAND_CONV num_CONV)) THENC
     qconv_1 THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV)) tm in
  let rec NOT_IN_INSERT_CONV tm =
   ((rconv_0 THENC NOT_IN_INSERT_CONV) ORELSEC
    (rconv_1 THENC RAND_CONV NOT_IN_INSERT_CONV) ORELSEC
    ALL_CONV) tm in
  let HAS_SIZE_CONV =
    GEN_REWRITE_CONV I [CONJUNCT1 HAS_SIZE_CLAUSES] ORELSEC
    (RAND_CONV num_CONV THENC
     GEN_REWRITE_CONV I [CONJUNCT2 HAS_SIZE_CLAUSES] THENC
     BINDER_CONV EXISTS_HAS_SIZE_AND_CONV) in
  fun tm ->
    let th = HAS_SIZE_CONV tm in
    let tm' = rand(concl th) in
    let evs,bod = strip_exists tm' in
    if evs = [] then th else
    let th' = funpow (length evs) BINDER_CONV NOT_IN_INSERT_CONV tm' in
    TRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Various useful lemmas about cardinalities of unions etc.                  *)
(* ------------------------------------------------------------------------- *)

let CARD_SUBSET_EQ = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`a:A->bool`; `b DIFF (a:A->bool)`] CARD_UNION) THEN
  SUBGOAL_THEN `FINITE(a:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(b:A->bool DIFF a)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `a:A->bool INTER (b DIFF a) = EMPTY` ASSUME_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a UNION (b:A->bool DIFF a) = b` ASSUME_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[ARITH_RULE `(a = a + b) <=> (b = 0)`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `b:A->bool DIFF a = EMPTY` MP_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE_0] THEN
    ASM_REWRITE_TAC[HAS_SIZE];
    UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]]);;

export_thm CARD_SUBSET_EQ;;

let CARD_SUBSET = prove
 (`!(a:A->bool) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b:A->bool = a UNION (b DIFF a)` SUBST1_TAC THENL
   [UNDISCH_TAC `a:A->bool SUBSET b` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `b:A->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SET_TAC[]];
    ARITH_TAC]);;

export_thm CARD_SUBSET;;

let CARD_SUBSET_LE = prove
 (`!(a:A->bool) b. FINITE b /\ a SUBSET b /\ (CARD b <= CARD a) ==> (a = b)`,
  MESON_TAC[CARD_SUBSET; CARD_SUBSET_EQ; LE_ANTISYM]);;

export_thm CARD_SUBSET_LE;;

let SUBSET_CARD_EQ = prove
 (`!s t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`,
  MESON_TAC[CARD_SUBSET_EQ; LE_ANTISYM; CARD_SUBSET]);;

export_thm SUBSET_CARD_EQ;;

let CARD_PSUBSET = prove
 (`!(a:A->bool) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SET_RULE
   `a PSUBSET b <=> ?x. x IN b /\ ~(x IN a) /\ a SUBSET (b DELETE x)` ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:A` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC LET_TRANS THEN EXISTS_TAC `CARD(b DELETE (x:A))` THEN
  ASM_SIMP_TAC[CARD_SUBSET; FINITE_DELETE] THEN
  ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `n - 1 < n <=> ~(n = 0)`] THEN
  ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]);;

export_thm CARD_PSUBSET;;

let CARD_UNION_LE = prove
 (`!s t:A->bool.
        FINITE s /\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(s:A->bool) + CARD(t DIFF s)` THEN
  ASM_SIMP_TAC[LE_ADD_LCANCEL; CARD_SUBSET; SUBSET_DIFF; FINITE_DIFF] THEN
  MATCH_MP_TAC EQ_IMP_LE THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

export_thm CARD_UNION_LE;;

let CARD_UNIONS_LE = prove
 (`!s t:A->B->bool m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE(t x) /\ CARD(t x) <= n)
        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THEN
  REWRITE_TAC[SET_RULE `UNIONS {t x | x IN {}} = {}`; CARD_CLAUSES; LE_0] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_RULES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
  REWRITE_TAC[SET_RULE
   `UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}`] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
   `CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN ASM_SIMP_TAC[IN_INSERT] THEN
    REWRITE_TAC[SET_RULE `{t x | x IN s} = IMAGE t s`] THEN
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE;
                 IN_INSERT];
    MATCH_MP_TAC(ARITH_RULE `a <= n /\ b <= x * n ==> a + b <= SUC x * n`) THEN
    ASM_SIMP_TAC[IN_INSERT]]);;

export_thm CARD_UNIONS_LE;;

let CARD_UNION_GEN = prove
 (`!s t. FINITE s /\ FINITE t
         ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `s UNION t = s UNION (t DIFF s)`] THEN
  ASM_SIMP_TAC[ARITH_RULE `x:num <= y ==> (a + y) - x = a + (y - x)`;
               CARD_SUBSET; INTER_SUBSET; GSYM CARD_DIFF] THEN
  REWRITE_TAC[SET_RULE `t DIFF (s INTER t) = t DIFF s`] THEN
  MATCH_MP_TAC CARD_UNION THEN ASM_SIMP_TAC[FINITE_DIFF] THEN SET_TAC[]);;

export_thm CARD_UNION_GEN;;

let CARD_UNION_OVERLAP_EQ = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_UNION_GEN] THEN
  REWRITE_TAC[ARITH_RULE `a - b = a <=> b = 0 \/ a = 0`] THEN
  ASM_SIMP_TAC[ADD_EQ_0; CARD_EQ_0; FINITE_INTER] THEN SET_TAC[]);;

export_thm CARD_UNION_OVERLAP_EQ;;

let CARD_UNION_OVERLAP = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD(s UNION t) < CARD(s) + CARD(t)
         ==> ~(s INTER t = {})`,
  SIMP_TAC[GSYM CARD_UNION_OVERLAP_EQ] THEN ARITH_TAC);;

export_thm CARD_UNION_OVERLAP;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                FINITE s ==> (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  REWRITE_TAC[TAUT `a /\ b ==> c <=> b ==> a ==> c`] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_IMAGE; IN_IMAGE] THEN
  COND_CASES_TAC THEN ASM_MESON_TAC[IN_INSERT]);;

export_thm CARD_IMAGE_INJ;;

let HAS_SIZE_IMAGE_INJ = prove
 (`!(f:A->B) s n.
        (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n
        ==> (IMAGE f s) HAS_SIZE n`,
  SIMP_TAC[HAS_SIZE; FINITE_IMAGE] THEN MESON_TAC[CARD_IMAGE_INJ]);;

export_thm HAS_SIZE_IMAGE_INJ;;

let CARD_IMAGE_LE = prove
 (`!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE; LE_REFL] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
  DISCH_THEN(MP_TAC o CONJUNCT1) THEN ARITH_TAC);;

export_thm CARD_IMAGE_LE;;

let CARD_IMAGE_INJ_EQ = prove
 (`!f:A->B s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

export_thm CARD_IMAGE_INJ_EQ;;

let CARD_SUBSET_IMAGE = prove
 (`!f s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`,
  MESON_TAC[LE_TRANS; FINITE_IMAGE; CARD_IMAGE_LE; CARD_SUBSET]);;

export_thm CARD_SUBSET_IMAGE;;

let HAS_SIZE_IMAGE_INJ_EQ = prove
 (`!f s n.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT
   `(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)`) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ;
    DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CARD_IMAGE_INJ] THEN
  ASM_REWRITE_TAC[]);;

export_thm HAS_SIZE_IMAGE_INJ_EQ;;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSET_STRONG = prove
 (`!n s:A->bool.
        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  INDUCT_TAC THEN REWRITE_TAC[HAS_SIZE_0; HAS_SIZE_SUC] THENL
   [MESON_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SET_PROVE_CASES THEN
  REWRITE_TAC[FINITE_EMPTY; CARD_CLAUSES; ARITH_RULE `~(SUC n <= 0)`] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; LE_SUC] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:A) INSERT t` THEN
  REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
  ASM_SIMP_TAC[HAS_SIZE; CARD_DELETE; FINITE_INSERT; FINITE_DELETE;
               CARD_CLAUSES] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[SUC_SUB1] THEN
  ASM SET_TAC[]);;

export_thm CHOOSE_SUBSET_STRONG;;

let CHOOSE_SUBSET = prove
 (`!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  MESON_TAC[CHOOSE_SUBSET_STRONG]);;

export_thm CHOOSE_SUBSET;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_PRODUCT_DEPENDENT = prove
 (`!s m t n.
         s HAS_SIZE m /\ (!x. x IN s ==> t(x) HAS_SIZE n)
         ==> {(x:A,y:B) | x IN s /\ y IN t(x)} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[CARD_CLAUSES; NOT_IN_EMPTY; IN_INSERT] THEN CONJ_TAC THENL
   [GEN_TAC THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `m:num` THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MAP_EVERY X_GEN_TAC [`t:A->B->bool`; `n:num`] THEN
  REWRITE_TAC[TAUT `a \/ b ==> c <=> (a ==> c) /\ (b ==> c)`] THEN
  SIMP_TAC[FORALL_AND_THM; LEFT_FORALL_IMP_THM; EXISTS_REFL] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s:A->bool)`) THEN
  ASM_REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
  REWRITE_TAC[SET_RULE
    `{(x,y) | (x = a \/ x IN s) /\ y IN t(x)} =
     {(x,y) | x IN s /\ y IN t(x)} UNION
     IMAGE (\y. (a,y)) (t a)`] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN
  ASM_SIMP_TAC[HAS_SIZE_IMAGE_INJ; PAIR_EQ] THEN
  REWRITE_TAC[DISJOINT; IN_IMAGE; IN_ELIM_THM; IN_INTER; EXTENSION;
              NOT_IN_EMPTY; EXISTS_PAIR_THM; PAIR_EQ] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[PAIR_EQ]);;

export_thm HAS_SIZE_PRODUCT_DEPENDENT;;

let FINITE_PRODUCT_DEPENDENT = prove
 (`!f:A->B->C s t.
        FINITE s /\ (!x. x IN s ==> FINITE(t x))
        ==> FINITE {f x y | x IN s /\ y IN (t x)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\(x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}` THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC FINITE_IMAGE; MESON_TAC[]] THEN
  MAP_EVERY UNDISCH_TAC
   [`!x:A. x IN s ==> FINITE(t x :B->bool)`; `FINITE(s:A->bool)`] THEN
  MAP_EVERY (fun t -> SPEC_TAC(t,t)) [`t:A->B->bool`; `s:A->bool`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN SUBGOAL_THEN `{(x:A,y:B) | x IN {} /\ y IN (t x)} = {}`
     (fun th -> REWRITE_TAC[th; FINITE_RULES]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `s:A->bool`] THEN STRIP_TAC THEN
  X_GEN_TAC `t:A->B->bool` THEN
  SUBGOAL_THEN
   `{(x:A,y:B) | x IN (a INSERT s) /\ y IN (t x)} =
    IMAGE (\y. a,y) (t a) UNION {(x,y) | x IN s /\ y IN (t x)}`
   (fun th -> ASM_SIMP_TAC[IN_INSERT; FINITE_IMAGE; FINITE_UNION; th]) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_INSERT; IN_UNION] THEN
  MESON_TAC[]);;

export_thm FINITE_PRODUCT_DEPENDENT;;

let FINITE_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`,
  SIMP_TAC[FINITE_PRODUCT_DEPENDENT]);;

export_thm FINITE_PRODUCT;;

let CARD_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`s:A->bool`; `CARD(s:A->bool)`; `\x:A. t:B->bool`;
                  `CARD(t:B->bool)`] HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_SIMP_TAC[HAS_SIZE]);;

export_thm CARD_PRODUCT;;

let HAS_SIZE_PRODUCT = prove
 (`!s m t n. s HAS_SIZE m /\ t HAS_SIZE n
             ==> {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`,
  SIMP_TAC[HAS_SIZE; CARD_PRODUCT; FINITE_PRODUCT]);;

export_thm HAS_SIZE_PRODUCT;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

logfile "set-def";;

let CROSS = new_definition
 `s CROSS t = {x,y | x IN s /\ y IN t}`;;

export_thm CROSS;;

logfile "set-thm";;

let IN_CROSS = prove
 (`!x y s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC[CROSS; IN_ELIM_PAIR_THM]);;

export_thm IN_CROSS;;

logfile "set-size-thm";;

let HAS_SIZE_CROSS = prove
 (`!s t m n. s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`,
  REWRITE_TAC[CROSS; HAS_SIZE_PRODUCT]);;

export_thm HAS_SIZE_CROSS;;

logfile "set-finite-thm";;

let FINITE_CROSS = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE(s CROSS t)`,
  SIMP_TAC[CROSS; FINITE_PRODUCT]);;

export_thm FINITE_CROSS;;

logfile "set-size-thm";;

let CARD_CROSS = prove
 (`!s t. FINITE s /\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t`,
  SIMP_TAC[CROSS; CARD_PRODUCT]);;

export_thm CARD_CROSS;;

let CROSS_EQ_EMPTY = prove
 (`!s t. s CROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN
  MESON_TAC[]);;

export_thm CROSS_EQ_EMPTY;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_FUNSPACE = prove
 (`!d n t:B->bool m s:A->bool.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; EXP] THEN
    CONV_TAC HAS_SIZE_CONV THEN EXISTS_TAC `(\x. d):A->B` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN REWRITE_TAC[FUN_EQ_THM];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM; LEFT_AND_EXISTS_THM]] THEN
  MAP_EVERY X_GEN_TAC [`s0:A->bool`; `a:A`; `s:A->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `s:A->bool`) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\
              (!x. ~(x IN a INSERT s) ==> (f x = d))} =
    IMAGE (\(b,g) x. if x = a then b else g(x))
          {b,g | b IN t /\
                 g IN {f | (!x. x IN s ==> f x IN t) /\
                           (!x. ~(x IN s) ==> (f x = d))}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM;
                EXISTS_PAIR_THM] THEN
    REWRITE_TAC[PAIR_EQ; CONJ_ASSOC; ONCE_REWRITE_RULE[CONJ_SYM]
     UNWIND_THM1] THEN
    X_GEN_TAC `f:A->B` THEN REWRITE_TAC[IN_INSERT] THEN EQ_TAC THENL
     [STRIP_TAC THEN MAP_EVERY EXISTS_TAC
       [`(f:A->B) a`; `\x. if x IN s then (f:A->B) x else d`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `b:B` (X_CHOOSE_THEN `g:A->B`
        STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_SIMP_TAC[EXP; HAS_SIZE_PRODUCT] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM; PAIR_EQ; CONJ_ASSOC] THEN
  REWRITE_TAC[ONCE_REWRITE_RULE[CONJ_SYM] UNWIND_THM1] THEN
  CONV_TAC(ONCE_DEPTH_CONV GEN_BETA_CONV) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:A`) THEN REWRITE_TAC[];
    X_GEN_TAC `x:A` THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
    ASM_MESON_TAC[]]);;

export_thm HAS_SIZE_FUNSPACE;;

let CARD_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> (f x = d))} =
              (CARD t) EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

export_thm CARD_FUNSPACE;;

let FINITE_FUNSPACE = prove
 (`!s t. FINITE s /\ FINITE t
         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\
                         (!x. ~(x IN s) ==> (f x = d))}`,
  MESON_TAC[HAS_SIZE_FUNSPACE; HAS_SIZE]);;

export_thm FINITE_FUNSPACE;;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_POWERSET = prove
 (`!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN
   `{f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}
    HAS_SIZE (2 EXP n)`
  MP_TAC THENL
   [MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`T`; `F`] THEN
    REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
    ACCEPT_TAC EXCLUDED_MIDDLE;
    REWRITE_TAC [IN_UNIV; CONTRAPOS_THM] THEN
    MATCH_MP_TAC (TAUT `!X Y. (X <=> Y) ==> Y ==> X`) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC
      `IMAGE (\f. {(x:A) | f x}) {f | (!x:A. f x ==> x IN s)}
         HAS_SIZE (2 EXP n)` THEN
    CONJ_TAC THENL
    [AP_THM_TAC THEN
     AP_TERM_TAC THEN
     REWRITE_TAC [EXTENSION; IN_ELIM_THM; SUBSET; IN_IMAGE] THEN
     GEN_TAC THEN
     EQ_TAC THENL
     [STRIP_TAC THEN
      EXISTS_TAC `\y. (y:A) IN x` THEN
      ASM_REWRITE_TAC [] THEN
      REWRITE_TAC [EXTENSION; IN_ELIM_THM];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM (SPEC `x'':A` th)]) THEN
      FIRST_ASSUM ACCEPT_TAC];
     MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
     REPEAT STRIP_TAC THEN
     REWRITE_TAC [FUN_EQ_THM] THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [IN_ELIM_THM; EXTENSION]]]);;

export_thm HAS_SIZE_POWERSET;;

let CARD_POWERSET = prove
 (`!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

export_thm CARD_POWERSET;;

let FINITE_POWERSET = prove
 (`!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}`,
  MESON_TAC[HAS_SIZE_POWERSET; HAS_SIZE]);;

export_thm FINITE_POWERSET;;

let FINITE_UNIONS = prove
 (`!s:(A->bool)->bool.
        FINITE(UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`,
  GEN_TAC THEN ASM_CASES_TAC `FINITE(s:(A->bool)->bool)` THEN
  ASM_SIMP_TAC[FINITE_FINITE_UNIONS] THEN
  DISCH_THEN(MP_TAC o MATCH_MP FINITE_POWERSET) THEN
  POP_ASSUM MP_TAC THEN REWRITE_TAC[CONTRAPOS_THM] THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET) THEN SET_TAC[]);;

export_thm FINITE_UNIONS;;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_NUMSEG_LT = prove
 (`!n. {m | m < n} HAS_SIZE n`,
  INDUCT_TAC THENL
   [SUBGOAL_THEN `{m | m < 0} = {}`
       (fun th -> REWRITE_TAC[HAS_SIZE_0; th]) THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; LT];
    SUBGOAL_THEN `{m | m < SUC n} = n INSERT {m | m < n}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN ARITH_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[HAS_SIZE]) THEN
    ASM_SIMP_TAC[HAS_SIZE; CARD_CLAUSES; FINITE_INSERT] THEN
    REWRITE_TAC[IN_ELIM_THM; LT_REFL]]);;

export_thm HAS_SIZE_NUMSEG_LT;;

let CARD_NUMSEG_LT = prove
 (`!n. CARD {m | m < n} = n`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

export_thm CARD_NUMSEG_LT;;

let FINITE_NUMSEG_LT = prove
 (`!n:num. FINITE {m | m < n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

export_thm FINITE_NUMSEG_LT;;

let HAS_SIZE_NUMSEG_LE = prove
 (`!n. {m | m <= n} HAS_SIZE (n + 1)`,
  REWRITE_TAC[GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]);;

export_thm HAS_SIZE_NUMSEG_LE;;

let FINITE_NUMSEG_LE = prove
 (`!n. FINITE {m | m <= n}`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

export_thm FINITE_NUMSEG_LE;;

let CARD_NUMSEG_LE = prove
 (`!n. CARD {m | m <= n} = n + 1`,
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

export_thm CARD_NUMSEG_LE;;

let num_FINITE = prove
 (`!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a`,
  GEN_TAC THEN EQ_TAC THENL
   [SPEC_TAC(`s:num->bool`,`s:num->bool`) THEN
    MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[LE_CASES; LE_TRANS];
    DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:num | m <= n}` THEN REWRITE_TAC[FINITE_NUMSEG_LE] THEN
    ASM_SIMP_TAC[SUBSET; IN_ELIM_THM]]);;

export_thm num_FINITE;;

let num_FINITE_AVOID = prove
 (`!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)`,
  MESON_TAC[num_FINITE; LT; NOT_LT]);;

export_thm num_FINITE_AVOID;;

let num_INFINITE = prove
 (`INFINITE(:num)`,
  REWRITE_TAC[INFINITE] THEN MESON_TAC[num_FINITE_AVOID; IN_UNIV]);;

export_thm num_INFINITE;;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = prove
 (`INFINITE(:string)`,
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[LENGTH_REPLICATE]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let FINITE_REAL_INTERVAL = prove
 (`(!a. ~FINITE {x:real | a < x}) /\
   (!a. ~FINITE {x:real | a <= x}) /\
   (!b. ~FINITE {x:real | x < b}) /\
   (!b. ~FINITE {x:real | x <= b}) /\
   (!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x < b} <=> b <= a) /\
   (!a b. FINITE {x:real | a < x /\ x <= b} <=> b <= a) /\
   (!a b. FINITE {x:real | a <= x /\ x <= b} <=> b <= a)`,
  SUBGOAL_THEN `!a b. FINITE {x:real | a < x /\ x < b} <=> b <= a`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN
    ASM_CASES_TAC `a:real < b` THEN
    ASM_SIMP_TAC[REAL_ARITH `~(a:real < b) ==> ~(a < x /\ x < b)`] THEN
    REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (\n. a + (b - a) / (&n + &2)) (:num)`) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    SIMP_TAC[REAL_LT_ADDR; REAL_ARITH `a + x / y < b <=> x / y < b - a`] THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_SUB_LT; REAL_LT_LDIV_EQ; NOT_IMP;
                 REAL_ARITH `&0:real < &n + &2`] THEN
    REWRITE_TAC[REAL_ARITH `x:real < x * (n + &2) <=> &0 < x * (n + &1)`] THEN
    ASM_SIMP_TAC[REAL_SUB_LT; REAL_LT_MUL; REAL_ARITH `&0:real < &n + &1`] THEN
    MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_SIMP_TAC[REAL_OF_NUM_EQ; REAL_FIELD
     `a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>
                 &n:real = &m)`];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | a < x /\ x < a + &1}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `{x:real | b - &1 < x /\ x < b}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ARITH
     `a:real <= x /\ x < b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a`];
    REWRITE_TAC[REAL_ARITH
     `a:real < x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = b`];
    ASM_CASES_TAC `b:real = a` THEN
    ASM_SIMP_TAC[REAL_LE_ANTISYM; REAL_LE_REFL; SING_GSPEC; FINITE_SING] THEN
    ASM_SIMP_TAC[REAL_ARITH
     `~(b:real = a) ==>
        (a <= x /\ x <= b <=> (a < x /\ x < b) \/ ~(b <= a) /\ x = a \/
        ~(b <= a) /\ x = b)`]] THEN
  ASM_REWRITE_TAC[FINITE_UNION; SET_RULE
   `{x | p x \/ q x} = {x | p x} UNION {x | q x}`] THEN
  ASM_CASES_TAC `b:real <= a` THEN
  ASM_REWRITE_TAC[EMPTY_GSPEC; FINITE_EMPTY]);;

let real_INFINITE = prove
 (`INFINITE(:real)`,
  REWRITE_TAC[INFINITE] THEN
  DISCH_THEN(MP_TAC o SPEC `{x:real | &0 <= x}` o
        MATCH_MP(REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
  REWRITE_TAC[FINITE_REAL_INTERVAL; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets.                                                  *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INDEX = prove
 (`!s n. s HAS_SIZE n
         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\
                        (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN INDUCT_TAC THEN
  SIMP_TAC[HAS_SIZE_0; HAS_SIZE_SUC; LT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `s:A->bool` THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (MP_TAC o SPEC `a:A`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s DELETE (a:A)`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\m:num. if m < n then f(m) else a:A` THEN CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  CONV_TAC(ONCE_DEPTH_CONV COND_ELIM_CONV) THEN
  ASM_CASES_TAC `a:A = x` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[LT_REFL; IN_DELETE]);;

export_thm HAS_SIZE_INDEX;;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "set-list-def";;

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

export_thm set_of_list;;

let list_of_set = new_definition
  `list_of_set s = @l. (set_of_list l = s) /\ (LENGTH l = CARD s)`;;

let LIST_OF_SET_PROPERTIES = prove
 (`!s:A->bool. FINITE(s)
               ==> (set_of_list(list_of_set s) = s) /\
                   (LENGTH(list_of_set s) = CARD s)`,
  REWRITE_TAC[list_of_set] THEN
  CONV_TAC(BINDER_CONV(RAND_CONV SELECT_CONV)) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `[]:A list` THEN REWRITE_TAC[CARD_CLAUSES; LENGTH; set_of_list];
    EXISTS_TAC `CONS (x:A) l` THEN ASM_REWRITE_TAC[LENGTH] THEN
    ASM_REWRITE_TAC[set_of_list] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC
     [MATCH_MP (CONJUNCT2 CARD_CLAUSES) th]) THEN
    ASM_REWRITE_TAC[]]);;

export_thm LIST_OF_SET_PROPERTIES;;

logfile "set-list-thm";;

let SET_OF_LIST_OF_SET = prove
 (`!s. FINITE(s) ==> (set_of_list(list_of_set s) = s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

export_thm SET_OF_LIST_OF_SET;;

let LENGTH_LIST_OF_SET = prove
 (`!s. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)`,
  MESON_TAC[LIST_OF_SET_PROPERTIES]);;

export_thm LENGTH_LIST_OF_SET;;

let MEM_LIST_OF_SET = prove
 (`!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV)
    [GSYM th]) THEN
  SPEC_TAC(`list_of_set(s:A->bool)`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; set_of_list; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

export_thm MEM_LIST_OF_SET;;

let FINITE_SET_OF_LIST = prove
 (`!l. FINITE(set_of_list l)`,
  LIST_INDUCT_TAC THEN ASM_SIMP_TAC[set_of_list; FINITE_RULES]);;

export_thm FINITE_SET_OF_LIST;;

let IN_SET_OF_LIST = prove
 (`!x l. x IN (set_of_list l) <=> MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MEM; set_of_list] THEN
  ASM_MESON_TAC[]);;

export_thm IN_SET_OF_LIST;;

let SET_OF_LIST_APPEND = prove
 (`!l1 l2. set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)`,
  REWRITE_TAC[EXTENSION; IN_SET_OF_LIST; IN_UNION; MEM_APPEND]);;

export_thm SET_OF_LIST_APPEND;;

let SET_OF_LIST_MAP = prove
 (`!f l. set_of_list(MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[set_of_list; MAP; IMAGE_CLAUSES]);;

export_thm SET_OF_LIST_MAP;;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!l. set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC[set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]);;

export_thm SET_OF_LIST_EQ_EMPTY;;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n & fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = `(INSERT):A->(A->bool)->(A->bool)`
  and nil_atm = `(EMPTY):A->bool` in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let pairwise = new_definition
  `pairwise r s <=> !x y. x IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

let PAIRWISE = new_recursive_definition list_RECURSION
  `(PAIRWISE (r:A->A->bool) [] <=> T) /\
   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\ PAIRWISE r t)`;;

let PAIRWISE_EMPTY = prove
 (`!r. pairwise r {} <=> T`,
  REWRITE_TAC[pairwise; NOT_IN_EMPTY] THEN MESON_TAC[]);;

let PAIRWISE_SING = prove
 (`!r x. pairwise r {x} <=> T`,
  REWRITE_TAC[pairwise; IN_SING] THEN MESON_TAC[]);;

let PAIRWISE_MONO = prove
 (`!r s t. pairwise r s /\ t SUBSET s ==> pairwise r t`,
  REWRITE_TAC[pairwise] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let CARD_SET_OF_LIST_LE = prove
 (`!l. CARD(set_of_list l) <= LENGTH l`,
  LIST_INDUCT_TAC THEN
  SIMP_TAC[LENGTH; set_of_list; CARD_CLAUSES; FINITE_SET_OF_LIST] THEN
  ASM_ARITH_TAC);;

export_thm CARD_SET_OF_LIST_LE;;

let HAS_SIZE_SET_OF_LIST = prove
 (`!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y. ~(x = y)) l`,
  REWRITE_TAC[HAS_SIZE; FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LENGTH; set_of_list; PAIRWISE; ALL;
               FINITE_SET_OF_LIST; GSYM ALL_MEM; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[CARD_SET_OF_LIST_LE; ARITH_RULE `~(SUC n <= n)`]);;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-thm";;

let SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_CASES_TAC `x:A = y` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CARD_SUBSET THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE] THEN
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_DELETE] THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_LE] THEN MATCH_MP_TAC LET_TRANS THEN
      EXISTS_TAC `CARD(s DELETE (y:A))` THEN
      ASM_SIMP_TAC[CARD_IMAGE_LE; FINITE_DELETE] THEN
      ASM_SIMP_TAC[CARD_DELETE; ARITH_RULE `x - 1 < x <=> ~(x = 0)`] THEN
      ASM_MESON_TAC[CARD_EQ_0; MEMBER_NOT_EMPTY]];
    SUBGOAL_THEN `IMAGE (f:A->B) s = t` MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[EXTENSION; IN_IMAGE]] THEN
    ASM_MESON_TAC[CARD_SUBSET_EQ; CARD_IMAGE_INJ]]);;

export_thm SURJECTIVE_IFF_INJECTIVE_GEN;;

let SURJECTIVE_IFF_INJECTIVE = prove
 (`!s f:A->A.
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN]);;

export_thm SURJECTIVE_IFF_INJECTIVE;;

let IMAGE_IMP_INJECTIVE_GEN = prove
 (`!s t f:A->B.
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`s:A->bool`; `t:B->bool`; `f:A->B`]
                SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[SUBSET_REFL; FINITE_IMAGE] THEN
  ASM_MESON_TAC[EXTENSION; IN_IMAGE]);;

export_thm IMAGE_IMP_INJECTIVE_GEN;;

let IMAGE_IMP_INJECTIVE = prove
 (`!s f. FINITE s /\ (IMAGE f s = s)
       ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MESON_TAC[IMAGE_IMP_INJECTIVE_GEN]);;

export_thm IMAGE_IMP_INJECTIVE;;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?f:A->B. (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN STRIP_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[CARD_CLAUSES; LE; NOT_SUC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:B->bool`] THEN
  SIMP_TAC[CARD_CLAUSES] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[LE_SUC] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `t:B->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:A. if z = x then (y:B) else f(z)` THEN
  REWRITE_TAC[IN_INSERT; SUBSET; IN_IMAGE] THEN
  ASM_MESON_TAC[SUBSET; IN_IMAGE]);;

export_thm CARD_LE_INJ;;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let FORALL_IN_CLAUSES = prove
 (`(!P. (!x. x IN {} ==> P x) <=> T) /\
   (!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\ (!x. x IN s ==> P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_thm FORALL_IN_CLAUSES;;

let EXISTS_IN_CLAUSES = prove
 (`(!P. (?x. x IN {} /\ P x) <=> F) /\
   (!P a s. (?x. x IN (a INSERT s) /\ P x) <=> P a \/ (?x. x IN s /\ P x))`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

export_thm EXISTS_IN_CLAUSES;;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

logfile "function-thm";;

let SURJECTIVE_ON_RIGHT_INVERSE = prove
 (`!f t. (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
         (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`,
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

export_thm SURJECTIVE_ON_RIGHT_INVERSE;;

let INJECTIVE_ON_LEFT_INVERSE = prove
 (`!f s. (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
         (?g. !x. x IN s ==> (g(f(x)) = x))`,
  let lemma = MESON[]
   `(!x. x IN s ==> (g(f(x)) = x)) <=>
    (!y x. x IN s /\ (y = f x) ==> (g y = x))` in
  REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_thm INJECTIVE_ON_LEFT_INVERSE;;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove
 (`!f s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  EQ_TAC THEN ASM_MESON_TAC[]);;

export_thm BIJECTIVE_ON_LEFT_RIGHT_INVERSE;;

let SURJECTIVE_RIGHT_INVERSE = prove
 (`(!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`,
  MESON_TAC[SURJECTIVE_ON_RIGHT_INVERSE; IN_UNIV]);;

export_thm SURJECTIVE_RIGHT_INVERSE;;

let INJECTIVE_LEFT_INVERSE = prove
 (`(!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)`,
  let th = REWRITE_RULE[IN_UNIV]
   (ISPECL [`f:A->B`; `UNIV:A->bool`] INJECTIVE_ON_LEFT_INVERSE) in
  REWRITE_TAC[th]);;

export_thm INJECTIVE_LEFT_INVERSE;;

let BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!f:A->B.
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC[IN_UNIV]);;

export_thm BIJECTIVE_LEFT_RIGHT_INVERSE;;

let FUNCTION_FACTORS_RIGHT = prove
 (`!f g. (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_thm FUNCTION_FACTORS_RIGHT;;

let FUNCTION_FACTORS_LEFT = prove
 (`!f g. (!x y. (g x = g y) ==> (f x = f y)) <=> ?h. f = h o g`,
  let lemma = prove
   (`(f = h o g) <=> !y x. (y = g x) ==> (h y = f x)`,
    REWRITE_TAC[FUN_EQ_THM; o_THM] THEN MESON_TAC[]) in
  REWRITE_TAC[lemma; GSYM SKOLEM_THM] THEN MESON_TAC[]);;

export_thm FUNCTION_FACTORS_LEFT;;

let SURJECTIVE_FORALL_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[GSYM th]) THEN MESON_TAC[]);;

export_thm SURJECTIVE_FORALL_THM;;

let SURJECTIVE_EXISTS_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`,
  GEN_TAC THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:B. !x:A. ~(f x = y)`) THEN MESON_TAC[]);;

export_thm SURJECTIVE_EXISTS_THM;;

logfile "set-thm";;

let SURJECTIVE_IMAGE_THM = prove
 (`!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  EQ_TAC THENL [ALL_TAC; DISCH_THEN(MP_TAC o SPEC `\y:B. T`)] THEN
  MESON_TAC[]);;

export_thm SURJECTIVE_IMAGE_THM;;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image under a function.                   *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_IMAGE = prove
 (`!f:A->B u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [DISCH_TAC; SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`{x:A}`; `{y:A}`]) THEN
  ASM_REWRITE_TAC[SING_SUBSET; IMAGE_CLAUSES] THEN SET_TAC[]);;

export_thm INJECTIVE_ON_IMAGE;;

let INJECTIVE_IMAGE = prove
 (`!f:A->B.
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN MP_TAC(ISPECL [`f:A->B`; `(:A)`] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_thm INJECTIVE_IMAGE;;

let SURJECTIVE_ON_IMAGE = prove
 (`!f:A->B u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{y:B}`) THEN ASM SET_TAC[];
    DISCH_TAC THEN X_GEN_TAC `t:B->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{x | x IN u /\ (f:A->B) x IN t}` THEN ASM SET_TAC[]]);;

export_thm SURJECTIVE_ON_IMAGE;;

let SURJECTIVE_IMAGE = prove
 (`!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  MP_TAC(ISPECL [`f:A->B`; `(:A)`; `(:B)`] SURJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_thm SURJECTIVE_IMAGE;;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-thm";;

let CARD_EQ_BIJECTION = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MP_TAC CARD_LE_INJ THEN REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  MESON_TAC[SUBSET; IN_IMAGE]);;

export_thm CARD_EQ_BIJECTION;;

let CARD_EQ_BIJECTIONS = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f(g y) = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SURJECTIVE_ON_RIGHT_INVERSE] THEN
  GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN MESON_TAC[]);;

export_thm CARD_EQ_BIJECTIONS;;

let BIJECTIONS_HAS_SIZE = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_ALL_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN ASM_MESON_TAC[]]);;

export_thm BIJECTIONS_HAS_SIZE;;

let BIJECTIONS_HAS_SIZE_EQ = prove
 (`!s t f:A->B g.
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  MATCH_MP_TAC(ONCE_REWRITE_RULE
  [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`] BIJECTIONS_HAS_SIZE) THENL
   [MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`];
    MAP_EVERY EXISTS_TAC [`g:B->A`; `f:A->B`]] THEN
  ASM_MESON_TAC[]);;

export_thm BIJECTIONS_HAS_SIZE_EQ;;

let BIJECTIONS_CARD_EQ = prove
 (`!s t f:A->B g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
  MESON_TAC[HAS_SIZE]);;

export_thm BIJECTIONS_CARD_EQ;;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let WF_FINITE = prove
 (`!(<<). (!x. ~(x << x)) /\ (!x y z. x << y /\ y << z ==> x << z) /\
          (!x:A. FINITE {y | y << x})
          ==> WF(<<)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[WF_DCHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> (s:num->A) n << s m` ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:num->A` INFINITE_IMAGE_INJ) THEN ANTS_TAC THENL
   [ASM_MESON_TAC[LT_CASES]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `(:num)`) THEN
  REWRITE_TAC[num_INFINITE] THEN REWRITE_TAC[INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s(0) INSERT {y:A | y << s(0)}` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_INSERT] THEN
  INDUCT_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[LT_0]);;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Examples/card.ml)                    *)
(* ------------------------------------------------------------------------- *)

let le_c = new_definition
  `s <=_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                    (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))`;;

let lt_c = new_definition
  `s <_c t <=> s <=_c t /\ ~(t <=_c s)`;;

let eq_c = new_definition
  `s =_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\
                   !y. y IN t ==> ?!x. x IN s /\ (f x = y)`;;

let ge_c = new_definition
 `s >=_c t <=> t <=_c s`;;

let gt_c = new_definition
 `s >_c t <=> t <_c s`;;

let LE_C = prove
 (`!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\ (g y = x)`,
  REWRITE_TAC[le_c; INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE;
              RIGHT_IMP_EXISTS_THM; SKOLEM_THM; RIGHT_AND_EXISTS_THM] THEN
  MESON_TAC[]);;

let GE_C = prove
 (`!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\ (y = f x)`,
  REWRITE_TAC[ge_c; LE_C] THEN MESON_TAC[]);;

let COUNTABLE = new_definition
  `COUNTABLE t <=> (:num) >=_c t`;;

logfile_end ();;

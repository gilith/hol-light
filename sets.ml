(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "calc_num.ml";;

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
  `!p x. (x : A) IN p <=> dest_set p x`;;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let IN_ELIM_THM = prove
 (`!p (x:A). x IN GSPEC p <=> p x`,
  REWRITE_TAC[IN_DEF; set_tybij]);;

export_thm IN_ELIM_THM;;

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
  `!s t.
     INJ s t =
     { (f:A->B) |
       (!x. x IN s ==> (f x) IN t) /\
       (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) }`;;

export_thm INJ;;

let SURJ = new_definition
  `!s t.
     SURJ s t =
     { (f:A->B) |
       (!x. x IN s ==> (f x) IN t) /\
       (!x. (x IN t) ==> ?y. y IN s /\ (f y = x)) }`;;

export_thm SURJ;;

let BIJ = new_definition
  `!(s : A set) (t : B set). BIJ s t = (INJ s t) INTER (SURJ s t)`;;

export_thm BIJ;;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let CHOICE_DEF = new_definition
  `!s. CHOICE s = @x:A. x IN s`;;

let CHOICE = prove
 (`!s : A set. ~(s = EMPTY) ==> (CHOICE s) IN s`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC [CHOICE_DEF] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC EXTENSION_IMP THEN
  REWRITE_TAC [EMPTY; IN_ELIM_THM] THEN
  REWRITE_TAC [GSYM NOT_EXISTS_THM; EXISTS_THM] THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm CHOICE;;

let REST = new_definition
  `!s. REST (s : A set) = s DELETE (CHOICE s)`;;

export_thm REST;;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let EXTENSION' = prove
 (`!s t. (!x:A. x IN s <=> x IN t) <=> s = t`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC EXTENSION_IMP;
   DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm EXTENSION';;

let EXTENSION = prove
 (`!s t. (s = t) <=> !x:A. x IN s <=> x IN t`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  ACCEPT_TAC EXTENSION');;

let IN_ELIM = prove
 (`!p (x:A). x IN GSPEC (\v. ?y. v = y /\ p y) <=> p x`,
  REWRITE_TAC[IN_ELIM_THM] THEN
  ACCEPT_TAC UNWIND_THM1);;

export_thm IN_ELIM;;

let NOT_IN_EMPTY = prove
 (`!x:A. ~(x IN EMPTY)`,
  PURE_REWRITE_TAC[IN_ELIM; EMPTY] THEN
  REWRITE_TAC []);;

export_thm NOT_IN_EMPTY;;

let IN_UNIV = prove
 (`!x:A. x IN UNIV`,
  PURE_REWRITE_TAC[IN_ELIM; UNIV] THEN
  REWRITE_TAC []);;

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
 (`!p a s. (!x. (x:A) IN (a INSERT s) ==> p x) <=> p a /\ (!x. x IN s ==> p x)`,
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
 (`!p a s. (?x. (x:A) IN (a INSERT s) /\ p x) <=> p a \/ ?x. x IN s /\ p x`,
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

let PSUBSET_NOT_SUBSET = prove
 (`!(s : A set) t. s PSUBSET t <=> s SUBSET t /\ ~(t SUBSET s)`,
  REWRITE_TAC [PSUBSET; GSYM SUBSET_ANTISYM_EQ] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   UNDISCH_TAC `~(s SUBSET (t : A set) /\ t SUBSET s)` THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm PSUBSET_NOT_SUBSET;;

let PSUBSET_TRANS = prove
 (`!(s : A set) t u. s PSUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV [PSUBSET])) THEN
  REWRITE_TAC [PSUBSET_NOT_SUBSET] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `s SUBSET (t : A set)` THEN
   ASM_REWRITE_TAC []]);;

export_thm PSUBSET_TRANS;;

let PSUBSET_SUBSET_TRANS = prove
 (`!(s : A set) t u. s PSUBSET t /\ t SUBSET u ==> s PSUBSET u`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV [PSUBSET])) THEN
  REWRITE_TAC [PSUBSET_NOT_SUBSET] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `~(t SUBSET (s : A set))` THEN
   ASM_REWRITE_TAC []]);;

export_thm PSUBSET_SUBSET_TRANS;;

let SUBSET_PSUBSET_TRANS = prove
 (`!(s : A set) t u. s SUBSET t /\ t PSUBSET u ==> s PSUBSET u`,
  REPEAT GEN_TAC THEN
  CONV_TAC (RAND_CONV (REWRITE_CONV [PSUBSET])) THEN
  REWRITE_TAC [PSUBSET_NOT_SUBSET] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `s SUBSET (t : A set)` THEN
   ASM_REWRITE_TAC []]);;

export_thm SUBSET_PSUBSET_TRANS;;

let PSUBSET_IRREFL = prove
 (`!s : A set. ~(s PSUBSET s)`,
  REWRITE_TAC [PSUBSET]);;

export_thm PSUBSET_IRREFL;;

let NOT_PSUBSET_EMPTY = prove
 (`!s : A set. ~(s PSUBSET EMPTY)`,
  REWRITE_TAC [PSUBSET_NOT_SUBSET; EMPTY_SUBSET]);;

export_thm NOT_PSUBSET_EMPTY;;

let NOT_UNIV_PSUBSET = prove
 (`!s : A set. ~(UNIV PSUBSET s)`,
  REWRITE_TAC [PSUBSET_NOT_SUBSET; SUBSET_UNIV]);;

export_thm NOT_UNIV_PSUBSET;;

let PSUBSET_UNIV = prove
 (`!s : A set. s PSUBSET UNIV <=> ?x. ~(x IN s)`,
  REWRITE_TAC [PSUBSET; GSYM EQ_UNIV; SUBSET_UNIV; NOT_FORALL_THM]);;

export_thm PSUBSET_UNIV;;

let PSUBSET_ALT = prove
 (`!s t : A set. s PSUBSET t <=> s SUBSET t /\ (?a. a IN t /\ ~(a IN s))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PSUBSET_NOT_SUBSET] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [SUBSET; NOT_FORALL_THM; NOT_IMP]);;

export_thm PSUBSET_ALT;;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let UNION_ASSOC = prove
 (`!(s : A set) t u. (s UNION t) UNION u = s UNION (t UNION u)`,
  REWRITE_TAC [EXTENSION; IN_UNION; DISJ_ASSOC]);;

export_thm UNION_ASSOC;;

let UNION_IDEMPOT = prove
 (`!s : A set. s UNION s = s`,
  REWRITE_TAC [EXTENSION; IN_UNION]);;

export_thm UNION_IDEMPOT;;

let UNION_COMM = prove
 (`!(s : A set) t. s UNION t = t UNION s`,
  REWRITE_TAC [EXTENSION; IN_UNION] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC DISJ_SYM);;

export_thm UNION_COMM;;

let SUBSET_LEFT_UNION = prove
 (`!s : A set. !t. s SUBSET (s UNION t)`,
  REWRITE_TAC [SUBSET; IN_UNION] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm SUBSET_LEFT_UNION;;

let SUBSET_RIGHT_UNION = prove
 (`!s : A set. !t. s SUBSET (t UNION s)`,
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  ACCEPT_TAC SUBSET_LEFT_UNION);;

export_thm SUBSET_RIGHT_UNION;;

let SUBSET_UNION = CONJ SUBSET_LEFT_UNION SUBSET_RIGHT_UNION;;

let SUBSET_UNION_ABSORPTION = prove
 (`!s : A set. !t. s SUBSET t <=> (s UNION t = t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; EXTENSION; IN_UNION] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC THEN
    DISJ2_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC []]);;

export_thm SUBSET_UNION_ABSORPTION;;

let UNION_LEFT_EMPTY = prove
 (`!s : A set. EMPTY UNION s = s`,
  REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_UNION]);;

export_thm UNION_LEFT_EMPTY;;

let UNION_RIGHT_EMPTY = prove
 (`!s : A set. s UNION EMPTY = s`,
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  ACCEPT_TAC UNION_LEFT_EMPTY);;

export_thm UNION_RIGHT_EMPTY;;

let UNION_EMPTY = CONJ UNION_LEFT_EMPTY UNION_RIGHT_EMPTY;;

let UNION_LEFT_UNIV = prove
 (`!s : A set. UNIV UNION s = UNIV`,
  REWRITE_TAC [EXTENSION; IN_UNIV; IN_UNION]);;

export_thm UNION_LEFT_UNIV;;

let UNION_RIGHT_UNIV = prove
 (`!s : A set. s UNION UNIV = UNIV`,
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  ACCEPT_TAC UNION_LEFT_UNIV);;

export_thm UNION_RIGHT_UNIV;;

let UNION_UNIV = CONJ UNION_LEFT_UNIV UNION_RIGHT_UNIV;;

let EMPTY_UNION = prove
 (`!s : A set. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\ (t = EMPTY)`,
  REWRITE_TAC
    [EXTENSION; IN_UNION; NOT_IN_EMPTY; DE_MORGAN_THM; FORALL_AND_THM]);;

export_thm EMPTY_UNION;;

let UNION_SUBSET = prove
 (`!(s : A set) t u. (s UNION t) SUBSET u <=> s SUBSET u /\ t SUBSET u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_UNION] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THENL
   [UNDISCH_THEN `!x. (x:A) IN s ==> x IN u` MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_THEN `!x. (x:A) IN t ==> x IN u` MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm UNION_SUBSET;;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let INTER_ASSOC = prove
 (`!(s : A set) t u. (s INTER t) INTER u = s INTER (t INTER u)`,
  REWRITE_TAC [EXTENSION; IN_INTER; CONJ_ASSOC]);;

export_thm INTER_ASSOC;;

let INTER_IDEMPOT = prove
 (`!s : A set. s INTER s = s`,
  REWRITE_TAC [EXTENSION; IN_INTER]);;

export_thm INTER_IDEMPOT;;

let INTER_COMM = prove
 (`!(s : A set) t. s INTER t = t INTER s`,
  REWRITE_TAC [EXTENSION; IN_INTER] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC CONJ_SYM);;

export_thm INTER_COMM;;

let LEFT_INTER_SUBSET = prove
 (`!s : A set. !t. (s INTER t) SUBSET s`,
  REWRITE_TAC [SUBSET; IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm LEFT_INTER_SUBSET;;

let RIGHT_INTER_SUBSET = prove
 (`!s : A set. !t. (t INTER s) SUBSET s`,
  ONCE_REWRITE_TAC [INTER_COMM] THEN
  ACCEPT_TAC LEFT_INTER_SUBSET);;

export_thm RIGHT_INTER_SUBSET;;

let INTER_SUBSET = CONJ LEFT_INTER_SUBSET RIGHT_INTER_SUBSET;;

let SUBSET_INTER_ABSORPTION = prove
 (`!s : A set. !t. s SUBSET t <=> (s INTER t = s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; EXTENSION; IN_INTER] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC []]);;

export_thm SUBSET_INTER_ABSORPTION;;

let INTER_LEFT_EMPTY = prove
 (`!s : A set. EMPTY INTER s = EMPTY`,
  REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_INTER]);;

export_thm INTER_LEFT_EMPTY;;

let INTER_RIGHT_EMPTY = prove
 (`!s : A set. s INTER EMPTY = EMPTY`,
  ONCE_REWRITE_TAC [INTER_COMM] THEN
  ACCEPT_TAC INTER_LEFT_EMPTY);;

export_thm INTER_RIGHT_EMPTY;;

let INTER_EMPTY = CONJ INTER_LEFT_EMPTY INTER_RIGHT_EMPTY;;

let INTER_LEFT_UNIV = prove
 (`!s : A set. UNIV INTER s = s`,
  REWRITE_TAC [EXTENSION; IN_UNIV; IN_INTER]);;

export_thm INTER_LEFT_UNIV;;

let INTER_RIGHT_UNIV = prove
 (`!s : A set. s INTER UNIV = s`,
  ONCE_REWRITE_TAC [INTER_COMM] THEN
  ACCEPT_TAC INTER_LEFT_UNIV);;

export_thm INTER_RIGHT_UNIV;;

let INTER_UNIV = CONJ INTER_LEFT_UNIV INTER_RIGHT_UNIV;;

let SUBSET_INTER = prove
 (`!(s : A set) t u. s SUBSET (t INTER u) <=> s SUBSET t /\ s SUBSET u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTER] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUBSET_INTER;;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let LEFT_UNION_DISTRIB = prove
 (`!s : A set. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)`,
  REWRITE_TAC [EXTENSION; IN_INTER; IN_UNION] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC LEFT_OR_DISTRIB);;

export_thm LEFT_UNION_DISTRIB;;

let RIGHT_UNION_DISTRIB = prove
 (`!s : A set. !t u. (s UNION t) INTER u = (s INTER u) UNION (t INTER u)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [INTER_COMM] THEN
  MATCH_ACCEPT_TAC LEFT_UNION_DISTRIB);;

export_thm RIGHT_UNION_DISTRIB;;

let LEFT_INTER_DISTRIB = prove
 (`!s : A set. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)`,
  REWRITE_TAC [EXTENSION; IN_INTER; IN_UNION] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC LEFT_AND_DISTRIB);;

export_thm LEFT_INTER_DISTRIB;;

let RIGHT_INTER_DISTRIB = prove
 (`!s : A set. !t u. (s INTER t) UNION u = (s UNION u) INTER (t UNION u)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  MATCH_ACCEPT_TAC LEFT_INTER_DISTRIB);;

export_thm RIGHT_INTER_DISTRIB;;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let IN_DISJOINT = prove
 (`!s : A set. !t. DISJOINT s t <=> ~(?x. x IN s /\ x IN t)`,
  REWRITE_TAC [DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; NOT_EXISTS_THM]);;

export_thm IN_DISJOINT;;

let DISJOINT_SYM = prove
 (`!s : A set. !t. DISJOINT s t <=> DISJOINT t s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DISJOINT] THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [INTER_COMM])) THEN
  REFL_TAC);;

export_thm DISJOINT_SYM;;

let EMPTY_DISJOINT = prove
 (`!s : A set. DISJOINT EMPTY s`,
  REWRITE_TAC [DISJOINT; INTER_EMPTY]);;

export_thm EMPTY_DISJOINT;;

let DISJOINT_EMPTY = prove
 (`!s : A set. DISJOINT s EMPTY`,
  ONCE_REWRITE_TAC [DISJOINT_SYM] THEN
  ACCEPT_TAC EMPTY_DISJOINT);;

export_thm DISJOINT_EMPTY;;

let DISJOINT_EMPTY_REFL = prove
 (`!s : A set. DISJOINT s s <=> s = EMPTY`,
  REWRITE_TAC [DISJOINT; INTER_IDEMPOT]);;

export_thm DISJOINT_EMPTY_REFL;;

let DISJOINT_UNION = prove
 (`!s : A set. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\ DISJOINT t u`,
  REWRITE_TAC [DISJOINT; RIGHT_UNION_DISTRIB; EMPTY_UNION]);;

export_thm DISJOINT_UNION;;

let SING_DISJOINT = prove
 (`!(x : A) s. DISJOINT (x INSERT EMPTY) s <=> ~(x IN s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SING] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `(x' : A) IN s` THEN
   ASM_REWRITE_TAC []]);;

export_thm SING_DISJOINT;;

let DISJOINT_SING = prove
 (`!(x : A) s. DISJOINT s (x INSERT EMPTY) <=> ~(x IN s)`,
  ONCE_REWRITE_TAC [DISJOINT_SYM] THEN
  ACCEPT_TAC SING_DISJOINT);;

export_thm DISJOINT_SING;;

let DISJOINT_UNIONS = prove
 (`!(s : A set) t. DISJOINT s (UNIONS t) <=> !x. x IN t ==> DISJOINT s x`,
  REWRITE_TAC [DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_UNIONS] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x:A set` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM (MP_TAC o SPEC `t':A set`) THEN
   ASM_REWRITE_TAC [NOT_FORALL_THM] THEN
   EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC []]);;

export_thm DISJOINT_UNIONS;;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let DIFF_EMPTY = prove
 (`!s : A set. s DIFF EMPTY = s`,
  REWRITE_TAC [EXTENSION; IN_DIFF; NOT_IN_EMPTY]);;

export_thm DIFF_EMPTY;;

let EMPTY_DIFF = prove
 (`!s : A set. EMPTY DIFF s = EMPTY`,
  REWRITE_TAC [EXTENSION; IN_DIFF; NOT_IN_EMPTY]);;

export_thm EMPTY_DIFF;;

let DIFF_UNIV = prove
 (`!s : A set. s DIFF UNIV = EMPTY`,
  REWRITE_TAC [EXTENSION; IN_DIFF; NOT_IN_EMPTY; IN_UNIV]);;

export_thm DIFF_UNIV;;

let DIFF_DIFF = prove
 (`!s : A set. !t. (s DIFF t) DIFF t = s DIFF t`,
  REWRITE_TAC [EXTENSION; IN_DIFF; GSYM CONJ_ASSOC]);;

export_thm DIFF_DIFF;;

let DIFF_EQ_EMPTY = prove
 (`!s : A set. s DIFF s = EMPTY`,
  REWRITE_TAC [EXTENSION; IN_DIFF; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [DISJ_SYM] THEN
  MATCH_ACCEPT_TAC EXCLUDED_MIDDLE);;

export_thm DIFF_EQ_EMPTY;;

let DIFF_SUBSET = prove
 (`!(s : A set) t. (s DIFF t) SUBSET s`,
  REWRITE_TAC [SUBSET; IN_DIFF] THEN
  REPEAT STRIP_TAC);;

export_thm DIFF_SUBSET;;

let DIFF_EMPTY_SUBSET = prove
 (`!s (t : A set). s DIFF t = {} <=> s SUBSET t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_DIFF; SUBSET; NOT_IN_EMPTY] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  BOOL_CASES_TAC `(x:A) IN s` THEN
  REWRITE_TAC []);;

export_thm DIFF_EMPTY_SUBSET;;

let UNION_DIFF_SUBSET = prove
 (`!s (t : A set). s UNION (t DIFF s) = t <=> s SUBSET t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_DIFF; SUBSET; IN_UNION] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  BOOL_CASES_TAC `(x:A) IN s` THEN
  REWRITE_TAC []);;

export_thm UNION_DIFF_SUBSET;;

let DIFF_UNION_SUBSET = prove
 (`!s (t : A set). (t DIFF s) UNION s = t <=> s SUBSET t`,
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  ACCEPT_TAC UNION_DIFF_SUBSET);;

export_thm DIFF_UNION_SUBSET;;

let SUBSET_DIFF = prove
 (`!(s : A set) t u. s SUBSET (t DIFF u) <=> s SUBSET t /\ DISJOINT s u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_DIFF; DISJOINT; IN_INTER; EXTENSION; NOT_IN_EMPTY] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC;
    FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_THEN `!x:A. ~(x IN s /\ x IN u)` (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC []]]);;

export_thm SUBSET_DIFF;;

let SUBSET_DIFF_UNION = prove
 (`!(s : A set) t u. s SUBSET (t UNION u) <=> ((s DIFF t) SUBSET u)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_DIFF; IN_UNION] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (TAUT `!x y. (~x ==> y) ==> x \/ y`) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm SUBSET_DIFF_UNION;;

let SUBSET_UNION_DIFF = prove
 (`!(s : A set) t u. s SUBSET (t UNION u) <=> ((s DIFF u) SUBSET t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  MATCH_ACCEPT_TAC SUBSET_DIFF_UNION);;

export_thm SUBSET_UNION_DIFF;;

let DIFF_UNION_CANCEL = prove
 (`!(s : A set) t. (s DIFF t) UNION t = s UNION t`,
  REWRITE_TAC [EXTENSION; IN_DIFF; IN_UNION] THEN
  REPEAT GEN_TAC THEN
  BOOL_CASES_TAC `(x:A) IN t` THEN
  REWRITE_TAC []);;

export_thm DIFF_UNION_CANCEL;;

let UNION_DIFF_CANCEL = prove
 (`!(s : A set) t. t UNION (s DIFF t) = t UNION s`,
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  ACCEPT_TAC DIFF_UNION_CANCEL);;

export_thm UNION_DIFF_CANCEL;;

let DISJOINT_DIFF = prove
 (`!(s : A set) t. (s DIFF t) = s <=> DISJOINT s t`,
  REWRITE_TAC [EXTENSION; DISJOINT; IN_DIFF; IN_INTER; NOT_IN_EMPTY] THEN
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   REWRITE_TAC [DE_MORGAN_THM] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm DISJOINT_DIFF;;

let DISJOINT_DIFF1 = prove
 (`!(s : A set) t. DISJOINT (t DIFF s) s`,
  REWRITE_TAC [GSYM DISJOINT_DIFF; DIFF_DIFF]);;

export_thm DISJOINT_DIFF1;;

let DISJOINT_DIFF2 = prove
 (`!(s : A set) t. DISJOINT s (t DIFF s)`,
  ONCE_REWRITE_TAC [DISJOINT_SYM] THEN
  ACCEPT_TAC DISJOINT_DIFF1);;

export_thm DISJOINT_DIFF2;;

let DIFF_UNION = prove
 (`!(t : A set) u s. (s DIFF t) DIFF u = s DIFF (t UNION u)`,
  REWRITE_TAC [EXTENSION; IN_DIFF; IN_UNION; CONJ_ASSOC; DE_MORGAN_THM]);;

export_thm DIFF_UNION;;

let DIFF_COMM = prove
 (`!(t : A set) u s. (s DIFF t) DIFF u = (s DIFF u) DIFF t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [DIFF_UNION] THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC UNION_COMM);;

export_thm DIFF_COMM;;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

let COMPONENT = prove
 (`!x:A. !s. x IN (x INSERT s)`,
  REWRITE_TAC [IN_INSERT]);;

export_thm COMPONENT;;

let DECOMPOSITION = prove
 (`!s : A set. !x. x IN s <=> ?t. (s = x INSERT t) /\ ~(x IN t)`,
  REPEAT GEN_TAC THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN EXISTS_TAC `s DELETE x:A` THEN
  REWRITE_TAC [EXTENSION; IN_INSERT; IN_DELETE] THEN
  GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_ACCEPT_TAC EXCLUDED_MIDDLE;
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm DECOMPOSITION;;

let SET_CASES = prove
 (`!s : A set. (s = EMPTY) \/ ?x:A. ?t. (s = x INSERT t) /\ ~(x IN t)`,
  GEN_TAC THEN
  MATCH_MP_TAC (TAUT `!x y. (~x ==> y) ==> x \/ y`) THEN
  REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] THEN
  STRIP_TAC THEN
  EXISTS_TAC `x:A` THEN
  ASM_REWRITE_TAC [GSYM DECOMPOSITION]);;

export_thm SET_CASES;;

let ABSORPTION = prove
 (`!x:A. !s. x IN s <=> (x INSERT s = s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_INSERT] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   DISCH_THEN (MP_TAC o SPEC `x:A`) THEN
   REWRITE_TAC []]);;

export_thm ABSORPTION;;

let INSERT_INSERT = prove
 (`!x:A. !s. x INSERT (x INSERT s) = x INSERT s`,
  REWRITE_TAC [EXTENSION; IN_INSERT; DISJ_ASSOC]);;

export_thm INSERT_INSERT;;

let INSERT_COMM = prove
 (`!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)`,
  REWRITE_TAC [EXTENSION; IN_INSERT; DISJ_ASSOC] THEN
  REPEAT GEN_TAC THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC DISJ_SYM);;

export_thm INSERT_COMM;;

let INSERT_UNION_EQ = prove
 (`!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)`,
  REWRITE_TAC [EXTENSION; IN_INSERT; IN_UNION; DISJ_ASSOC]);;

export_thm INSERT_UNION_EQ;;

let INSERT_UNION_SING = prove
 (`!x:A. !s. (x INSERT EMPTY) UNION s = x INSERT s`,
  REWRITE_TAC [INSERT_UNION_EQ; UNION_EMPTY]);;

export_thm INSERT_UNION_SING;;

let INSERT_UNIV = prove
 (`!x:A. x INSERT UNIV = UNIV`,
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
  REWRITE_TAC [UNION_UNIV]);;

export_thm INSERT_UNIV;;

let NOT_INSERT_EMPTY = prove
 (`!x:A. !s. ~(x INSERT s = EMPTY)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_INSERT; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
  EXISTS_TAC `x:A` THEN
  REWRITE_TAC []);;

export_thm NOT_INSERT_EMPTY;;

let NOT_EMPTY_INSERT = prove
 (`!x:A. !s. ~(EMPTY = x INSERT s)`,
  ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
  ACCEPT_TAC NOT_INSERT_EMPTY);;

let INSERT_UNION = prove
 (`!x:A. !s t. (x INSERT s) UNION t =
               if x IN t then s UNION t else x INSERT (s UNION t)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [EXTENSION; IN_UNION; IN_INSERT] THEN
  GEN_TAC THEN
  ASM_CASES_TAC `x' = (x:A)` THEN
  ASM_REWRITE_TAC []);;

export_thm INSERT_UNION;;

let INSERT_INTER = prove
 (`!x:A. !s t. (x INSERT s) INTER t =
               if x IN t then x INSERT (s INTER t) else s INTER t`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THEN
  ASM_REWRITE_TAC [EXTENSION; IN_INTER; IN_INSERT] THEN
  GEN_TAC THEN
  ASM_CASES_TAC `x' = (x:A)` THEN
  ASM_REWRITE_TAC []);;

export_thm INSERT_INTER;;

let DISJOINT_INSERT = prove
 (`!(x:A) s t. DISJOINT (x INSERT s) t <=> ~(x IN t) /\ (DISJOINT s t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
  REWRITE_TAC [DISJOINT_UNION] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [DISJOINT; EXTENSION; IN_INSERT; IN_INTER; NOT_IN_EMPTY] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `(x' : A) IN t` THEN
   ASM_REWRITE_TAC []]);;

export_thm DISJOINT_INSERT;;

let INSERT_SUBSET = prove
 (`!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\ s SUBSET t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
  REWRITE_TAC [UNION_SUBSET] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm INSERT_SUBSET;;

let SUBSET_INSERT = prove
 (`!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [SUBSET; IN_INSERT] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC (TAUT `!x y. ~x ==> (x \/ y ==> y)`) THEN
   STRIP_TAC THEN
   UNDISCH_TAC `(x' : A) IN s` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   DISJ2_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUBSET_INSERT;;

let SUBSET_INSERT_IMP = prove
 (`!s t (x:A). s SUBSET t ==> s SUBSET (x INSERT t)`,
  REWRITE_TAC [SUBSET; IN_INSERT] THEN
  REPEAT STRIP_TAC THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm SUBSET_INSERT_IMP;;

let INSERT_DIFF = prove
 (`!s t. !x:A. (x INSERT s) DIFF t =
               if x IN t then s DIFF t else x INSERT (s DIFF t)`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
  [REWRITE_TAC [EXTENSION; IN_INSERT; IN_DIFF; RIGHT_OR_DISTRIB] THEN
   GEN_TAC THEN
   MATCH_MP_TAC (TAUT `!x y. ~x ==> (x \/ y <=> y)`) THEN
   MATCH_MP_TAC (TAUT `!x y. (x ==> y) ==> ~(x /\ ~y)`) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   REWRITE_TAC [EXTENSION; IN_INSERT; IN_DIFF; RIGHT_OR_DISTRIB] THEN
   GEN_TAC THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm INSERT_DIFF;;

let INSERT_AC = prove
 (`!(x:A) y s.
     (x INSERT (y INSERT s) = y INSERT (x INSERT s)) /\
     (x INSERT (x INSERT s) = x INSERT s)`,
  REWRITE_TAC[INSERT_COMM; INSERT_INSERT]);;

export_thm INSERT_AC;;

let INTER_ACI = prove
 (`!(p : A set) q r.
     (p INTER q = q INTER p) /\
     ((p INTER q) INTER r = p INTER q INTER r) /\
     (p INTER q INTER r = q INTER p INTER r) /\
     (p INTER p = p) /\
     (p INTER p INTER q = p INTER q)`,
  PURE_REWRITE_TAC [EXTENSION; IN_INTER; GSYM FORALL_AND_THM] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC CONJ_ACI);;

export_thm INTER_ACI;;

let UNION_ACI = prove
 (`!(p : A set) q r.
     (p UNION q = q UNION p) /\
     ((p UNION q) UNION r = p UNION q UNION r) /\
     (p UNION q UNION r = q UNION p UNION r) /\
     (p UNION p = p) /\
     (p UNION p UNION q = p UNION q)`,
  PURE_REWRITE_TAC [EXTENSION; IN_UNION; GSYM FORALL_AND_THM] THEN
  REPEAT GEN_TAC THEN
  MATCH_ACCEPT_TAC DISJ_ACI);;

export_thm UNION_ACI;;

let DELETE_DIFF_SING = prove
 (`!x:A. !s. s DIFF (x INSERT EMPTY) = s DELETE x`,
  REWRITE_TAC [EXTENSION; IN_DELETE; IN_DIFF; IN_INSERT; NOT_IN_EMPTY]);;

export_thm DELETE_DIFF_SING;;

let DELETE_NON_ELEMENT = prove
 (`!x:A. !s. (s DELETE x = s) <=> ~(x IN s)`,
  REWRITE_TAC [GSYM DELETE_DIFF_SING; DISJOINT_DIFF; DISJOINT_SING]);;

export_thm DELETE_NON_ELEMENT;;

let IN_DELETE_SWAP = prove
 (`!s x. !x':A.
     (x IN s <=> x' IN s) ==>
     (x IN (s DELETE x') <=> x' IN (s DELETE x))`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [IN_DELETE] THEN
  AP_TERM_TAC THEN
  AP_TERM_TAC THEN
  MATCH_ACCEPT_TAC EQ_SYM_EQ);;

export_thm IN_DELETE_SWAP;;

let IN_DELETE_EQ = prove
 (`!s x. !x':A.
     (x IN (s DELETE x') <=> x' IN (s DELETE x)) <=>
     (x IN s <=> x' IN s)`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REWRITE_TAC [IN_DELETE] THEN
   ASM_CASES_TAC `(x:A) = x'` THEN
   ASM_REWRITE_TAC [];
   MATCH_ACCEPT_TAC IN_DELETE_SWAP]);;

export_thm IN_DELETE_EQ;;

let EMPTY_DELETE = prove
 (`!x:A. EMPTY DELETE x = EMPTY`,
  REWRITE_TAC [GSYM DELETE_DIFF_SING; EMPTY_DIFF]);;

export_thm EMPTY_DELETE;;

let DELETE_DELETE = prove
 (`!x:A. !s. (s DELETE x) DELETE x = s DELETE x`,
  REWRITE_TAC [GSYM DELETE_DIFF_SING; DIFF_DIFF]);;

export_thm DELETE_DELETE;;

let DELETE_COMM = prove
 (`!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM DELETE_DIFF_SING] THEN
  MATCH_ACCEPT_TAC DIFF_COMM);;

export_thm DELETE_COMM;;

let DELETE_SUBSET = prove
 (`!x:A. !s. (s DELETE x) SUBSET s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM DELETE_DIFF_SING] THEN
  MATCH_ACCEPT_TAC DIFF_SUBSET);;

export_thm DELETE_SUBSET;;

let SUBSET_DELETE = prove
 (`!x:A. !s t. s SUBSET (t DELETE x) <=> (s SUBSET t) /\ ~(x IN s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM DELETE_DIFF_SING; SUBSET_DIFF; DISJOINT_SING]);;

export_thm SUBSET_DELETE;;

let SUBSET_INSERT_DELETE = prove
 (`!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING; GSYM DELETE_DIFF_SING] THEN
  MATCH_ACCEPT_TAC SUBSET_DIFF_UNION);;

export_thm SUBSET_INSERT_DELETE;;

let DIFF_INSERT = prove
 (`!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING; GSYM DELETE_DIFF_SING] THEN
  REWRITE_TAC [DIFF_UNION]);;

export_thm DIFF_INSERT;;

let PSUBSET_INSERT_SUBSET = prove
 (`!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\ (x INSERT s) SUBSET t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [PSUBSET_ALT; INSERT_SUBSET] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EXISTS_TAC `a:A` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC []]]);;

export_thm PSUBSET_INSERT_SUBSET;;

let DELETE_INSERT = prove
 (`!x:A. !y s.
      (x INSERT s) DELETE y =
        if x = y then s DELETE y else x INSERT (s DELETE y)`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [EXTENSION; IN_INSERT; IN_DELETE] THEN
   GEN_TAC THEN
   BOOL_CASES_TAC `x' = (y : A)` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [EXTENSION; IN_INSERT; IN_DELETE] THEN
   GEN_TAC THEN
   BOOL_CASES_TAC `(x' : A) IN s` THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `(x' : A) = x` THEN
   ASM_REWRITE_TAC []]);;

export_thm DELETE_INSERT;;

let INSERT_DELETE = prove
 (`!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [EXTENSION; IN_INSERT; IN_DELETE] THEN
  GEN_TAC THEN
  ASM_CASES_TAC `(x' : A) = x` THEN
  ASM_REWRITE_TAC []);;

export_thm INSERT_DELETE;;

let DELETE_INSERT_NON_ELEMENT = prove
 (`!(x:A) s. (x INSERT s) DELETE x = s <=> ~(x IN s)`,
  REWRITE_TAC [DELETE_INSERT; DELETE_NON_ELEMENT]);;

export_thm DELETE_INSERT_NON_ELEMENT;;

let DELETE_INTER = prove
 (`!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x`,
  REWRITE_TAC [EXTENSION; IN_DELETE; IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm DELETE_INTER;;

let DISJOINT_DELETE_SYM = prove
 (`!s t. !x:A. DISJOINT (s DELETE x) t <=> DISJOINT (t DELETE x) s`,
  REWRITE_TAC [DISJOINT; IN_DELETE; IN_INTER; NOT_IN_EMPTY; EXTENSION] THEN
  REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  AP_TERM_TAC THEN
  EQ_TAC THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm DISJOINT_DELETE_SYM;;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let UNIONS_0 = prove
 (`UNIONS {} = ({} : A set)`,
  REWRITE_TAC [EXTENSION; IN_UNIONS; NOT_IN_EMPTY]);;

export_thm UNIONS_0;;

let UNIONS_INSERT = prove
 (`!(s : A set) u. UNIONS (s INSERT u) = s UNION (UNIONS u)`,
  ONCE_REWRITE_TAC [EXTENSION] THEN
  REWRITE_TAC [IN_UNIONS; IN_UNION; IN_INSERT] THEN
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THENL
   [DISJ1_TAC THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [];
    DISJ2_TAC THEN
    EXISTS_TAC `t : A set` THEN
    ASM_REWRITE_TAC []];
   STRIP_TAC THENL
   [EXISTS_TAC `s : A set` THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `t : A set` THEN
    ASM_REWRITE_TAC []]]);;

export_thm UNIONS_INSERT;;

let UNIONS_1 = prove
 (`!s : A set. UNIONS {s} = s`,
  REWRITE_TAC [UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

export_thm UNIONS_1;;

let UNIONS_2 = prove
 (`!(s : A set) t. UNIONS {s,t} = s UNION t`,
  REWRITE_TAC [UNIONS_INSERT; UNIONS_0; UNION_EMPTY]);;

export_thm UNIONS_2;;

let FORALL_IN_UNIONS = prove
 (`!p (s : (A set) set).
     (!x. x IN UNIONS s ==> p x) <=> !t x. t IN s /\ x IN t ==> p x`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  REWRITE_TAC [IN_UNIONS; LEFT_IMP_EXISTS_THM]);;

export_thm FORALL_IN_UNIONS;;

let EXISTS_IN_UNIONS = prove
 (`!p (s : (A set) set).
    (?x. x IN UNIONS s /\ p x) <=> (?t x. t IN s /\ x IN t /\ p x)`,
  ONCE_REWRITE_TAC [SWAP_EXISTS_THM] THEN
  REWRITE_TAC [IN_UNIONS; LEFT_AND_EXISTS_THM; CONJ_ASSOC]);;

export_thm EXISTS_IN_UNIONS;;

let EMPTY_UNIONS = prove
 (`!s : (A set) set. (UNIONS s = {}) <=> !t. t IN s ==> t = {}`,
  GEN_TAC THEN
  REWRITE_TAC
    [EXTENSION; IN_UNIONS; NOT_IN_EMPTY; NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`x:A`; `t : A set`]) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `t : A set`) THEN
   BOOL_CASES_TAC `(t : A set) IN s` THEN
   REWRITE_TAC [] THEN
   DISCH_THEN MATCH_ACCEPT_TAC]);;

export_thm EMPTY_UNIONS;;

let UNIONS_INTER = prove
 (`!s (t : A set). UNIONS s INTER t = UNIONS {x INTER t | x IN s}`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `t' INTER (t : A set)` THEN
   ASM_REWRITE_TAC [IN_INTER] THEN
   EXISTS_TAC `t' : A set` THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_REWRITE_TAC [IN_INTER] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A set` THEN
   ASM_REWRITE_TAC []]);;

export_thm UNIONS_INTER;;

let INTER_UNIONS = prove
 (`!s (t : A set). t INTER UNIONS s = UNIONS {t INTER x | x IN s}`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [INTER_COMM] THEN
  MATCH_ACCEPT_TAC UNIONS_INTER);;

export_thm INTER_UNIONS;;

let UNIONS_SUBSET = prove
 (`!f (t : A set). UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `s : A set` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `t' : A set`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm UNIONS_SUBSET;;

let SUBSET_UNIONS = prove
 (`!(f : (A set) set) g. f SUBSET g ==> UNIONS f SUBSET UNIONS g`,
  REWRITE_TAC [SUBSET; IN_UNIONS] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `t : A set` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm SUBSET_UNIONS;;

let UNIONS_UNION = prove
 (`!(s : (A set) set) t. UNIONS (s UNION t) = (UNIONS s) UNION (UNIONS t)`,
  REWRITE_TAC [EXTENSION; IN_UNIONS; IN_UNION] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THENL
   [DISJ1_TAC THEN
    EXISTS_TAC `t' : A set` THEN
    ASM_REWRITE_TAC [];
    DISJ2_TAC THEN
    EXISTS_TAC `t' : A set` THEN
    ASM_REWRITE_TAC []];
   STRIP_TAC THENL
   [EXISTS_TAC `t' : A set` THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `t' : A set` THEN
    ASM_REWRITE_TAC []]]);;

export_thm UNIONS_UNION;;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let INTERS_0 = prove
 (`INTERS {} = (UNIV : A set)`,
  REWRITE_TAC [EXTENSION; IN_INTERS; IN_UNIV; NOT_IN_EMPTY]);;

export_thm INTERS_0;;

let INTERS_INSERT = prove
 (`!(s : A set) u. INTERS (s INSERT u) = s INTER (INTERS u)`,
  ONCE_REWRITE_TAC [EXTENSION] THEN
  REWRITE_TAC [IN_INTERS; IN_INTER; IN_INSERT] THEN
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]]);;

export_thm INTERS_INSERT;;

let INTERS_1 = prove
 (`!s : A set. INTERS {s} = s`,
  REWRITE_TAC [INTERS_INSERT; INTERS_0; INTER_UNIV]);;

export_thm INTERS_1;;

let INTERS_2 = prove
 (`!(s : A set) t. INTERS {s,t} = s INTER t`,
  REWRITE_TAC [INTERS_INSERT; INTERS_0; INTER_UNIV]);;

export_thm INTERS_2;;

let UNIV_INTERS = prove
 (`!s : (A set) set. (INTERS s = UNIV) <=> !t. t IN s ==> t = UNIV`,
  REWRITE_TAC [EXTENSION; IN_INTERS; IN_UNIV] THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  REWRITE_TAC [RIGHT_IMP_FORALL_THM]);;

export_thm UNIV_INTERS;;

let INTERS_UNION = prove
 (`!s (t : A set). INTERS s UNION t = INTERS {x UNION t | x IN s}`,
  ONCE_REWRITE_TAC[EXTENSION] THEN
  REWRITE_TAC[IN_INTERS; IN_ELIM_THM; IN_UNION] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [IN_UNION] THEN
    DISJ1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC [IN_UNION]];
   REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `(x : A) IN t` THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `t' UNION (t : A set)`) THEN
   ASM_REWRITE_TAC [IN_UNION] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   EXISTS_TAC `t' : A set` THEN
   ASM_REWRITE_TAC []]);;

export_thm INTERS_UNION;;

let UNION_INTERS = prove
 (`!s (t : A set). t UNION INTERS s = INTERS {t UNION x | x IN s}`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  MATCH_ACCEPT_TAC INTERS_UNION);;

export_thm UNION_INTERS;;

let SUBSET_INTERS = prove
 (`!(t : A set) f. t SUBSET (INTERS f) <=> !s. s IN f ==> t SUBSET s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_INTERS] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC;
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `t' : A set`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUBSET_INTERS;;

let INTERS_SUBSET = prove
 (`!(f : (A set) set) g. f SUBSET g ==> (INTERS g) SUBSET (INTERS f)`,
  REWRITE_TAC [SUBSET; IN_INTERS] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm INTERS_SUBSET;;

let INTERS_UNION = prove
 (`!(s : (A set) set) t. INTERS (s UNION t) = (INTERS s) INTER (INTERS t)`,
  REWRITE_TAC [EXTENSION; IN_INTERS; IN_INTER; IN_UNION] THEN
  REWRITE_TAC [GSYM FORALL_AND_THM] THEN
  REPEAT STRIP_TAC THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  ITAUT_TAC);;

export_thm INTERS_UNION;;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let IMAGE_EMPTY = prove
 (`!(f : A -> B). IMAGE f {} = {}`,
  REWRITE_TAC [IMAGE; IN_ELIM_THM; NOT_IN_EMPTY; EXTENSION]);;

export_thm IMAGE_EMPTY;;

let IMAGE_INSERT = prove
 (`!(f : A -> B) x s. IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s)`,
  REWRITE_TAC [IMAGE; IN_ELIM_THM; IN_INSERT; EXTENSION] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    DISJ2_TAC THEN
    EXISTS_TAC `y:B` THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `x'':A` THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `x':B` THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `x:A` THEN
    ASM_REWRITE_TAC [];
    EXISTS_TAC `y:B` THEN
    ASM_REWRITE_TAC [] THEN
    EXISTS_TAC `x'':A` THEN
    ASM_REWRITE_TAC []]]);;

export_thm IMAGE_INSERT;;

let IMAGE_CLAUSES = CONJ IMAGE_EMPTY IMAGE_INSERT;;

let IMAGE_SING = prove
 (`!(f : A -> B) x. IMAGE f (x INSERT EMPTY) = f x INSERT EMPTY`,
  REWRITE_TAC [IMAGE_CLAUSES]);;

export_thm IMAGE_SING;;

let IMAGE_UNION = prove
 (`!(f : A -> B) s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)`,
  REWRITE_TAC
    [EXTENSION; IN_IMAGE; IN_UNION; GSYM EXISTS_OR_THM; LEFT_OR_DISTRIB]);;

export_thm IMAGE_UNION;;

let IMAGE_ID = prove
 (`!s. IMAGE (\x. (x:A)) s = s`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; UNWIND_THM1]);;

export_thm IMAGE_ID;;

let IMAGE_I = prove
 (`!s : A set. IMAGE I s = s`,
  REWRITE_TAC [I_DEF; IMAGE_ID]);;

export_thm IMAGE_I;;

let IMAGE_o = prove
 (`!(f : B -> C) (g : A -> B) s. IMAGE (f o g) s = IMAGE f (IMAGE g s)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; o_THM] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EXISTS_TAC `(g : A -> B) x'` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `x'' : A` THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_o;;

let IMAGE_SUBSET = prove
 (`!(f : A -> B) s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)`,
  REWRITE_TAC[SUBSET; IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x':A` THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm IMAGE_SUBSET;;

let IMAGE_INTER_INJ = prove
 (`!(f : A -> B) s t.
     (!x y. (f(x) = f(y)) ==> (x = y))
        ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))`,
  REWRITE_TAC [EXTENSION; IN_IMAGE; IN_INTER] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN `(x':A) = x''` (fun th -> ASM_REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th]) THEN
   FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th])]);;

export_thm IMAGE_INTER_INJ;;

let IMAGE_DIFF_INJ = prove
 (`!(f : A -> B) s t.
      (!x y. (f(x) = f(y)) ==> (x = y))
           ==> (IMAGE f (s DIFF t) = (IMAGE f s) DIFF (IMAGE f t))`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_DIFF; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [EXISTS_TAC `x':A` THEN
    ASM_REWRITE_TAC [];
    UNDISCH_TAC `~((x':A) IN t)` THEN
    SUBGOAL_THEN `(x':A) = x''` (fun th -> ASM_REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th])];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_DIFF_INJ;;

let IMAGE_DELETE_INJ = prove
 (`!(f : A -> B) s a.
      (!x. (f(x) = f(a)) ==> (x = a))
           ==> (IMAGE f (s DELETE a) = (IMAGE f s) DELETE (f a))`,
  REWRITE_TAC [EXTENSION; IN_IMAGE; IN_DELETE; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [EXISTS_TAC `x':A` THEN
    ASM_REWRITE_TAC [];
    UNDISCH_TAC `~((x':A) = a)` THEN
    REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_X_ASSUM (fun th -> REWRITE_TAC [SYM th])];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   UNDISCH_TAC `x = (f : A -> B) x'` THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_DELETE_INJ;;

let IMAGE_EQ_EMPTY = prove
 (`!(f : A -> B) s. (IMAGE f s = {}) <=> (s = {})`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_IMAGE; NOT_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`(f : A -> B) x`; `x:A`]) THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`x':A`]) THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_EQ_EMPTY;;

let FORALL_IN_IMAGE = prove
 (`!p (f : A -> B) s. (!y. y IN IMAGE f s ==> p y) <=> (!x. x IN s ==> p (f x))`,
  REWRITE_TAC[IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm FORALL_IN_IMAGE;;

let EXISTS_IN_IMAGE = prove
 (`!p (f : A -> B) s. (?y. y IN IMAGE f s /\ p y) <=> ?x. x IN s /\ p (f x)`,
  REWRITE_TAC[IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:A` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B) x` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x : A` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_IN_IMAGE;;

let SUBSET_IMAGE = prove
 (`!(f : A -> B) s t.
     s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\ (s = IMAGE f u)`,
  REWRITE_TAC [EXTENSION; SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `{x | x IN t /\ (f:A->B) x IN s}` THEN
   REWRITE_TAC [IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    EQ_TAC THENL
    [REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `x:B`) THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     EXISTS_TAC `x':A` THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `x':A` THEN
     FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
     STRIP_TAC THEN
     ASM_REWRITE_TAC []]];
   FIRST_X_ASSUM (MP_TAC o SPEC `x:B`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SUBSET_IMAGE;;

let FORALL_SUBSET_IMAGE = prove
 (`!p (f : A -> B) s.
     (!t. t SUBSET IMAGE f s ==> p t) <=>
     (!t. t SUBSET s ==> p (IMAGE f t))`,
  REWRITE_TAC [SUBSET_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm FORALL_SUBSET_IMAGE;;

let EXISTS_SUBSET_IMAGE = prove
 (`!p (f : A -> B) s.
    (?t. t SUBSET IMAGE f s /\ p t) <=> (?t. t SUBSET s /\ p (IMAGE f t))`,
  REWRITE_TAC [SUBSET_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `u : A set` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `IMAGE (f : A -> B) t` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_SUBSET_IMAGE;;

let IMAGE_CONST = prove
 (`!(s : A set) (c : B). IMAGE (\x. c) s = if s = {} then {} else {c}`,
  REPEAT GEN_TAC THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [IMAGE_CLAUSES];
   POP_ASSUM (MP_TAC o REWRITE_RULE [GSYM MEMBER_NOT_EMPTY]) THEN
   STRIP_TAC THEN
   REWRITE_TAC [EXTENSION; IN_IMAGE; IN_SING] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THEN
   EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_CONST;;

let SIMPLE_IMAGE = prove
 (`!(f : A -> B) s. {f x | x IN s} = IMAGE f s`,
  REWRITE_TAC [EXTENSION; IN_IMAGE] THEN
  ONCE_REWRITE_TAC [CONJ_SYM] THEN
  REWRITE_TAC [IN_ELIM_THM]);;

export_thm SIMPLE_IMAGE;;

let SIMPLE_IMAGE_GEN = prove
 (`!p (f : A -> B). {f x | p x} = IMAGE f {x | p x}`,
  REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [];
   EXISTS_TAC `x'':A` THEN
   ASM_REWRITE_TAC []]);;

export_thm SIMPLE_IMAGE_GEN;;

let IMAGE_UNIONS = prove
 (`!(f : A -> B) s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)`,
  ONCE_REWRITE_TAC[EXTENSION] THEN REWRITE_TAC[IN_UNIONS; IN_IMAGE] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[SWAP_EXISTS_THM] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC; UNWIND_THM2; IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [];
   EXISTS_TAC `x'':A` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A set` THEN
   ASM_REWRITE_TAC []]);;

export_thm IMAGE_UNIONS;;

let FUN_IN_IMAGE = prove
 (`!(f : A -> B) s x. x IN s ==> f x IN IMAGE f s`,
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x:A` THEN
  ASM_REWRITE_TAC []);;

export_thm FUN_IN_IMAGE;;

let SURJECTIVE_IMAGE_EQ = prove
 (`!(f : A -> B) s t.
     (!y. y IN t ==> ?x. f x = y) /\ (!x. (f x) IN t <=> x IN s)
         ==> IMAGE f s = t`,
  REWRITE_TAC [EXTENSION; IN_IMAGE] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [ASM_REWRITE_TAC [];
   FIRST_X_ASSUM (MP_TAC o SPEC `x:B`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   EXISTS_TAC `x' : A` THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM (SPEC `x' : A` th)])]);;

export_thm SURJECTIVE_IMAGE_EQ;;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let EMPTY_GSPEC = prove
 (`GSPEC (\ (x:A). F) = {}`,
  REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM]);;

export_thm EMPTY_GSPEC;;

let SING_GSPEC1 = prove
 (`!(a:A). {x | x = a} = {a}`,
  REWRITE_TAC [EXTENSION; IN_ELIM; IN_SING]);;

export_thm SING_GSPEC1;;

let SING_GSPEC2 = prove
 (`!(a:A). {x | a = x} = {a}`,
  REWRITE_TAC [EXTENSION; IN_ELIM; IN_SING] THEN
  ACCEPT_TAC EQ_SYM_EQ);;

export_thm SING_GSPEC2;;

let SING_GSPEC = CONJ SING_GSPEC1 SING_GSPEC2;;

let IN_ELIM_PAIR_THM = prove
 (`!p (a:A) (b:B). (a,b) IN {(x,y) | p x y} <=> p a b`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   EXISTS_TAC `a:A` THEN
   EXISTS_TAC `b:B` THEN
   ASM_REWRITE_TAC []]);;

export_thm IN_ELIM_PAIR_THM;;

let SET_PAIR_THM = prove
 (`!(p : A # B -> bool). { ab | p ab } = { (a,b) | p (a,b) }`,
  REWRITE_TAC [EXTENSION; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPEC `ab : A # B` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   EXISTS_TAC `x:A` THEN
   EXISTS_TAC `y:B` THEN
   ASM_REWRITE_TAC [];
   EXISTS_TAC `(a:A,b:B)` THEN
   ASM_REWRITE_TAC []]);;

export_thm SET_PAIR_THM;;

let FORALL_IN_GSPEC1 = prove
 (`!p (f : A -> B) q.
     (!z. z IN {f x | p x} ==> q z) <=> (!x. p x ==> q (f x))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x:A` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm FORALL_IN_GSPEC1;;

let FORALL_IN_GSPEC2 = prove
 (`!p (f : A -> B -> C) q.
     (!z. z IN {f x y | p x y} ==> q z) <=>
     (!x y. p x y ==> q (f x y))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x:A` THEN
   EXISTS_TAC `y:B` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm FORALL_IN_GSPEC2;;

let FORALL_IN_GSPEC3 = prove
 (`!p (f : A -> B -> C -> D) q.
     (!z. z IN {f w x y | p w x y} ==> q z) <=>
     (!w x y. p w x y ==> q (f w x y))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `w:A` THEN
   EXISTS_TAC `x:B` THEN
   EXISTS_TAC `y:C` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm FORALL_IN_GSPEC3;;

let FORALL_IN_GSPEC =
    CONJ FORALL_IN_GSPEC1 (CONJ FORALL_IN_GSPEC2 FORALL_IN_GSPEC3);;

let EXISTS_IN_GSPEC1 = prove
 (`!p (f : A -> B) q.
     (?z. z IN {f x | p x} /\ q z) <=> (?x. p x /\ q (f x))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:A` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B) x` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x : A` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_IN_GSPEC1;;

let EXISTS_IN_GSPEC2 = prove
 (`!p (f : A -> B -> C) q.
     (?z. z IN {f x y | p x y} /\ q z) <=>
     (?x y. p x y /\ q (f x y))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:A` THEN
   EXISTS_TAC `y:B` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B -> C) x y` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x : A` THEN
   EXISTS_TAC `y : B` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_IN_GSPEC2;;

let EXISTS_IN_GSPEC3 = prove
 (`!p (f : A -> B -> C -> D) q.
     (?z. z IN {f w x y | p w x y} /\ q z) <=>
     (?w x y. p w x y /\ q (f w x y))`,
  REWRITE_TAC [IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `w:A` THEN
   EXISTS_TAC `x:B` THEN
   EXISTS_TAC `y:C` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B -> C -> D) w x y` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `w : A` THEN
   EXISTS_TAC `x : B` THEN
   EXISTS_TAC `y : C` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_IN_GSPEC3;;

let EXISTS_IN_GSPEC =
    CONJ EXISTS_IN_GSPEC1 (CONJ EXISTS_IN_GSPEC2 EXISTS_IN_GSPEC3);;

let SET_PROVE_CASES = prove
 (`!p : A set -> bool.
       p {} /\ (!a s. ~(a IN s) ==> p (a INSERT s))
       ==> !s. p s`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `s:A set` SET_CASES) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [];
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SET_PROVE_CASES;;

let UNIONS_IMAGE = prove
 (`!(f : A -> B set) s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\ y IN f x}`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x : B` THEN
   REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B set) x'` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   ASM_REWRITE_TAC []]);;

export_thm UNIONS_IMAGE;;

let INTERS_IMAGE = prove
 (`!(f : A -> B set) s.
     INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_INTERS; IN_IMAGE; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x : B` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x' : A` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm INTERS_IMAGE;;

let UNIONS_GSPEC1 = prove
 (`!p (f : A -> B set).
     UNIONS {f x | p x} = {a | ?x. p x /\ a IN (f x)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_UNIONS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:B` THEN
   REWRITE_TAC [] THEN
   EXISTS_TAC `x':A` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B set) x'` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   ASM_REWRITE_TAC []]);;

export_thm UNIONS_GSPEC1;;

let UNIONS_GSPEC2 = prove
 (`!p (f : A -> B -> C set).
     UNIONS {f x y | p x y} = {a | ?x y. p x y /\ a IN (f x y)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_UNIONS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:C` THEN
   REWRITE_TAC [] THEN
   EXISTS_TAC `x':A` THEN
   EXISTS_TAC `y:B` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B -> C set) x' y` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   EXISTS_TAC `y : B` THEN
   ASM_REWRITE_TAC []]);;

export_thm UNIONS_GSPEC2;;

let UNIONS_GSPEC3 = prove
 (`!p (f : A -> B -> C -> D set).
     UNIONS {f x y z | p x y z} =
     {a | ?x y z. p x y z /\ a IN (f x y z)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_UNIONS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:D` THEN
   REWRITE_TAC [] THEN
   EXISTS_TAC `x':A` THEN
   EXISTS_TAC `y:B` THEN
   EXISTS_TAC `z:C` THEN
   FIRST_X_ASSUM (fun th -> ASM_REWRITE_TAC [SYM th]);
   EXISTS_TAC `(f : A -> B -> C -> D set) x' y z` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `x' : A` THEN
   EXISTS_TAC `y : B` THEN
   EXISTS_TAC `z : C` THEN
   ASM_REWRITE_TAC []]);;

export_thm UNIONS_GSPEC3;;

let UNIONS_GSPEC =
    CONJ UNIONS_GSPEC1 (CONJ UNIONS_GSPEC2 UNIONS_GSPEC3);;

let INTERS_GSPEC1 = prove
 (`!p (f : A -> B set).
     INTERS {f x | p x} = {a | !x. p x ==> a IN (f x)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_INTERS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:B` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x':A` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm INTERS_GSPEC1;;

let INTERS_GSPEC2 = prove
 (`!p (f : A -> B -> C set).
     INTERS {f x y | p x y} = {a | !x y. p x y ==> a IN (f x y)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_INTERS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:C` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x':A` THEN
   EXISTS_TAC `y:B` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm INTERS_GSPEC2;;

let INTERS_GSPEC3 = prove
 (`!p (f : A -> B -> C -> D set).
     INTERS {f x y z | p x y z} =
     {a | !x y z. p x y z ==> a IN (f x y z)}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC [IN_INTERS; IN_ELIM_THM] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [EXISTS_TAC `x:D` THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x':A` THEN
   EXISTS_TAC `y:B` THEN
   EXISTS_TAC `z:C` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm INTERS_GSPEC3;;

let INTERS_GSPEC =
    CONJ INTERS_GSPEC1 (CONJ INTERS_GSPEC2 INTERS_GSPEC3);;

let DIFF_INTERS = prove
 (`!(u : A set) s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [UNIONS_GSPEC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  GEN_TAC THEN
  REWRITE_TAC [IN_INTERS; IN_DIFF; IN_ELIM; NOT_FORALL_THM] THEN
  BOOL_CASES_TAC `(x:A) IN u` THEN
  REWRITE_TAC [] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  BOOL_CASES_TAC `(x:A) IN t` THEN
  REWRITE_TAC []);;

export_thm DIFF_INTERS;;

let INTERS_UNIONS = prove
 (`!(s : (A set) set). INTERS s = UNIV DIFF (UNIONS {UNIV DIFF t | t IN s})`,
  GEN_TAC THEN
  REWRITE_TAC [GSYM DIFF_INTERS] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  GEN_TAC THEN
  REWRITE_TAC [IN_INTERS; IN_DIFF; IN_UNIV]);;

export_thm INTERS_UNIONS;;

let UNIONS_INTERS = prove
 (`!(s : (A set) set). UNIONS s = UNIV DIFF (INTERS {UNIV DIFF t | t IN s})`,
  GEN_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  GEN_TAC THEN
  REWRITE_TAC
    [IN_UNIONS; IN_UNIV; IN_DIFF; INTERS_GSPEC; IN_ELIM; NOT_FORALL_THM;
     NOT_IMP]);;

export_thm UNIONS_INTERS;;

let INTERS_OVER_UNIONS = prove
 (`!(f:A->((B set) set)) s.
        INTERS { UNIONS(f x) | x IN s} =
        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `b:B` THEN
  REWRITE_TAC
    [SIMPLE_IMAGE; INTERS_IMAGE; UNIONS_IMAGE; INTERS_IMAGE; UNIONS_GSPEC] THEN
  REWRITE_TAC [IN_UNIONS; IN_ELIM] THEN
  REWRITE_TAC [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  REWRITE_TAC [GSYM FORALL_AND_THM] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  BOOL_CASES_TAC `(x : A) IN s` THEN
  REWRITE_TAC []);;

export_thm INTERS_OVER_UNIONS;;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "set-finite-def";;

let FINITE_RULES,FINITE_INDUCT,FINITE_CASES =
  new_inductive_definition
    `FINITE (EMPTY : A set) /\
     !(x:A) s. FINITE s ==> FINITE (x INSERT s)`;;

export_thm FINITE_INDUCT;;
export_thm FINITE_CASES;;

let FINITE_EMPTY = CONJUNCT1 FINITE_RULES;;

export_thm FINITE_EMPTY;;

let FINITE_INSERT_IMP = CONJUNCT2 FINITE_RULES;;

export_thm FINITE_INSERT_IMP;;

let FINITE_RULES = CONJ FINITE_EMPTY FINITE_INSERT_IMP;;

let INFINITE = new_definition
  `INFINITE (s:A set) <=> ~(FINITE s)`;;

export_thm INFINITE;;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

logfile "set-finite-thm";;

let FINITE_SUBSET = prove
 (`!(s:A set) t. FINITE t /\ s SUBSET t ==> FINITE s`,
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC [SUBSET_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [FINITE_EMPTY];
   X_GEN_TAC `x:A` THEN X_GEN_TAC `u:A set` THEN DISCH_TAC THEN
   X_GEN_TAC `t:A set` THEN DISCH_TAC THEN
   ASM_CASES_TAC `(x : A) IN t` THENL
   [MP_TAC (SPECL [`x:A`; `t: A set`] INSERT_DELETE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [SYM th]) THEN
    MATCH_MP_TAC (CONJUNCT2 FINITE_RULES) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [GSYM SUBSET_INSERT_DELETE];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `t SUBSET ((x:A) INSERT u)` THEN
    ASM_REWRITE_TAC [SUBSET; IN_INSERT] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC (TAUT `!x y. ~x ==> (x \/ y ==> y)`) THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(x' : A) IN t` THEN
    ASM_REWRITE_TAC []]]);;

export_thm FINITE_SUBSET;;

let FINITE_UNION_IMP = prove
 (`!(s:A set) t. FINITE s /\ FINITE t ==> FINITE (s UNION t)`,
  REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT THEN REWRITE_TAC[UNION_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
  REWRITE_TAC [UNION_ASSOC] THEN
  ONCE_REWRITE_TAC [INSERT_UNION_SING] THEN
  MATCH_MP_TAC (CONJUNCT2 FINITE_RULES) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm FINITE_UNION_IMP;;

let FINITE_UNION = prove
 (`!(s:A set) t. FINITE(s UNION t) <=> FINITE(s) /\ FINITE(t)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(s:A set) UNION t` THEN
    ASM_REWRITE_TAC [SUBSET_UNION];
    MATCH_ACCEPT_TAC FINITE_UNION_IMP]);;

export_thm FINITE_UNION;;

let FINITE_INTER = prove
 (`!(s:A set) t. FINITE s \/ FINITE t ==> FINITE (s INTER t)`,
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `s : A set` THEN
   ASM_REWRITE_TAC [INTER_SUBSET];
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC [INTER_SUBSET]]);;

export_thm FINITE_INTER;;

let FINITE_INSERT = prove
 (`!(s : A set) x. FINITE (x INSERT s) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [STRIP_TAC THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `(x:A) INSERT s` THEN
   ASM_REWRITE_TAC [] THEN
   ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
   REWRITE_TAC [SUBSET_UNION];
   MATCH_ACCEPT_TAC (CONJUNCT2 FINITE_RULES)]);;

export_thm FINITE_INSERT;;

let FINITE_SING = prove
 (`!(a : A). FINITE {a}`,
  REWRITE_TAC [FINITE_INSERT; FINITE_EMPTY]);;

export_thm FINITE_SING;;

let FINITE_DELETE_IMP = prove
 (`!(s:A set) x. FINITE s ==> FINITE (s DELETE x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s : A set` THEN
  ASM_REWRITE_TAC [DELETE_SUBSET]);;

export_thm FINITE_DELETE_IMP;;

let FINITE_DELETE = prove
 (`!(s : A set) x. FINITE (s DELETE x) <=> FINITE s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [ASM_CASES_TAC `(x:A) IN s` THENL
   [STRIP_TAC THEN
    MP_TAC (SPECL [`x:A`; `s : A set`] INSERT_DELETE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [SYM th]) THEN
    ASM_REWRITE_TAC [FINITE_INSERT];
    MP_TAC (SPECL [`x:A`; `s : A set`] DELETE_NON_ELEMENT) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [th])];
   MATCH_ACCEPT_TAC FINITE_DELETE_IMP]);;

export_thm FINITE_DELETE;;

let FINITE_FINITE_UNIONS = prove
 (`!(s : (A set) set).
     FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))`,
  MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; UNIONS_0; FINITE_EMPTY];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [IN_INSERT; UNIONS_INSERT; FINITE_UNION] THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM SUBST_VAR_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC];
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []]]]);;

export_thm FINITE_FINITE_UNIONS;;

let FINITE_IMAGE_EXPAND = prove
 (`!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\ (y = f x)}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; EMPTY_GSPEC; FINITE_EMPTY];
   REPEAT GEN_TAC THEN
   SUBGOAL_THEN `{y | ?z. z IN (x INSERT s) /\ (y = (f:A->B) z)} =
                 {y | ?z. z IN s /\ (y = f z)} UNION {(f x)}`
     (fun th -> REWRITE_TAC [th]) THENL
   [REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_INSERT; IN_UNION; NOT_IN_EMPTY] THEN
    GEN_TAC THEN
    EQ_TAC THENL
    [REPEAT STRIP_TAC THENL
     [DISJ2_TAC THEN
      ASM_REWRITE_TAC [];
      DISJ1_TAC THEN
      EXISTS_TAC `x':B` THEN
      ASM_REWRITE_TAC [] THEN
      EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC []];
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC `x':B` THEN
      ASM_REWRITE_TAC [] THEN
      EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC [];
      EXISTS_TAC `x':B` THEN
      ASM_REWRITE_TAC [] THEN
      EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC []]];
    STRIP_TAC THEN
    ASM_REWRITE_TAC [FINITE_UNION; FINITE_INSERT; FINITE_EMPTY]]]);;

export_thm FINITE_IMAGE_EXPAND;;

let FINITE_IMAGE = prove
 (`!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)`,
  REWRITE_TAC [IMAGE; FINITE_IMAGE_EXPAND]);;

export_thm FINITE_IMAGE;;

let FINITE_IMAGE_INJ_GENERAL = prove
 (`!(f:A->B) A s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
                  FINITE A ==> FINITE {x | x IN s /\ f(x) IN A}`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  GEN_TAC THEN
  REWRITE_TAC [IMP_CONJ] THEN
  REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC FINITE_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; EMPTY_GSPEC; FINITE_EMPTY];
   X_GEN_TAC `y:B` THEN
   X_GEN_TAC `t : B set` THEN
   DISCH_TAC THEN
   SUBGOAL_THEN
     `{x | x IN s /\ (f:A->B) x IN (y INSERT t)} =
      if (?x. x IN s /\ (f x = y))
      then (@x. x IN s /\ (f x = y)) INSERT {x | x IN s /\ f x IN t}
      else {x | x IN s /\ f x IN t}`
     (fun th -> ONCE_REWRITE_TAC [th]) THENL
  [COND_CASES_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SELECT_RULE) THEN
    SPEC_TAC (`@x. x IN s /\ ((f:A->B) x = y)`,`z:A`) THEN
    REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    REPEAT STRIP_TAC THEN
    EQ_TAC THENL
    [STRIP_TAC THENL
     [DISJ1_TAC THEN
      ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (MP_TAC o SPEC `z:A`) THEN
      ASM_REWRITE_TAC [];
      DISJ2_TAC THEN
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC []];
     STRIP_TAC THENL
     [EXISTS_TAC `z:A` THEN
      ASM_REWRITE_TAC [];
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC []]];
    REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_INSERT] THEN
    X_GEN_TAC `z:A` THEN
    EQ_TAC THENL
    [STRIP_TAC THENL
     [SUBGOAL_THEN `F` CONTR_TAC THEN
      UNDISCH_TAC `~(?x. x IN s /\ (f:A->B) x = y)` THEN
      REWRITE_TAC [] THEN
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC [];
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC []];
     STRIP_TAC THEN
     EXISTS_TAC `x':A` THEN
     ASM_REWRITE_TAC []]];
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [FINITE_INSERT];
     FIRST_ASSUM ACCEPT_TAC]]]);;

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
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC [IN_ELIM_THM; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `z:A` THEN
    EQ_TAC THENL
    [REPEAT STRIP_TAC THEN
     EXISTS_TAC `(f : A -> B) x'` THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `x' : A` THEN
     ASM_REWRITE_TAC [];
     REPEAT STRIP_TAC THEN
     EXISTS_TAC `x' : A` THEN
     ASM_REWRITE_TAC []];
    ASM_SIMP_TAC[FINITE_FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE]]);;

export_thm FINITE_FINITE_PREIMAGE_GENERAL;;

let FINITE_FINITE_PREIMAGE = prove
 (`!f:A->B t.
        FINITE t /\
        (!y. y IN t ==> FINITE {x | f(x) = y})
        ==> FINITE {x | f(x) IN t}`,
  REPEAT GEN_TAC THEN MP_TAC
   (ISPECL [`f:A->B`; `UNIV : A set`; `t : B set`]
      FINITE_FINITE_PREIMAGE_GENERAL) THEN
  REWRITE_TAC[IN_UNIV]);;

export_thm FINITE_FINITE_PREIMAGE;;

let FINITE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s. (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y))
                ==> (FINITE(IMAGE f s) <=> FINITE s)`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [POP_ASSUM MP_TAC THEN
   REWRITE_TAC[IMP_IMP] THEN
   DISCH_THEN (MP_TAC o MATCH_MP FINITE_IMAGE_INJ_GENERAL) THEN
   MATCH_MP_TAC EQ_IMP THEN
   AP_TERM_TAC THEN
   REWRITE_TAC [EXTENSION; IN_ELIM] THEN
   GEN_TAC THEN
   MATCH_MP_TAC (TAUT `!x y. (x ==> y) ==> (x /\ y <=> x)`) THEN
   MATCH_ACCEPT_TAC FUN_IN_IMAGE;
   MATCH_ACCEPT_TAC FINITE_IMAGE]);;

export_thm FINITE_IMAGE_INJ_EQ;;

let FINITE_IMAGE_INJ = prove
 (`!(f:A->B) A. (!x y. (f(x) = f(y)) ==> (x = y)) /\
                FINITE A ==> FINITE {x | f(x) IN A}`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`f:A->B`; `A:B set`; `UNIV:A set`]
    FINITE_IMAGE_INJ_GENERAL) THEN REWRITE_TAC[IN_UNIV]);;

export_thm FINITE_IMAGE_INJ;;

let INFINITE_IMAGE_INJ_EQ = prove
 (`!f:A->B. (!x y. (f x = f y) ==> (x = y))
            ==> !s. INFINITE (IMAGE f s) <=> INFINITE s`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [INFINITE] THEN
  AP_TERM_TAC THEN
  MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm INFINITE_IMAGE_INJ_EQ;;

let INFINITE_IMAGE_INJ = prove
 (`!(f:A->B) s.
     (!x y. (f x = f y) ==> (x = y)) /\
     INFINITE s ==> INFINITE (IMAGE f s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `f:A->B` INFINITE_IMAGE_INJ_EQ) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (fun th -> ASM_REWRITE_TAC [th]));;

export_thm INFINITE_IMAGE_INJ;;

let INFINITE_NONEMPTY = prove
 (`!(s : A set). INFINITE(s) ==> ~(s = EMPTY)`,
  REWRITE_TAC [INFINITE; CONTRAPOS_THM] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [FINITE_EMPTY]);;

export_thm INFINITE_NONEMPTY;;

let INFINITE_DIFF_FINITE = prove
 (`!(s:A set) t. INFINITE(s) /\ FINITE(t) ==> INFINITE(s DIFF t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [INFINITE] THEN
  MATCH_MP_TAC (TAUT `(b /\ c ==> a) ==> ~a /\ b ==> ~c`) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(t:A set) UNION (s DIFF t)` THEN
  ASM_REWRITE_TAC [FINITE_UNION; SUBSET_DIFF_UNION; SUBSET_REFL]);;

export_thm INFINITE_DIFF_FINITE;;

let FINITE_SUBSET_IMAGE = prove
 (`!(f:A->B) s t.
        FINITE(t) /\ t SUBSET (IMAGE f s) <=>
        ?s'. FINITE s' /\ s' SUBSET s /\ (t = IMAGE f s')`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   EXISTS_TAC `IMAGE (\y. @x. (y = (f:A->B)(x)) /\ x IN s) t` THEN
   REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `y:B` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `?x. y = (f:A->B) x /\ x IN s` (MP_TAC o SELECT_RULE) THENL
    [UNDISCH_TAC `t SUBSET IMAGE (f:A->B) s` THEN
     REWRITE_TAC [SUBSET; IN_IMAGE] THEN
     DISCH_THEN MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     STRIP_TAC];
    REWRITE_TAC [GSYM IMAGE_o] THEN
    REWRITE_TAC [EXTENSION; IN_IMAGE; o_THM] THEN
    X_GEN_TAC `y:B` THEN
    EQ_TAC THENL
    [STRIP_TAC THEN
     EXISTS_TAC `y:B` THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN `?x. y = (f:A->B) x /\ x IN s` (MP_TAC o SELECT_RULE) THENL
     [UNDISCH_TAC `t SUBSET IMAGE (f:A->B) s` THEN
      REWRITE_TAC [SUBSET; IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      STRIP_TAC];
     STRIP_TAC THEN
     FIRST_X_ASSUM SUBST_VAR_TAC THEN
     SUBGOAL_THEN `?x. x' = (f:A->B) x /\ x IN s` (MP_TAC o SELECT_RULE) THENL
     [UNDISCH_TAC `t SUBSET IMAGE (f:A->B) s` THEN
      REWRITE_TAC [SUBSET; IN_IMAGE] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      SPEC_TAC (`@x. x' = (f:A->B) x /\ x IN s`,`x:A`) THEN
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `x':B IN t` THEN
      ASM_REWRITE_TAC []]]];
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC IMAGE_SUBSET THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm FINITE_SUBSET_IMAGE;;

let EXISTS_FINITE_SUBSET_IMAGE = prove
 (`!p (f:A->B) s.
    (?t. FINITE t /\ t SUBSET IMAGE f s /\ p t) <=>
    (?t. FINITE t /\ t SUBSET s /\ p (IMAGE f t))`,
  REWRITE_TAC[FINITE_SUBSET_IMAGE; CONJ_ASSOC] THEN
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   EXISTS_TAC `s' : A set` THEN
   ASM_REWRITE_TAC [];
   EXISTS_TAC `IMAGE (f : A -> B) t` THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `t : A set` THEN
   ASM_REWRITE_TAC []]);;

export_thm EXISTS_FINITE_SUBSET_IMAGE;;

let FINITE_SUBSET_IMAGE_IMP = prove
 (`!(f:A->B) s t.
        FINITE(t) /\ t SUBSET (IMAGE f s)
        ==> ?s'. FINITE s' /\ s' SUBSET s /\ t SUBSET (IMAGE f s')`,
  REWRITE_TAC [FINITE_SUBSET_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  EXISTS_TAC `s' : A set` THEN
  ASM_REWRITE_TAC [SUBSET_REFL]);;

export_thm FINITE_SUBSET_IMAGE_IMP;;

let FINITE_DIFF = prove
 (`!(s : A set) t. FINITE s ==> FINITE(s DIFF t)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s : A set` THEN
  ASM_REWRITE_TAC [DIFF_SUBSET]);;

export_thm FINITE_DIFF;;

let FINITE_RESTRICT = prove
 (`!(s:A set) P. FINITE s ==> FINITE {x | x IN s /\ P x}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s : A set` THEN
  ASM_REWRITE_TAC [SUBSET; IN_ELIM] THEN
  REPEAT STRIP_TAC);;

export_thm FINITE_RESTRICT;;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_STRONG = prove
 (`!p : A set -> bool.
     p {} /\ (!x s. p s /\ ~(x IN s) /\ FINITE s ==> p (x INSERT s)) ==>
     !s. FINITE s ==> p s`,
  GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!s:A set. FINITE s ==> FINITE s /\ p s` MP_TAC THENL
  [MATCH_MP_TAC FINITE_INDUCT THEN
   ASM_REWRITE_TAC [FINITE_EMPTY; FINITE_INSERT] THEN
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   ASM_CASES_TAC `x:A IN s` THENL
   [MP_TAC (SPECL [`x:A`; `s:A set`] ABSORPTION) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (fun th -> ASM_REWRITE_TAC [th]);
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `s : A set`) THEN
   ASM_REWRITE_TAC []]);;

export_thm FINITE_INDUCT_STRONG;;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

logfile "set-fold-def";;

let FINREC = new_recursive_definition num_RECURSION
  `(!f b s a. FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\ (a = b)) /\
   (!f b s a n. FINREC (f:A->B->B) b s a (SUC n) <=>
                ?x c. x IN s /\
                      FINREC f b (s DELETE x) c n  /\
                      (a = f x c))`;;

let FINREC_1_LEMMA = prove
 (`!(f:A->B->B) b s a.
    FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\ (a = f x b)`,
  REWRITE_TAC [FINREC] THEN
  REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  REWRITE_TAC
    [EXTENSION; IN_DELETE; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `x':A`) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     UNDISCH_TAC `~((x':A) IN s)` THEN
     ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC []];
    ASM_REWRITE_TAC []];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `b:B` THEN
   ASM_REWRITE_TAC [] THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [DISJ_SYM] THEN
   MATCH_ACCEPT_TAC EXCLUDED_MIDDLE]);;

let FINREC_SUC_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n s z.
                FINREC f b s z (SUC n)
                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\
                                       (z = f x w)`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [FINREC_1_LEMMA] THEN
   REWRITE_TAC [FINREC] THEN
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `b:B` THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC
     [EXTENSION; IN_DELETE; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [DISJ_SYM] THEN
   MATCH_ACCEPT_TAC EXCLUDED_MIDDLE;
   REPEAT GEN_TAC THEN
   GEN_REWRITE_TAC LAND_CONV [FINREC] THEN
   DISCH_THEN (X_CHOOSE_THEN `y:A` MP_TAC) THEN
   DISCH_THEN (X_CHOOSE_THEN `c:B` STRIP_ASSUME_TAC) THEN
   X_GEN_TAC `x:A` THEN
   DISCH_TAC THEN
   ASM_CASES_TAC `x:A = y` THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    EXISTS_TAC `c:B` THEN
    ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    UNDISCH_TAC `FINREC (f:A->B->B) b (s DELETE y) c (SUC n)` THEN
    DISCH_THEN
      (fun th ->
         FIRST_X_ASSUM (fun th' -> MP_TAC (SPEC `x:A` (MATCH_MP th' th)))) THEN
    ASM_REWRITE_TAC [IN_DELETE] THEN
    DISCH_THEN (X_CHOOSE_THEN `v:B` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(f:A->B->B) y v` THEN
    ASM_REWRITE_TAC [FINREC] THEN
    CONJ_TAC THENL
    [MAP_EVERY EXISTS_TAC [`y:A`; `v:B`] THEN
     ONCE_REWRITE_TAC [DELETE_COMM] THEN
     ASM_REWRITE_TAC [IN_DELETE];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]]]]);;

let FINREC_UNIQUE_LEMMA = prove
 (`!(f:A->B->B) b.
         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
         ==> !n1 n2 s a1 a2.
                FINREC f b s a1 n1 /\ FINREC f b s a2 n2
                ==> (a1 = a2) /\ (n1 = n2)`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  INDUCT_TAC THENL
  [INDUCT_TAC THENL
   [REWRITE_TAC [FINREC] THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [FINREC; NOT_SUC] THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC (TAUT `!x y. (x ==> ~y) ==> ~(x /\ y)`) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY]];
   INDUCT_TAC THENL
   [REWRITE_TAC [FINREC; NOT_SUC] THEN
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC (TAUT `!x y. (y ==> ~x) ==> ~(x /\ y)`) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [NOT_IN_EMPTY];
    POP_ASSUM (K ALL_TAC) THEN
    REPEAT GEN_TAC THEN
    STRIP_TAC THEN
    REWRITE_TAC [SUC_INJ] THEN
    UNDISCH_TAC `FINREC (f:A->B->B) b s a1 (SUC n1)` THEN
    REWRITE_TAC [FINREC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPECL [`f:A->B->B`; `b:B`] FINREC_SUC_LEMMA) THEN
    DISCH_THEN
      (fun th -> FIRST_X_ASSUM (fun th' -> MP_TAC (MATCH_MP th th'))) THEN
    DISCH_THEN
      (fun th -> FIRST_X_ASSUM (fun th' -> MP_TAC (MATCH_MP th th'))) THEN
    DISCH_THEN
      (fun th -> FIRST_ASSUM (fun th' -> MP_TAC (MATCH_MP th th'))) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    SUBGOAL_THEN `(c:B) = w /\ (n1:num) = n2` (fun th -> REWRITE_TAC [th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `s DELETE (x:A)` THEN
    ASM_REWRITE_TAC []]]);;

let FINREC_EXISTS_LEMMA = prove
 (`!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`b:B`; `0`] THEN REWRITE_TAC[FINREC];
    MAP_EVERY EXISTS_TAC [`(f:A->B->B) x a`; `SUC n`] THEN
    REWRITE_TAC[FINREC] THEN MAP_EVERY EXISTS_TAC [`x:A`; `a:B`] THEN
    MP_TAC (SPECL [`x:A`; `s : A set`] DELETE_INSERT_NON_ELEMENT) THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN
    DISCH_THEN (fun th -> ASM_REWRITE_TAC [th])]);;

let FINREC_FUN_LEMMA = prove
 (`!P (R:A->B->C->bool).
       (!s. P s ==> ?a n. R s a n) /\
       (!n1 n2 s a1 a2. R s a1 n1 /\ R s a2 n2 ==> (a1 = a2) /\ (n1 = n2))
       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `\s:A. @a:B. ?n:C. R s a n` THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `s : A`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SELECT_RULE) THEN
  SPEC_TAC (`@a. ?n. (R:A->B->C->bool) s a n`,`a':B`) THEN
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   SUBGOAL_THEN `(a':B) = a /\ (n:C) = n'` (fun th -> REWRITE_TAC [th]) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `s:A` THEN
   ASM_REWRITE_TAC [];
   DISCH_THEN SUBST_VAR_TAC THEN
   EXISTS_TAC `n:C` THEN
   FIRST_ASSUM ACCEPT_TAC]);;

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
  DISCH_THEN(X_CHOOSE_TAC `g:(A set)->B`) THEN
  EXISTS_TAC `g:(A set)->B` THEN CONJ_TAC THENL
  [POP_ASSUM (MP_TAC o SPECL [`EMPTY : A set`; `b : B`]) THEN
   ASM_REWRITE_TAC [FINITE_EMPTY] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
   EXISTS_TAC `0` THEN
   REWRITE_TAC [FINREC];
   REPEAT STRIP_TAC THEN
   FIRST_ASSUM (MP_TAC o SPECL [`s : A set`; `(g:(A set)->B) s`]) THEN
   MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [LEFT_IMP_EXISTS_THM] THEN
   INDUCT_TAC THENL
   [ASM_REWRITE_TAC[FINREC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    UNDISCH_TAC `(x:A) IN s` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY];
    POP_ASSUM (K ALL_TAC) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (fun th -> MP_TAC (MATCH_MP FINREC_SUC_LEMMA th)) THEN
    FIRST_X_ASSUM
      (fun th -> DISCH_THEN (fun th' -> MP_TAC (MATCH_MP th' th))) THEN
    FIRST_X_ASSUM
      (fun th -> DISCH_THEN (fun th' -> MP_TAC (MATCH_MP th' th))) THEN
    STRIP_TAC THEN
    POP_ASSUM SUBST1_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`s DELETE (x:A)`; `w:B`]) THEN
    ASM_REWRITE_TAC [FINITE_DELETE] THEN
    DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
    EXISTS_TAC `n:num` THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

let SET_RECURSION_LEMMA = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> ?g. (g {} = b) /\
                !x s. FINITE s
                      ==> (g (x INSERT s) =
                                if x IN s then g s else f x (g s))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `b:B` o MATCH_MP FINREC_FUN) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(A set)->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:(A set)->B` THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   AP_TERM_TAC THEN REWRITE_TAC [GSYM ABSORPTION] THEN ASM_REWRITE_TAC[];
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `FINITE (x:A INSERT s) /\ x IN (x INSERT s)` MP_TAC THENL
   [ASM_REWRITE_TAC [FINITE_INSERT; IN_INSERT];
    DISCH_THEN
      (fun th -> FIRST_X_ASSUM (fun th' -> SUBST1_TAC (MATCH_MP th' th))) THEN
    REPEAT AP_TERM_TAC THEN
    ASM_REWRITE_TAC [DELETE_INSERT_NON_ELEMENT]]]);;

let ITSET = new_definition
  `!(f:A->B->B) b s.
     ITSET f b s =
        (@g. (g {} = b) /\
             !x s. FINITE s
                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))
        s`;;

let FINITE_RECURSION = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f b {} = b) /\
            !x s. FINITE s
                  ==> (ITSET f b (x INSERT s) =
                       if x IN s then ITSET f b s
                                 else f x (ITSET f b s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ITSET] THEN
  CONV_TAC SELECT_CONV THEN MATCH_MP_TAC SET_RECURSION_LEMMA THEN
  ASM_REWRITE_TAC[]);;

export_thm FINITE_RECURSION;;

logfile "set-fold-thm";;

let FINITE_RECURSION_DELETE = prove
 (`!(f:A->B->B) b.
        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))
        ==> (ITSET f b {} = b) /\
            !x s. FINITE s
                  ==> (ITSET f b s =
                       if x IN s then f x (ITSET f b (s DELETE x))
                                 else ITSET f b (s DELETE x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP FINITE_RECURSION) THEN
  DISCH_THEN (STRIP_ASSUME_TAC o SPEC `b:B`) THEN
  ASM_REWRITE_TAC [] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A IN s` THENL
  [ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o MATCH_MP FINITE_DELETE_IMP) THEN
   DISCH_THEN
     (fun th ->
        FIRST_X_ASSUM
          (fun th' -> MP_TAC (SPEC `x:A` (MATCH_MP th' (SPEC `x:A` th))))) THEN
    REWRITE_TAC [IN_DELETE] THEN
    MATCH_MP_TAC (TAUT `!x y. (x <=> y) ==> (x ==> y)`) THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC INSERT_DELETE THEN
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC [] THEN
    DISCH_TAC THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    ASM_REWRITE_TAC [DELETE_NON_ELEMENT]]);;

export_thm FINITE_RECURSION_DELETE;;

let ITSET_EQ = prove
 (`!(f:A->B->B) g b s.
             FINITE(s) /\ (!x. x IN s ==> (f x = g x)) /\
             (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\
             (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))
             ==> (ITSET f b s = ITSET g b s)`,
  GEN_TAC THEN
  GEN_TAC THEN
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  ONCE_REWRITE_TAC [IMP_CONJ] THEN
  ONCE_REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
  [MP_TAC (SPECL [`f:A->B->B`; `b:B`] FINITE_RECURSION) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
   MP_TAC (SPECL [`g:A->B->B`; `b:B`] FINITE_RECURSION) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o CONJUNCT1) THEN
   REFL_TAC;
   MP_TAC (SPECL [`f:A->B->B`; `b:B`] FINITE_RECURSION) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`x:A`; `s:A set`] o CONJUNCT2) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`g:A->B->B`; `b:B`] FINITE_RECURSION) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (MP_TAC o SPECL [`x:A`; `s:A set`] o CONJUNCT2) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`b:B`]) THEN
   ANTS_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [IN_INSERT];
    DISCH_THEN SUBST1_TAC THEN
    AP_THM_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [IN_INSERT]]]);;

export_thm ITSET_EQ;;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-def";;

let CARD = new_definition
 `CARD = ITSET (\ (x:A) n. SUC n) 0`;;

export_thm CARD;;

logfile "set-size-thm";;

let (CARD_EMPTY,CARD_INSERT) = (CONJ_PAIR o prove)
 (`(CARD ({}:A set) = 0) /\
   (!(x:A) s. FINITE s ==>
                 (CARD (x INSERT s) =
                      if x IN s then CARD s else SUC(CARD s)))`,
  MP_TAC(ISPECL [`\(x:A) n. SUC n`; `0`] FINITE_RECURSION) THEN
  REWRITE_TAC[CARD]);;

export_thm CARD_EMPTY;;
export_thm CARD_INSERT;;

let CARD_CLAUSES = CONJ CARD_EMPTY CARD_INSERT;;

let CARD_SING = prove
 (`!(x:A). CARD (x INSERT EMPTY) = 1`,
  GEN_TAC THEN
  MP_TAC (SPECL [`x:A`; `EMPTY : A set`] CARD_INSERT) THEN
  REWRITE_TAC [FINITE_EMPTY; NOT_IN_EMPTY; CARD_EMPTY; ONE]);;

export_thm CARD_SING;;

let CARD_UNION = prove
 (`!(s:A set) t. FINITE(s) /\ FINITE(t) /\ DISJOINT s t
         ==> (CARD (s UNION t) = CARD s + CARD t)`,
  REWRITE_TAC[TAUT `a /\ b /\ c ==> d <=> a ==> b /\ c ==> d`] THEN
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNION_EMPTY; CARD_CLAUSES; ADD; DISJOINT_INSERT] THEN
  X_GEN_TAC `x:A` THEN X_GEN_TAC `s:A set` THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [INSERT_UNION] THEN
  MP_TAC (SPECL [`x:A`; `s:A set`] CARD_INSERT) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  MP_TAC (SPECL [`x:A`; `(s:A set) UNION t`] CARD_INSERT) THEN
  ASM_REWRITE_TAC [FINITE_UNION; IN_UNION] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [ADD] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm CARD_UNION;;

let CARD_DELETE = prove
 (`!x:A s. FINITE(s)
           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [MP_TAC (SPECL [`x:A`; `s : A set`] INSERT_DELETE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN
      (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th]))) THEN
    MP_TAC (SPECL [`x:A`; `s DELETE (x:A)`] CARD_INSERT) THEN
    ASM_REWRITE_TAC [FINITE_DELETE; IN_DELETE] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [ADD1; ADD_SUB];
    AP_TERM_TAC THEN
    ASM_REWRITE_TAC [DELETE_NON_ELEMENT]]);;

export_thm CARD_DELETE;;

let CARD_UNION_EQ = prove
 (`!(s:A set) t u.
     FINITE u /\ DISJOINT s t /\ (s UNION t = u)
           ==> (CARD s + CARD t = CARD u)`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC CARD_UNION THEN
  ASM_REWRITE_TAC [GSYM FINITE_UNION]);;

export_thm CARD_UNION_EQ;;

let CARD_DIFF = prove
 (`!(s:A set) t. FINITE s /\ t SUBSET s ==> CARD (s DIFF t) = CARD s - CARD t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!(a:num) b c. a + b = c ==> a = c - b` MATCH_MP_TAC THENL
  [REPEAT GEN_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [ADD_SUB];
   MATCH_MP_TAC CARD_UNION_EQ THEN
   ASM_REWRITE_TAC [GSYM DISJOINT_DIFF; DIFF_DIFF; DIFF_UNION_CANCEL] THEN
   ONCE_REWRITE_TAC [UNION_COMM] THEN
   ASM_REWRITE_TAC [GSYM SUBSET_UNION_ABSORPTION]]);;

export_thm CARD_DIFF;;

let CARD_EQ_0 = prove
 (`!(s:A set). FINITE s ==> ((CARD s = 0) <=> (s = {}))`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC [CONJUNCT1 CARD_CLAUSES; NOT_INSERT_EMPTY] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`x:A`; `s:A set`] CARD_INSERT) THEN
  ASM_REWRITE_TAC [NOT_SUC]);;

export_thm CARD_EQ_0;;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let FINITE_INDUCT_DELETE = prove
 (`!p.
     p {} /\
     (!s. FINITE s /\ ~(s = {}) ==> ?x. x IN s /\ (p (s DELETE x) ==> p s)) ==>
     !s : A set. FINITE s ==> p s`,
  GEN_TAC THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  SUBGOAL_THEN `!n (s:A set). FINITE s ==> CARD s = n ==> p s`
    (fun th ->
       MP_TAC (SPECL [`CARD (s : A set)`; `s : A set`] th) THEN
       REWRITE_TAC []) THEN
  INDUCT_TAC THENL
  [GEN_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `s : A set` CARD_EQ_0) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   GEN_TAC THEN
   STRIP_TAC THEN
   ASM_CASES_TAC `(s : A set) = {}` THENL
   [ASM_REWRITE_TAC [CARD_EMPTY; NOT_SUC];
    FIRST_X_ASSUM
      (fun th ->
         MP_TAC (SPEC `s : A set` th) THEN
         ANTS_TAC THENL
         [CONJ_TAC THEN
          FIRST_ASSUM ACCEPT_TAC;
          ALL_TAC]) THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`x : A`; `s : A set`] INSERT_DELETE) THEN
    ANTS_TAC THENL
    [FIRST_ASSUM ACCEPT_TAC;
     DISCH_THEN
       (fun th ->
          CONV_TAC
            (LAND_CONV (LAND_CONV (RAND_CONV (REWR_CONV (SYM th)))))) THEN
     MP_TAC (SPECL [`x : A`; `s DELETE (x : A)`] CARD_INSERT) THEN
     ASM_REWRITE_TAC [FINITE_DELETE; IN_DELETE] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [SUC_INJ] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `s DELETE (x : A)`) THEN
     ASM_REWRITE_TAC [FINITE_DELETE]]]]);;

export_thm FINITE_INDUCT_DELETE;;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-def";;

let HAS_SIZE = new_definition
  `!(s : A set) n. s HAS_SIZE n <=> FINITE s /\ (CARD s = n)`;;

export_thm HAS_SIZE;;

logfile "set-size-thm";;

let HAS_SIZE_CARD = prove
 (`!(s:A set) n. s HAS_SIZE n ==> (CARD s = n)`,
  SIMP_TAC [HAS_SIZE]);;

export_thm HAS_SIZE_CARD;;

let HAS_SIZE_0 = prove
 (`!(s:A set). s HAS_SIZE 0 <=> (s = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC [HAS_SIZE] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   MP_TAC (SPEC `s:A set` CARD_EQ_0) THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [FINITE_EMPTY; CARD_CLAUSES]]);;

export_thm HAS_SIZE_0;;

let HAS_SIZE_SING = prove
 (`!(x:A). (x INSERT EMPTY) HAS_SIZE 1`,
  REWRITE_TAC [HAS_SIZE; FINITE_SING; CARD_SING]);;

export_thm HAS_SIZE_SING;;

let HAS_SIZE_SUC = prove
 (`!(s:A set) n. s HAS_SIZE (SUC n) <=>
                   ~(s = {}) /\ !a. a IN s ==> (s DELETE a) HAS_SIZE n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  ASM_CASES_TAC `(s:A set) = {}` THENL
  [ASM_REWRITE_TAC [FINITE_EMPTY; CARD_CLAUSES; NOT_SUC];
   ASM_REWRITE_TAC [FINITE_DELETE] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`a:A`; `s:A set`] CARD_DELETE) THEN
    ASM_REWRITE_TAC [SUC_SUB1];
    MP_TAC (SPEC `s:A set` MEMBER_NOT_EMPTY) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    DISCH_THEN (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    MP_TAC (SPECL [`x:A`; `s:A set`] CARD_DELETE) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPEC `CARD (s:A set)` num_CASES) THEN
    STRIP_TAC THENL
    [MP_TAC (SPECL [`s:A set`] CARD_EQ_0) THEN
     ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [SUC_SUB1]]]]);;

export_thm HAS_SIZE_SUC;;

let HAS_SIZE_UNION = prove
 (`!(s:A set) t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ DISJOINT s t
             ==> (s UNION t) HAS_SIZE (m + n)`,
  SIMP_TAC[HAS_SIZE; FINITE_UNION; DISJOINT; CARD_UNION]);;

export_thm HAS_SIZE_UNION;;

let HAS_SIZE_DIFF = prove
 (`!(s:A set) t m n. s HAS_SIZE m /\ t HAS_SIZE n /\ t SUBSET s
             ==> (s DIFF t) HAS_SIZE (m - n)`,
  SIMP_TAC[HAS_SIZE; FINITE_DIFF; CARD_DIFF]);;

export_thm HAS_SIZE_DIFF;;

let HAS_SIZE_UNIONS = prove
 (`!s t:(A->B set) m n.
        s HAS_SIZE m /\
        (!x. x IN s ==> t(x) HAS_SIZE n) /\
        (!x y. x IN s /\ y IN s /\ ~(x = y) ==> DISJOINT (t x) (t y))
        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN REWRITE_TAC[CARD_CLAUSES] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) (K ALL_TAC)) THEN
   REWRITE_TAC[MULT_CLAUSES; HAS_SIZE_0; EMPTY_UNIONS] THEN
   REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
   MAP_EVERY X_GEN_TAC [`y:A`; `s:A set`] THEN STRIP_TAC THEN
   MAP_EVERY X_GEN_TAC [`t:A->B set`; `m:num`; `n:num`] THEN
   ASM_SIMP_TAC[CARD_CLAUSES] THEN
   DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) STRIP_ASSUME_TAC) THEN
   SUBGOAL_THEN
     `{(t:A->B set) x' | x' IN y INSERT s} =
      t y INSERT {t x | x IN s}` SUBST1_TAC THENL
   [REWRITE_TAC [EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    GEN_TAC THEN
    EQ_TAC THENL
    [REPEAT STRIP_TAC THENL
     [DISJ1_TAC THEN
      FIRST_X_ASSUM (SUBST_VAR_TAC o SYM) THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC []];
     REPEAT STRIP_TAC THENL
     [EXISTS_TAC `y:A` THEN
      ASM_REWRITE_TAC [];
      EXISTS_TAC `x':A` THEN
      ASM_REWRITE_TAC []]];
    REWRITE_TAC [UNIONS_INSERT] THEN
    REWRITE_TAC [MULT] THEN
    ONCE_REWRITE_TAC [ADD_SYM] THEN
    MATCH_MP_TAC HAS_SIZE_UNION THEN ASM_SIMP_TAC[IN_INSERT] THEN
    REWRITE_TAC [DISJOINT_UNIONS; IN_ELIM_THM] THEN
    GEN_TAC THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN
    DISCH_THEN SUBST_VAR_TAC THEN
    UNDISCH_TAC `(x':A) IN s` THEN
    ASM_REWRITE_TAC []]]);;

export_thm HAS_SIZE_UNIONS;;

let FINITE_HAS_SIZE = prove
 (`!(s:A set). FINITE s <=> s HAS_SIZE CARD s`,
  REWRITE_TAC[HAS_SIZE]);;

export_thm FINITE_HAS_SIZE;;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_INSERT = prove
 (`(!s n. (s:A set) HAS_SIZE (SUC n) <=>
        ?a t. t HAS_SIZE n /\ ~(a IN t) /\ (s = a INSERT t))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
    STRIP_TAC THEN
    POP_ASSUM
      (fun th ->
         FIRST_ASSUM (fun th' -> STRIP_ASSUME_TAC (MATCH_MP th th'))) THEN
    EXISTS_TAC `x:A` THEN
    EXISTS_TAC `s DELETE (x:A)` THEN
    ASM_REWRITE_TAC [IN_DELETE] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC INSERT_DELETE THEN
    FIRST_ASSUM ACCEPT_TAC;
    SIMP_TAC [LEFT_IMP_EXISTS_THM; HAS_SIZE; CARD_CLAUSES; FINITE_INSERT]]);;

export_thm HAS_SIZE_INSERT;;

let HAS_SIZE_CLAUSES = CONJ HAS_SIZE_0 HAS_SIZE_INSERT;;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let HAS_SIZE_CONV =
  let pth = prove
   (`(~((a:A) IN {}) /\ P <=> P) /\
     (~(a IN {b}) /\ P <=> ~(a = b) /\ P) /\
     (~(a IN (b INSERT cs)) /\ P <=> ~(a = b) /\ ~(a IN cs) /\ P)`,
    REWRITE_TAC [NOT_IN_EMPTY; IN_INSERT; DE_MORGAN_THM; CONJ_ASSOC])
  and qth = prove
   (`((?s. s HAS_SIZE 0 /\ P s) <=> P {}) /\
     ((?s. s HAS_SIZE (SUC n) /\ P s) <=>
      (?(a:A) s. s HAS_SIZE n /\ ~(a IN s) /\ P(a INSERT s)))`,
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
 (`!(a:A set) b. FINITE b /\ a SUBSET b /\ (CARD a = CARD b) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_REWRITE_TAC [] THEN
  REWRITE_TAC [GSYM DIFF_EMPTY_SUBSET; GSYM HAS_SIZE_0; HAS_SIZE] THEN
  SUBGOAL_THEN `FINITE((b:A set) DIFF a)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_DIFF THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD (b:A set) - CARD (a:A set)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_DIFF THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [SUB_REFL]]);;

export_thm CARD_SUBSET_EQ;;

let CARD_SUBSET = prove
 (`!(a:A set) b. a SUBSET b /\ FINITE(b) ==> CARD(a) <= CARD(b)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a UNION (b DIFF a) = (b:A set)` (SUBST1_TAC o SYM) THENL
  [ASM_REWRITE_TAC [UNION_DIFF_SUBSET];
   REWRITE_TAC [LE_EXISTS] THEN
   EXISTS_TAC `CARD (b DIFF (a:A set))` THEN
   MATCH_MP_TAC CARD_UNION THEN
   REWRITE_TAC [DISJOINT_DIFF2] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `b : A set` THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC FINITE_DIFF THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm CARD_SUBSET;;

let CARD_SUBSET_LE = prove
 (`!(a:A set) b. FINITE b /\ a SUBSET b /\ (CARD b <= CARD a) ==> (a = b)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CARD_SUBSET_EQ THEN
  ASM_REWRITE_TAC [GSYM LE_ANTISYM] THEN
  MATCH_MP_TAC CARD_SUBSET THEN
  ASM_REWRITE_TAC []);;

export_thm CARD_SUBSET_LE;;

let SUBSET_CARD_EQ = prove
 (`!(s:A set) t. FINITE t /\ s SUBSET t ==> (CARD s = CARD t <=> s = t)`,
  REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
  [MATCH_MP_TAC CARD_SUBSET_EQ THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC []]);;

export_thm SUBSET_CARD_EQ;;

let CARD_PSUBSET = prove
 (`!(a:A set) b. a PSUBSET b /\ FINITE(b) ==> CARD(a) < CARD(b)`,
  REWRITE_TAC [PSUBSET; LT_LE] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC CARD_SUBSET THEN
   ASM_REWRITE_TAC [];
   UNDISCH_TAC `~((a:A set) = b)` THEN
   REWRITE_TAC [] THEN
   MATCH_MP_TAC CARD_SUBSET_EQ THEN
   ASM_REWRITE_TAC []]);;

export_thm CARD_PSUBSET;;

let CARD_UNION_DIFF = prove
 (`!s (t : A set).
     FINITE s /\ FINITE t ==> CARD (s UNION t) = CARD s + CARD (t DIFF s)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_REWRITE_TAC [FINITE_UNION; DISJOINT_DIFF2] THEN
  REWRITE_TAC [EXTENSION; IN_UNION; IN_DIFF] THEN
  GEN_TAC THEN
  BOOL_CASES_TAC `(x:A) IN s` THEN
  REWRITE_TAC []);;

export_thm CARD_UNION_DIFF;;

let CARD_UNION_INTER = prove
 (`!(s : A set) t.
     FINITE s /\ FINITE t ==>
     CARD (s UNION t) + CARD (s INTER t) = CARD s + CARD t`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`s:A set`; `t:A set`] CARD_UNION_DIFF) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [EQ_ADD_LCANCEL; GSYM ADD_ASSOC] THEN
  MATCH_MP_TAC CARD_UNION_EQ THEN
  ASM_REWRITE_TAC [] THEN
  CONJ_TAC THENL
  [REWRITE_TAC [DISJOINT; EXTENSION; IN_DIFF; IN_INTER; NOT_IN_EMPTY] THEN
   GEN_TAC THEN
   BOOL_CASES_TAC `(x:A) IN s` THEN
   REWRITE_TAC [];
   REWRITE_TAC [EXTENSION; IN_DIFF; IN_UNION; IN_INTER] THEN
   GEN_TAC THEN
   BOOL_CASES_TAC `(x:A) IN s` THEN
   REWRITE_TAC []]);;

export_thm CARD_UNION_INTER;;

let CARD_UNION_LE = prove
 (`!s (t : A set).
     FINITE s /\ FINITE t ==> CARD (s UNION t) <= CARD(s) + CARD(t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [LE_EXISTS] THEN
  EXISTS_TAC `CARD ((s : A set) INTER t)` THEN
  MATCH_MP_TAC EQ_SYM THEN
  MATCH_MP_TAC CARD_UNION_INTER THEN
  ASM_REWRITE_TAC []);;

export_thm CARD_UNION_LE;;

let CARD_UNIONS_LE = prove
 (`!s (t:A->(B set)) m n.
        s HAS_SIZE m /\ (!x. x IN s ==> FINITE (t x) /\ CARD (t x) <= n)
        ==> CARD (UNIONS {t x | x IN s}) <= m * n`,
  REWRITE_TAC [SIMPLE_IMAGE; HAS_SIZE; GSYM CONJ_ASSOC] THEN
  ONCE_REWRITE_TAC[IMP_CONJ] THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
  [REWRITE_TAC [IMAGE_CLAUSES; UNIONS_0; CARD_CLAUSES; LE_0];
   REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
   ASM_SIMP_TAC [CARD_CLAUSES; FINITE_RULES] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) ASSUME_TAC) THEN
   REWRITE_TAC [IMAGE_CLAUSES; UNIONS_INSERT; MULT] THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `CARD ((t : A -> B set) x) + CARD (UNIONS (IMAGE t s))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC CARD_UNION_LE THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
     REWRITE_TAC [IN_INSERT] THEN
     DISCH_THEN (ACCEPT_TAC o CONJUNCT1);
     ASM_SIMP_TAC [FINITE_FINITE_UNIONS; FINITE_IMAGE] THEN
     X_GEN_TAC `y : B set` THEN
     REWRITE_TAC [IN_IMAGE] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM SUBST_VAR_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `x' : A`) THEN
     ASM_REWRITE_TAC [IN_INSERT] THEN
     DISCH_THEN (ACCEPT_TAC o CONJUNCT1)];
    MATCH_MP_TAC LE_ADD2 THEN
    CONJ_TAC THENL
    [FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
     REWRITE_TAC [IN_INSERT] THEN
     DISCH_THEN (ACCEPT_TAC o CONJUNCT2);
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [] THEN
     GEN_TAC THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [IN_INSERT]]]]);;

export_thm CARD_UNIONS_LE;;

let CARD_UNION_GEN = prove
 (`!(s : A set) t.
     FINITE s /\ FINITE t ==>
     CARD (s UNION t) = (CARD(s) + CARD(t)) - CARD (s INTER t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`s : A set`; `t : A set`] CARD_UNION_INTER) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [ADD_SUB]);;

export_thm CARD_UNION_GEN;;

let CARD_UNION_OVERLAP_EQ = prove
 (`!(s : A set) t.
     FINITE s /\ FINITE t ==>
     (CARD (s UNION t) = CARD s + CARD t <=> DISJOINT s t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC [GSYM CARD_UNION_INTER] THEN
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
  REWRITE_TAC [EQ_ADD_LCANCEL_0; DISJOINT] THEN
  MATCH_MP_TAC CARD_EQ_0 THEN
  MATCH_MP_TAC FINITE_INTER THEN
  ASM_REWRITE_TAC []);;

export_thm CARD_UNION_OVERLAP_EQ;;

let CARD_UNION_OVERLAP = prove
 (`!(s:A set) t.
     FINITE s /\ FINITE t /\ CARD (s UNION t) < CARD(s) + CARD(t) ==>
     ~(DISJOINT s t)`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC [GSYM CARD_UNION_OVERLAP_EQ] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `CARD ((s : A set) UNION t) < CARD s + CARD t` THEN
  ASM_REWRITE_TAC [LT_REFL]);;

export_thm CARD_UNION_OVERLAP;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let CARD_IMAGE_INJ = prove
 (`!(f:A->B) s.
     (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\
     FINITE s ==>
     (CARD (IMAGE f s) = CARD s)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [CONJ_SYM] THEN
  ONCE_REWRITE_TAC [IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REWRITE_TAC [IMAGE_CLAUSES; CARD_CLAUSES];
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [IMAGE_CLAUSES] THEN
   ASM_SIMP_TAC [CARD_CLAUSES; FINITE_IMAGE] THEN
   COND_CASES_TAC THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [IN_IMAGE] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`x:A`; `x':A`]) THEN
    ASM_REWRITE_TAC [IN_INSERT] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `~((x:A) IN s)` THEN
    ASM_REWRITE_TAC [];
    REWRITE_TAC [SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [IN_INSERT]]]);;

export_thm CARD_IMAGE_INJ;;

let HAS_SIZE_IMAGE_INJ = prove
 (`!(f:A->B) s n.
     (!x y. x IN s /\ y IN s /\ (f(x) = f(y)) ==> (x = y)) /\ s HAS_SIZE n ==>
     (IMAGE f s) HAS_SIZE n`,
  REWRITE_TAC [HAS_SIZE] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE THEN
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MATCH_MP_TAC CARD_IMAGE_INJ THEN
   CONJ_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm HAS_SIZE_IMAGE_INJ;;

let CARD_IMAGE_LE = prove
 (`!(f:A->B) s. FINITE s ==> CARD (IMAGE f s) <= CARD s`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REWRITE_TAC [IMAGE_CLAUSES; CARD_CLAUSES; LE_0];
   REPEAT STRIP_TAC THEN
   ASM_SIMP_TAC [IMAGE_CLAUSES; CARD_CLAUSES; FINITE_IMAGE] THEN
   COND_CASES_TAC THENL
   [MATCH_MP_TAC LT_IMP_LE THEN
    ASM_REWRITE_TAC [GSYM LE_SUC_LT; LE_SUC];
    ASM_REWRITE_TAC [LE_SUC]]]);;

export_thm CARD_IMAGE_LE;;

let CARD_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s t.
        FINITE s /\
        (!x. x IN s ==> f(x) IN t) /\
        (!y. y IN t ==> ?!x. x IN s /\ f(x) = y)
        ==> CARD t = CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_VAR_TAC THENL
  [REWRITE_TAC [EXTENSION; IN_IMAGE] THEN
   GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x:B`) THEN
    ASM_REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    STRIP_TAC THEN
    EXISTS_TAC `x':A` THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   MATCH_MP_TAC CARD_IMAGE_INJ THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) y`) THEN
   MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [EXISTS_UNIQUE_DEF] THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC []]]);;

export_thm CARD_IMAGE_INJ_EQ;;

let CARD_SUBSET_IMAGE = prove
 (`!(f:A->B) s t. FINITE t /\ s SUBSET IMAGE f t ==> CARD s <= CARD t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (f:A->B) t)` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC CARD_SUBSET THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC FINITE_IMAGE THEN
   FIRST_ASSUM ACCEPT_TAC;
   MATCH_MP_TAC CARD_IMAGE_LE THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm CARD_SUBSET_IMAGE;;

let HAS_SIZE_IMAGE_INJ_EQ = prove
 (`!(f:A->B) s n.
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) ==>
     ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  MATCH_MP_TAC(TAUT
   `(a' <=> a) /\ (a ==> (b' <=> b)) ==> (a' /\ b' <=> a /\ b)`) THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
   FIRST_ASSUM ACCEPT_TAC;
   DISCH_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   MATCH_MP_TAC CARD_IMAGE_INJ THEN
   ASM_REWRITE_TAC[]]);;

export_thm HAS_SIZE_IMAGE_INJ_EQ;;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let CHOOSE_SUBSET_STRONG = prove
 (`!(s:A set) n.
     (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [REPEAT STRIP_TAC THEN
   REWRITE_TAC[HAS_SIZE_0] THEN
   EXISTS_TAC `EMPTY : A set` THEN
   REWRITE_TAC [EMPTY_SUBSET];
   REPEAT STRIP_TAC THEN
   MP_TAC (SPEC `s : A set` SET_CASES) THEN
   STRIP_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    SUBGOAL_THEN `F` CONTR_TAC THEN
    POP_ASSUM MP_TAC THEN
    REWRITE_TAC [FINITE_EMPTY; CARD_CLAUSES; LE; NOT_SUC];
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `t : A set`) THEN
    MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
    CONJ_TAC THENL
    [STRIP_TAC THEN
     UNDISCH_TAC `FINITE ((x:A) INSERT t) ==> SUC n <= CARD (x INSERT t)` THEN
     ASM_REWRITE_TAC [FINITE_INSERT] THEN
     ASM_SIMP_TAC [CARD_CLAUSES] THEN
     REWRITE_TAC [LE_SUC];
     STRIP_TAC THEN
     EXISTS_TAC `(x:A) INSERT t'` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC [INSERT_SUBSET; IN_INSERT] THEN
      MATCH_MP_TAC SUBSET_INSERT_IMP THEN
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC [HAS_SIZE_CLAUSES] THEN
      EXISTS_TAC `x:A` THEN
      EXISTS_TAC `t' : A set` THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `t' SUBSET (t : A set)` THEN
      REWRITE_TAC [SUBSET; NOT_FORALL_THM] THEN
      EXISTS_TAC `x:A` THEN
      ASM_REWRITE_TAC []]]]]);;

export_thm CHOOSE_SUBSET_STRONG;;

let CHOOSE_SUBSET = prove
 (`!(s : A set) n. FINITE s /\ n <= CARD s ==> ?t. t SUBSET s /\ t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`s : A set`; `n : num`] CHOOSE_SUBSET_STRONG) THEN
  ASM_REWRITE_TAC []);;

export_thm CHOOSE_SUBSET;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let EMPTY_PRODUCT_DEPENDENT = prove
 (`!(t : A -> B set). { (x,y) | x IN {} /\ y IN t x } = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [NOT_IN_EMPTY] THEN
  REWRITE_TAC [EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY]);;

export_thm EMPTY_PRODUCT_DEPENDENT;;

let INSERT_PRODUCT_DEPENDENT = prove
 (`!(s : A set) (t : A -> B set) a.
     { (x,y) | x IN a INSERT s /\ y IN t x } =
     IMAGE ((,) a) (t a) UNION { (x,y) | x IN s /\ y IN t x }`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION] THEN
  X_GEN_TAC `p : A # B` THEN
  MP_TAC (ISPEC `p : A # B` PAIR_SURJECTIVE) THEN
  DISCH_THEN (X_CHOOSE_THEN `u : A` (X_CHOOSE_THEN `v : B` SUBST_VAR_TAC)) THEN
  REWRITE_TAC [IN_ELIM_PAIR_THM; IN_UNION; IN_INSERT; IN_IMAGE] THEN
  REWRITE_TAC [IN_ELIM_THM; RIGHT_OR_DISTRIB; PAIR_EQ] THEN
  AP_THM_TAC THEN
  AP_TERM_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   EXISTS_TAC `v:B` THEN
   ASM_REWRITE_TAC [];
   DISCH_THEN (X_CHOOSE_THEN `b : B` STRIP_ASSUME_TAC) THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm INSERT_PRODUCT_DEPENDENT;;

logfile "set-size-thm";;

let HAS_SIZE_PRODUCT_DEPENDENT = prove
 (`!s t m n.
     s HAS_SIZE m /\ (!x. x IN s ==> t x HAS_SIZE n) ==>
     {(x:A,y:B) | x IN s /\ y IN t x} HAS_SIZE (m * n)`,
  GEN_REWRITE_TAC (funpow 4 BINDER_CONV o funpow 2 LAND_CONV) [HAS_SIZE] THEN
  REWRITE_TAC [IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [CARD_CLAUSES; EMPTY_PRODUCT_DEPENDENT] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [HAS_SIZE_CLAUSES; MULT];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  ASM_SIMP_TAC [CARD_CLAUSES] THEN
  MP_TAC (SPEC `m : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
      SUBST_VAR_TAC
      (X_CHOOSE_THEN `m' : num` SUBST_VAR_TAC)) THENL
  [ASM_REWRITE_TAC [NOT_SUC] THEN
   NO_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [SUC_INJ] THEN
  DISCH_THEN SUBST_VAR_TAC THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [INSERT_PRODUCT_DEPENDENT] THEN
  ONCE_REWRITE_TAC [MULT_SYM] THEN
  REWRITE_TAC [MULT_SUC] THEN
  MATCH_MP_TAC HAS_SIZE_UNION THEN
  REPEAT CONJ_TAC THENL
  [MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
   CONJ_TAC THENL
   [REWRITE_TAC [PAIR_EQ] THEN
    REPEAT STRIP_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [IN_INSERT]];
   ONCE_REWRITE_TAC [MULT_SYM] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`t : A -> B set`; `CARD (s : A set)`]) THEN
   REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [IN_INSERT];
   REWRITE_TAC [DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
   X_GEN_TAC `p : A # B` THEN
   MP_TAC (ISPEC `p : A # B` PAIR_SURJECTIVE) THEN
   DISCH_THEN (X_CHOOSE_THEN `a : A` (X_CHOOSE_THEN `b : B` SUBST_VAR_TAC)) THEN
   REWRITE_TAC [IN_ELIM_PAIR_THM; IN_IMAGE; PAIR_EQ] THEN
   STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (SUBST_VAR_TAC o SYM)) THEN
   UNDISCH_TAC `~((a:A) IN s)` THEN
   ASM_REWRITE_TAC []]);;

export_thm HAS_SIZE_PRODUCT_DEPENDENT;;

logfile "set-finite-thm";;

let FINITE_PRODUCT_DEPENDENT = prove
 (`!(f:A->B->C) s t.
        FINITE s /\ (!x. x IN s ==> FINITE (t x))
        ==> FINITE {f x y | x IN s /\ y IN t x}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\ (x,y). (f:A->B->C) x y) {x,y | x IN s /\ y IN t x}` THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC FINITE_IMAGE THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`t : A -> B set`,`t : A -> B set`) THEN
   POP_ASSUM MP_TAC THEN
   SPEC_TAC (`s : A set`,`s : A set`) THEN
   MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
   CONJ_TAC THENL
   [REWRITE_TAC [EMPTY_PRODUCT_DEPENDENT; FINITE_EMPTY] THEN
    NO_TAC;
    ALL_TAC] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [INSERT_PRODUCT_DEPENDENT; FINITE_UNION] THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC [IN_INSERT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [IN_INSERT]];
  REWRITE_TAC [SUBSET; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM] THEN
  REWRITE_TAC [FORALL_IN_GSPEC] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x : A` THEN
  EXISTS_TAC `y : B` THEN
  ASM_REWRITE_TAC []]);;

export_thm FINITE_PRODUCT_DEPENDENT;;

let FINITE_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\ y IN t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (ISPECL [`(,) : A -> B -> A # B`; `s : A set`; `\x : A. t : B set`]
      FINITE_PRODUCT_DEPENDENT) THEN
  ASM_REWRITE_TAC []);;

export_thm FINITE_PRODUCT;;

logfile "set-size-thm";;

let CARD_PRODUCT = prove
 (`!s t. FINITE s /\ FINITE t
         ==> (CARD {(x:A,y:B) | x IN s /\ y IN t} = CARD s * CARD t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`s : A set`; `\x : A. t : B set`;
            `CARD (s : A set)`; `CARD (t : B set)`]
           HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_REWRITE_TAC [HAS_SIZE] THEN
  DISCH_THEN (ACCEPT_TAC o CONJUNCT2));;

export_thm CARD_PRODUCT;;

let HAS_SIZE_PRODUCT = prove
 (`!s t m n.
     s HAS_SIZE m /\ t HAS_SIZE n ==>
     {(x:A,y:B) | x IN s /\ y IN t} HAS_SIZE (m * n)`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL [`s : A set`; `\x : A. t : B set`; `m : num`; `n : num`]
           HAS_SIZE_PRODUCT_DEPENDENT) THEN
  ASM_REWRITE_TAC []);;

export_thm HAS_SIZE_PRODUCT;;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

logfile "set-def";;

let CROSS = new_definition
 `!(s : A set) (t : B set). s CROSS t = {x,y | x IN s /\ y IN t}`;;

export_thm CROSS;;

logfile "set-thm";;

let IN_CROSS = prove
 (`!(x:A) (y:B) s t. (x,y) IN (s CROSS t) <=> x IN s /\ y IN t`,
  REWRITE_TAC [CROSS; IN_ELIM_PAIR_THM]);;

export_thm IN_CROSS;;

logfile "set-size-thm";;

let HAS_SIZE_CROSS = prove
 (`!(s : A set) (t : B set) m n.
     s HAS_SIZE m /\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)`,
  REWRITE_TAC [CROSS; HAS_SIZE_PRODUCT]);;

export_thm HAS_SIZE_CROSS;;

logfile "set-finite-thm";;

let FINITE_CROSS = prove
 (`!(s : A set) (t : B set). FINITE s /\ FINITE t ==> FINITE(s CROSS t)`,
  REWRITE_TAC [CROSS; FINITE_PRODUCT]);;

export_thm FINITE_CROSS;;

logfile "set-size-thm";;

let CARD_CROSS = prove
 (`!(s : A set) (t : B set).
     FINITE s /\ FINITE t ==> CARD (s CROSS t) = CARD s * CARD t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [CROSS] THEN
  MATCH_MP_TAC CARD_PRODUCT THEN
  ASM_REWRITE_TAC []);;

export_thm CARD_CROSS;;

logfile "set-thm";;

let CROSS_EQ_EMPTY = prove
 (`!(s : A set) (t : B set). s CROSS t = {} <=> s = {} \/ t = {}`,
  REWRITE_TAC [EXTENSION; FORALL_PAIR_THM; IN_CROSS; NOT_IN_EMPTY] THEN
  REWRITE_TAC [DE_MORGAN_THM; LEFT_FORALL_OR_THM; RIGHT_FORALL_OR_THM]);;

export_thm CROSS_EQ_EMPTY;;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let EMPTY_FUNSPACE = prove
 (`!d (t : B set).
     {f | (!x. (x:A) IN {} ==> f x IN t) /\ (!x. ~(x IN {}) ==> f x = d)} =
     (\x. d) INSERT EMPTY`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_ELIM_THM; IN_SING; NOT_IN_EMPTY] THEN
  X_GEN_TAC `g : A -> B` THEN
  REWRITE_TAC [UNWIND_THM1] THEN
  REWRITE_TAC [FUN_EQ_THM]);;

export_thm EMPTY_FUNSPACE;;

let INSERT_FUNSPACE = prove
 (`!d a (s : A set) (t : B set).
    {(f:A->B) | (!x. x IN a INSERT s ==> f x IN t) /\
                (!x. ~(x IN a INSERT s) ==> (f x = d))} =
    IMAGE (\ (b,g) x. if x = a then b else g(x))
      (t CROSS
       {f | (!x. x IN s ==> f x IN t) /\
            (!x. ~(x IN s) ==> (f x = d))})`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(a:A) IN s` THENL
  [MP_TAC (SPECL [`a : A`; `s : A set`] ABSORPTION) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC
     [EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM; EXISTS_PAIR_THM;
      IN_CROSS] THEN
   X_GEN_TAC `g : A -> B` THEN
   REWRITE_TAC [UNWIND_THM1] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `(g : A -> B) a` THEN
    EXISTS_TAC `g : A -> B` THEN
    REPEAT STRIP_TAC THENL
    [REWRITE_TAC [FUN_EQ_THM] THEN
     GEN_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []];
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THENL
    [COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []];
     COND_CASES_TAC THENL
     [UNDISCH_TAC `~((x:A) IN s)` THEN
      ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []]]];
   REWRITE_TAC
     [EXTENSION; IN_IMAGE; FORALL_PAIR_THM; IN_ELIM_THM; EXISTS_PAIR_THM;
      IN_CROSS; IN_INSERT] THEN
   X_GEN_TAC `g : A -> B` THEN
   REWRITE_TAC [UNWIND_THM1] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `(g : A -> B) a` THEN
    EXISTS_TAC `\x. if x = a then d else (g : A -> B) x` THEN
    REPEAT STRIP_TAC THENL
    [REWRITE_TAC [FUN_EQ_THM] THEN
     GEN_TAC THEN
     COND_CASES_TAC THEN
     ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [];
     REWRITE_TAC [] THEN
     COND_CASES_TAC THENL
     [UNDISCH_TAC `(x:A) IN s` THEN
      ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []];
     REWRITE_TAC [] THEN
     COND_CASES_TAC THENL
     [ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []]];
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [DE_MORGAN_THM] THEN
    REPEAT STRIP_TAC THENL
    [ASM_REWRITE_TAC [];
     COND_CASES_TAC THENL
     [UNDISCH_TAC `(x:A) IN s` THEN
      ASM_REWRITE_TAC [];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []];
     ASM_REWRITE_TAC [] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []]]]);;

export_thm INSERT_FUNSPACE;;

logfile "set-finite-thm";;

let FINITE_FUNSPACE = prove
 (`!d (s : A set) (t : B set).
     FINITE s /\ FINITE t
         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\
                         (!x. ~(x IN s) ==> (f x = d))}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `FINITE (s : A set)` THEN
  SPEC_TAC (`s : A set`, `s : A set`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REWRITE_TAC [EMPTY_FUNSPACE; FINITE_SING] THEN
   NO_TAC;
   ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [INSERT_FUNSPACE] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_MP_TAC FINITE_CROSS THEN
  ASM_REWRITE_TAC []);;

export_thm FINITE_FUNSPACE;;

logfile "set-size-thm";;

let HAS_SIZE_FUNSPACE = prove
 (`!d (s : A set) (t : B set) m n.
        s HAS_SIZE m /\ t HAS_SIZE n
        ==> {f | (!x. x IN s ==> f(x) IN t) /\ (!x. ~(x IN s) ==> (f x = d))}
            HAS_SIZE (n EXP m)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`s : A set`, `s : A set`) THEN
  SPEC_TAC (`m : num`, `m : num`) THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [HAS_SIZE_CLAUSES] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [EXP; EMPTY_FUNSPACE; HAS_SIZE_SING] THEN
   NO_TAC;
   ALL_TAC] THEN
  REWRITE_TAC [HAS_SIZE_CLAUSES] THEN
  GEN_TAC THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `a : A` (X_CHOOSE_THEN `u : A set` STRIP_ASSUME_TAC))
       STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC [INSERT_FUNSPACE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  CONJ_TAC THENL
  [REWRITE_TAC [FORALL_PAIR_THM; IN_CROSS; PAIR_EQ; IN_ELIM] THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT STRIP_TAC THENL
   [POP_ASSUM (MP_TAC o SPEC `a:A`) THEN
    REWRITE_TAC [];
    ASM_CASES_TAC `(x:A) = a` THENL
    [POP_ASSUM SUBST_VAR_TAC THEN
     UNDISCH_TAC `!x. ~(x IN u) ==> (p2' : A -> B) x = d` THEN
     DISCH_THEN (MP_TAC o SPEC `a : A`) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
     ASM_REWRITE_TAC []]];
   REWRITE_TAC [EXP] THEN
   MATCH_MP_TAC HAS_SIZE_CROSS THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm HAS_SIZE_FUNSPACE;;

let CARD_FUNSPACE = prove
 (`!d (s : A set) (t : B set).
     FINITE s /\ FINITE t
         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\
                        (!x. ~(x IN s) ==> (f x = d))} =
              (CARD t) EXP (CARD s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`d : B`; `s : A set`; `t : B set`;
                 `CARD (s : A set)`; `CARD (t : B set)`] HAS_SIZE_FUNSPACE) THEN
  ASM_REWRITE_TAC [HAS_SIZE] THEN
  DISCH_THEN (ACCEPT_TAC o CONJUNCT2));;

export_thm CARD_FUNSPACE;;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let IMAGE_POWERSET = prove
 (`!(s : A set).
     {t | t SUBSET s} =
     IMAGE (\p. {x | p x})
       {p | (!x:A. x IN s ==> p x IN UNIV) /\
            (!x. ~(x IN s) ==> (p x = F))}`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [EXTENSION] THEN
  X_GEN_TAC `t : A set` THEN
  REWRITE_TAC
    [IN_ELIM; IN_IMAGE; IN_UNIV; EXTENSION; SUBSET; CONTRAPOS_THM] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EXISTS_TAC `\x. (x:A) IN t` THEN
   REWRITE_TAC [] THEN
   FIRST_ASSUM ACCEPT_TAC;
   DISCH_THEN (X_CHOOSE_THEN `p : A -> bool` STRIP_ASSUME_TAC) THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM (SUBST1_TAC o SYM o SPEC `x : A`) THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm IMAGE_POWERSET;;

let INSERT_BOOL = prove
 (`UNIV = T INSERT (F INSERT EMPTY)`,
  REWRITE_TAC [EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] THEN
  ACCEPT_TAC EXCLUDED_MIDDLE);;

export_thm INSERT_BOOL;;

let EMPTY_POWERSET = prove
 (`{s | (s : A set) SUBSET {}} = {{}}`,
  ONCE_REWRITE_TAC [EXTENSION] THEN
  X_GEN_TAC `x : A set` THEN
  REWRITE_TAC [SUBSET_EMPTY; IN_SING; IN_ELIM]);;

export_thm EMPTY_POWERSET;;

let INSERT_POWERSET = prove
 (`(!(a:A) t.
      {s | s SUBSET (a INSERT t)} =
      {s | s SUBSET t} UNION IMAGE (\s. a INSERT s) {s | s SUBSET t})`,
  REWRITE_TAC [SUBSET_INSERT_DELETE] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `t:A set`] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC [UNION_SUBSET] THEN
  ONCE_REWRITE_TAC [SUBSET] THEN
  REWRITE_TAC [FORALL_IN_IMAGE; FORALL_IN_GSPEC] THEN
  REWRITE_TAC [IN_ELIM; IN_UNION; IN_IMAGE] THEN
  REPEAT CONJ_TAC THENL
  [X_GEN_TAC `s:A set` THEN
   ASM_CASES_TAC `(a:A) IN s` THENL
   [STRIP_TAC THEN
    DISJ2_TAC THEN
    EXISTS_TAC `s DELETE (a:A)` THEN
    ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC INSERT_DELETE THEN
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN (fun th -> DISJ1_TAC THEN MP_TAC th) THEN
    MATCH_MP_TAC EQ_IMP THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    ASM_REWRITE_TAC [DELETE_NON_ELEMENT]];
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `s : A set` THEN
   ASM_REWRITE_TAC [DELETE_SUBSET];
   REWRITE_TAC [DELETE_INSERT] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `s : A set` THEN
   ASM_REWRITE_TAC [DELETE_SUBSET]]);;

export_thm INSERT_POWERSET;;

let POWERSET_CLAUSES = CONJ EMPTY_POWERSET INSERT_POWERSET;;

logfile "set-finite-thm";;

let FINITE_BOOL = prove
 (`FINITE (UNIV : bool set)`,
  REWRITE_TAC [INSERT_BOOL; FINITE_INSERT; FINITE_EMPTY]);;

export_thm FINITE_BOOL;;

let FINITE_POWERSET = prove
 (`!(s : A set). FINITE s ==> FINITE {t | t SUBSET s}`,
  REPEAT STRIP_TAC THEN
  PURE_REWRITE_TAC [IMAGE_POWERSET] THEN
  MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_MP_TAC FINITE_FUNSPACE THEN
  ASM_REWRITE_TAC [FINITE_BOOL]);;

export_thm FINITE_POWERSET;;

let FINITE_UNIONS = prove
 (`!(s : (A set) set).
     FINITE (UNIONS s) <=> FINITE s /\ (!t. t IN s ==> FINITE t)`,
  GEN_TAC THEN
  ASM_CASES_TAC `FINITE (s : (A set) set)` THENL
  [MP_TAC (SPEC `s : (A set) set` FINITE_FINITE_UNIONS) THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{(t : A set) | t SUBSET (UNIONS s)}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_POWERSET THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [SUBSET; IN_ELIM; IN_UNIONS] THEN
    X_GEN_TAC `t : A set` THEN
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `t : A set` THEN
    ASM_REWRITE_TAC []]]);;

export_thm FINITE_UNIONS;;

logfile "set-size-thm";;

let HAS_SIZE_BOOL = prove
 (`(UNIV : bool set) HAS_SIZE 2`,
  CONV_TAC HAS_SIZE_CONV THEN
  EXISTS_TAC `T` THEN
  EXISTS_TAC `F` THEN
  REWRITE_TAC [INSERT_BOOL]);;

export_thm HAS_SIZE_BOOL;;

let HAS_SIZE_POWERSET = prove
 (`!(s:A set) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)`,
  REPEAT STRIP_TAC THEN
  PURE_REWRITE_TAC [IMAGE_POWERSET] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  CONJ_TAC THENL
  [X_GEN_TAC `p : A -> bool` THEN
   X_GEN_TAC `q : A -> bool` THEN
   REWRITE_TAC [EXTENSION; IN_ELIM; FUN_EQ_THM] THEN
   STRIP_TAC;
   MATCH_MP_TAC HAS_SIZE_FUNSPACE THEN
   ASM_REWRITE_TAC [HAS_SIZE_BOOL]]);;

export_thm HAS_SIZE_POWERSET;;

let CARD_POWERSET = prove
 (`!(s : A set). FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPECL [`s : A set`; `CARD (s : A set)`] HAS_SIZE_POWERSET) THEN
  ASM_REWRITE_TAC [HAS_SIZE] THEN
  DISCH_THEN (ACCEPT_TAC o CONJUNCT2));;

export_thm CARD_POWERSET;;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let EMPTY_NUMSEG_LT = prove
  (`{m | m < 0} = EMPTY`,
   REWRITE_TAC [EXTENSION; NOT_IN_EMPTY; IN_ELIM; LT]);;

export_thm EMPTY_NUMSEG_LT;;

let INSERT_NUMSEG_LT = prove
  (`!n. {m | m < SUC n} = n INSERT {m | m < n}`,
   REWRITE_TAC [EXTENSION; IN_INSERT; IN_ELIM; LT]);;

export_thm INSERT_NUMSEG_LT;;

logfile "set-finite-thm";;

let FINITE_NUMSEG_LT = prove
 (`!(n:num). FINITE {m | m < n}`,
  INDUCT_TAC THENL
  [REWRITE_TAC [EMPTY_NUMSEG_LT; FINITE_EMPTY];
   ASM_REWRITE_TAC [INSERT_NUMSEG_LT; FINITE_INSERT]]);;

export_thm FINITE_NUMSEG_LT;;

let FINITE_NUMSEG_LE = prove
 (`!n. FINITE {m | m <= n}`,
  REWRITE_TAC [GSYM LT_SUC_LE; FINITE_NUMSEG_LT]);;

export_thm FINITE_NUMSEG_LE;;

let num_FINITE = prove
 (`!(s : num set). FINITE s <=> ?a. !x. x IN s ==> x <= a`,
  GEN_TAC THEN
  EQ_TAC THENL
  [SPEC_TAC (`s : num set`,`s : num set`) THEN
   MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
   REWRITE_TAC [IN_INSERT; NOT_IN_EMPTY] THEN
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `MAX x a` THEN
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [LE_MAX1];
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `a:num` THEN
    REWRITE_TAC [LE_MAX2] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   STRIP_TAC THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
   EXISTS_TAC `{m:num | m <= a}` THEN
   REWRITE_TAC [FINITE_NUMSEG_LE] THEN
   REWRITE_TAC [SUBSET; IN_ELIM] THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm num_FINITE;;

let num_FINITE_AVOID = prove
 (`!(s : num set). FINITE s ==> ?a. ~(a IN s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `s : num set` num_FINITE) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  EXISTS_TAC `SUC a` THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `SUC a`) THEN
  ASM_REWRITE_TAC [NOT_LE; LT]);;

export_thm num_FINITE_AVOID;;

let num_INFINITE = prove
 (`INFINITE (UNIV : num set)`,
  REWRITE_TAC [INFINITE] THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `UNIV : num set` num_FINITE_AVOID) THEN
  ASM_REWRITE_TAC [IN_UNIV]);;

export_thm num_INFINITE;;

logfile "set-size-thm";;

let HAS_SIZE_NUMSEG_LT = prove
 (`!n. {m | m < n} HAS_SIZE n`,
  INDUCT_TAC THENL
  [REWRITE_TAC [EMPTY_NUMSEG_LT; HAS_SIZE_CLAUSES];
   REWRITE_TAC [INSERT_NUMSEG_LT; HAS_SIZE_CLAUSES] THEN
   EXISTS_TAC `n:num` THEN
   EXISTS_TAC `{m | m < n}` THEN
   ASM_REWRITE_TAC [IN_ELIM; LT_REFL]]);;

export_thm HAS_SIZE_NUMSEG_LT;;

let CARD_NUMSEG_LT = prove
 (`!n. CARD {m | m < n} = n`,
  REWRITE_TAC [REWRITE_RULE [HAS_SIZE] HAS_SIZE_NUMSEG_LT]);;

export_thm CARD_NUMSEG_LT;;

let HAS_SIZE_NUMSEG_LE = prove
 (`!n. {m | m <= n} HAS_SIZE (n + 1)`,
  REWRITE_TAC [GSYM LT_SUC_LE; HAS_SIZE_NUMSEG_LT; ADD1]);;

export_thm HAS_SIZE_NUMSEG_LE;;

let CARD_NUMSEG_LE = prove
 (`!n. CARD {m | m <= n} = n + 1`,
  REWRITE_TAC [REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_LE]);;

export_thm CARD_NUMSEG_LE;;

(***
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
***)

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets.                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-thm";;

let HAS_SIZE_INDEX = prove
 (`!s n.
     s HAS_SIZE n ==>
     ?(f : num -> A).
       (!m. m < n ==> f(m) IN s) /\
                      (!x. x IN s ==> ?!m. m < n /\ (f m = x))`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  INDUCT_TAC THENL
  [GEN_TAC THEN
   REWRITE_TAC [HAS_SIZE_0] THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   REWRITE_TAC [NOT_IN_EMPTY; LT];
   GEN_TAC THEN
   REWRITE_TAC [HAS_SIZE_SUC; GSYM MEMBER_NOT_EMPTY] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `s DELETE (x:A)`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   EXISTS_TAC `\m. if (m:num) = n then (x:A) else f m` THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    ASM_CASES_TAC `(m:num) = n` THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [LT] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `m:num`) THEN
     ASM_REWRITE_TAC [IN_DELETE] THEN
     STRIP_TAC];
    REWRITE_TAC [EXISTS_UNIQUE_THM] THEN
    X_GEN_TAC `y:A` THEN
    STRIP_TAC THEN
    CONJ_TAC THENL
    [ASM_CASES_TAC `(y:A) = x` THENL
     [POP_ASSUM SUBST_VAR_TAC THEN
      EXISTS_TAC `n:num` THEN
      REWRITE_TAC [SUC_LT];
      FIRST_X_ASSUM (MP_TAC o SPEC `y:A`) THEN
      ASM_REWRITE_TAC [IN_DELETE; EXISTS_UNIQUE_THM] THEN
      DISCH_THEN (STRIP_ASSUME_TAC o CONJUNCT1) THEN
      EXISTS_TAC `m:num` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC LT_TRANS THEN
       EXISTS_TAC `n:num` THEN
       ASM_REWRITE_TAC [SUC_LT];
       COND_CASES_TAC THENL
       [UNDISCH_TAC `m < n` THEN
        ASM_REWRITE_TAC [LT_REFL];
        FIRST_ASSUM ACCEPT_TAC]]];
     ASM_CASES_TAC `(y:A) = x` THENL
     [POP_ASSUM SUBST_VAR_TAC THEN
      X_GEN_TAC `m1:num` THEN
      X_GEN_TAC `m2:num` THEN
      REWRITE_TAC [LT] THEN
      COND_CASES_TAC THENL
      [POP_ASSUM SUBST_VAR_TAC THEN
       COND_CASES_TAC THENL
       [POP_ASSUM SUBST_VAR_TAC THEN
        REWRITE_TAC [];
        REWRITE_TAC [] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC `m2:num`) THEN
        ASM_REWRITE_TAC [IN_DELETE]];
       REWRITE_TAC [] THEN
       STRIP_TAC THEN
       FIRST_X_ASSUM (MP_TAC o SPEC `m1:num`) THEN
       ASM_REWRITE_TAC [IN_DELETE]];
      X_GEN_TAC `m1:num` THEN
      X_GEN_TAC `m2:num` THEN
      REWRITE_TAC [LT] THEN
      COND_CASES_TAC THENL
      [ASM_REWRITE_TAC [];
       COND_CASES_TAC THENL
       [ASM_REWRITE_TAC [];
        REWRITE_TAC [] THEN
        STRIP_TAC THEN
        FIRST_X_ASSUM (MP_TAC o SPEC `y:A`) THEN
        ASM_REWRITE_TAC [IN_DELETE; EXISTS_UNIQUE_THM] THEN
        DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN
        ASM_REWRITE_TAC []]]]]]]);;

export_thm HAS_SIZE_INDEX;;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_IFF_INJECTIVE_GEN = prove
 (`!s t (f:A->B).
        FINITE s /\ FINITE t /\ (CARD s = CARD t) /\ (IMAGE f s) SUBSET t
        ==> ((!y. y IN t ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM NOT_CLAUSES] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))` MP_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC [FINITE_IMAGE; FINITE_DELETE] THEN
    REWRITE_TAC [SUBSET; IN_IMAGE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x' : B`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `z : A` STRIP_ASSUME_TAC) THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    ASM_CASES_TAC `(z : A) = y` THENL
    [EXISTS_TAC `x : A` THEN
     ASM_REWRITE_TAC [];
     EXISTS_TAC `z : A` THEN
     ASM_REWRITE_TAC []];
    REWRITE_TAC [NOT_LE] THEN
    MATCH_MP_TAC LET_TRANS THEN
    EXISTS_TAC `CARD (s DELETE (y:A))` THEN
    ASM_SIMP_TAC [CARD_IMAGE_LE; FINITE_DELETE] THEN
    ASM_SIMP_TAC [CARD_DELETE] THEN
    REWRITE_TAC [GSYM LE_SUC_LT] THEN
    MATCH_MP_TAC EQ_IMP_LE THEN
    REWRITE_TAC [ONE] THEN
    CONV_TAC (RAND_CONV (REWR_CONV (GSYM SUB_0))) THEN
    MATCH_MP_TAC SUB_SUC_CANCEL THEN
    REWRITE_TAC [GSYM NOT_LE; LE] THEN
    FIRST_X_ASSUM
      (fun th -> CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (SYM th))))) THEN
    ASM_SIMP_TAC [CARD_EQ_0] THEN
    REWRITE_TAC [GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `x : A` THEN
    FIRST_ASSUM ACCEPT_TAC];
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   SUBGOAL_THEN `IMAGE (f:A->B) s = t` MP_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (fun th -> CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC [];
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    REWRITE_TAC [IN_IMAGE] THEN
    STRIP_TAC THEN
    EXISTS_TAC `x : A` THEN
    ASM_REWRITE_TAC []]]);;

export_thm SURJECTIVE_IFF_INJECTIVE_GEN;;

let SURJECTIVE_IFF_INJECTIVE = prove
 (`!s (f:A->A).
        FINITE s /\ (IMAGE f s) SUBSET s
        ==> ((!y. y IN s ==> ?x. x IN s /\ (f x = y)) <=>
             (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)))`,
  SIMP_TAC[SURJECTIVE_IFF_INJECTIVE_GEN]);;

export_thm SURJECTIVE_IFF_INJECTIVE;;

let IMAGE_IMP_INJECTIVE_GEN = prove
 (`!s t (f:A->B).
        FINITE s /\ (CARD s = CARD t) /\ (IMAGE f s = t)
        ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT GEN_TAC THEN DISCH_THEN (ASSUME_TAC o GSYM) THEN
  MP_TAC(ISPECL [`s:A set`; `t:B set`; `f:A->B`]
                SURJECTIVE_IFF_INJECTIVE_GEN) THEN
  ASM_SIMP_TAC[SUBSET_REFL; FINITE_IMAGE] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [IN_IMAGE] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x : A` THEN
  ASM_REWRITE_TAC []);;

export_thm IMAGE_IMP_INJECTIVE_GEN;;

let IMAGE_IMP_INJECTIVE = prove
 (`!s (f : A -> A). FINITE s /\ (IMAGE f s = s)
       ==> !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`s : A set`; `s : A set`; `f : A -> A`]
            IMAGE_IMP_INJECTIVE_GEN) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm IMAGE_IMP_INJECTIVE;;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let CARD_LE_INJ = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s <= CARD t
   ==> ?(f:A->B). (IMAGE f s) SUBSET t /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  REWRITE_TAC [IMP_CONJ] THEN
  REWRITE_TAC [RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REWRITE_TAC [IMAGE_CLAUSES; EMPTY_SUBSET; NOT_IN_EMPTY];
   ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s : A set`] THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC [CARD_CLAUSES] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
  [REWRITE_TAC [CARD_EMPTY; LE; NOT_SUC];
   ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:B`; `t:B set`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC [CARD_CLAUSES] THEN
  REWRITE_TAC [LE_SUC] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t:B set`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (X_CHOOSE_THEN `f:A->B` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\z:A. if z = x then (y:B) else f(z)` THEN
  REWRITE_TAC [IMAGE_CLAUSES] THEN
  CONJ_TAC THENL
  [UNDISCH_TAC `IMAGE (f : A -> B) s SUBSET t` THEN
   REWRITE_TAC [SUBSET; IN_IMAGE; IN_INSERT] THEN
   STRIP_TAC THEN
   X_GEN_TAC `z : B` THEN
   MATCH_MP_TAC (TAUT `(Y ==> (~X ==> Z)) ==> (X \/ Y ==> X \/ Z)`) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `w : A` (CONJUNCTS_THEN2 SUBST_VAR_TAC ASSUME_TAC)) THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC [];
    STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `w : A` THEN
    ASM_REWRITE_TAC []];
   X_GEN_TAC `w : A` THEN
   COND_CASES_TAC THENL
   [DISCH_THEN (K ALL_TAC) THEN
    POP_ASSUM SUBST_VAR_TAC THEN
    X_GEN_TAC `z : A` THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [IN_INSERT] THEN
     REPEAT STRIP_TAC THEN
     UNDISCH_TAC `IMAGE (f : A -> B) s SUBSET t` THEN
     REWRITE_TAC [SUBSET; IN_IMAGE; NOT_FORALL_THM] THEN
     EXISTS_TAC `y : B` THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `z : A` THEN
     ASM_REWRITE_TAC []];
    ASM_REWRITE_TAC [IN_INSERT] THEN
    STRIP_TAC THEN
    X_GEN_TAC `z : A` THEN
    COND_CASES_TAC THENL
    [DISCH_THEN (K ALL_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     STRIP_TAC THEN
     SUBGOAL_THEN `F` CONTR_TAC THEN
     UNDISCH_TAC `IMAGE (f : A -> B) s SUBSET t` THEN
     REWRITE_TAC [SUBSET; IN_IMAGE; NOT_FORALL_THM] THEN
     EXISTS_TAC `y : B` THEN
     ASM_REWRITE_TAC [] THEN
     EXISTS_TAC `w : A` THEN
     ASM_REWRITE_TAC [];
     REWRITE_TAC [] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `w : A`) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (MP_TAC o SPEC `z : A`) THEN
     ASM_REWRITE_TAC []]]]);;

export_thm CARD_LE_INJ;;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "set-thm";;

let FORALL_IN_EMPTY = prove
 (`!p. (!x : A. x IN {} ==> p x) <=> T`,
  REWRITE_TAC [NOT_IN_EMPTY]);;

let FORALL_IN_CLAUSES = CONJ FORALL_IN_EMPTY FORALL_IN_INSERT;;

let EXISTS_IN_EMPTY = prove
 (`!p. (?x : A. x IN {} /\ p x) <=> F`,
  REWRITE_TAC [NOT_IN_EMPTY]);;

let EXISTS_IN_CLAUSES = CONJ EXISTS_IN_EMPTY EXISTS_IN_INSERT;;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

let SURJECTIVE_ON_RIGHT_INVERSE = prove
 (`!(f:A->B) s t. (!y. y IN t ==> ?x. x IN s /\ (f(x) = y)) <=>
         (?g. !y. y IN t ==> g(y) IN s /\ (f(g(y)) = y))`,
  REWRITE_TAC [RIGHT_IMP_EXISTS_THM; SKOLEM_THM]);;

export_thm SURJECTIVE_ON_RIGHT_INVERSE;;

let INJECTIVE_ON_LEFT_INVERSE = prove
 (`!(f:A->B) s.
     (!x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)) <=>
     (?g. !x. x IN s ==> (g (f x) = x))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `!(g : B -> A).
       (!x. x IN s ==> (g (f x) = x)) <=>
       (!y x. x IN s /\ (y = f x) ==> (g y = x))`
    (fun th -> REWRITE_TAC [th]) THENL
  [GEN_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    POP_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []];
   REWRITE_TAC [GSYM SKOLEM_THM] THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXISTS_TAC `@z. z IN s /\ (f : A -> B) z = y` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `x : A` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x`) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM
      (fun th ->
         MP_TAC (SPEC `x : A` th) THEN
         MP_TAC (SPEC `y : A` th)) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN SUBST1_TAC THEN
    REFL_TAC]]);;

export_thm INJECTIVE_ON_LEFT_INVERSE;;

let BIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove
 (`!(f : A -> B) s t.
        (!x. x IN s ==> f(x) IN t)
        ==> ((!x y. x IN s /\ y IN s /\ f(x) = f(y) ==> x = y) /\
             (!y. y IN t ==> ?x. x IN s /\ f x = y) <=>
            ?g. (!y. y IN t ==> g(y) IN s) /\
                (!y. y IN t ==> (f(g(y)) = y)) /\
                (!x. x IN s ==> (g(f(x)) = x)))`,
  REPEAT GEN_TAC THEN
  DISCH_TAC THEN
  REWRITE_TAC [INJECTIVE_ON_LEFT_INVERSE; SURJECTIVE_ON_RIGHT_INVERSE] THEN
  REWRITE_TAC [RIGHT_AND_EXISTS_THM] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  EQ_TAC THENL
  [DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_THEN `h : B -> A` STRIP_ASSUME_TAC)
                               STRIP_ASSUME_TAC) THEN
   REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ACCEPT_TAC (K ALL_TAC));
    FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC);
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(h : B -> A) (f (x : A))` THEN
    CONJ_TAC THENL
    [SUBGOAL_THEN `(f : A -> B) x IN t` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC;
      SPEC_TAC (`(f : A -> B) x`,`y : B`) THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `(h : B -> A) ((f : A -> B) ((g : B -> A) y))` THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC EQ_SYM THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (CONJUNCTS_THEN2 ACCEPT_TAC (K ALL_TAC));
       AP_TERM_TAC THEN
       FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) ACCEPT_TAC)]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_ASSUM ACCEPT_TAC]];
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `g : B -> A` THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm BIJECTIVE_ON_LEFT_RIGHT_INVERSE;;

let SURJECTIVE_RIGHT_INVERSE = prove
 (`!(f : A -> B). (!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)`,
  GEN_TAC THEN
  MP_TAC (SPECL [`f : A -> B`; `UNIV : A set`; `UNIV : B set`]
                SURJECTIVE_ON_RIGHT_INVERSE) THEN
  REWRITE_TAC [IN_UNIV]);;

export_thm SURJECTIVE_RIGHT_INVERSE;;

let INJECTIVE_LEFT_INVERSE = prove
 (`!(f : A -> B). (!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC (SPECL [`f : A -> B`; `UNIV : A set`]
                INJECTIVE_ON_LEFT_INVERSE) THEN
  REWRITE_TAC [IN_UNIV]);;

export_thm INJECTIVE_LEFT_INVERSE;;

let BIJECTIVE_LEFT_RIGHT_INVERSE = prove
 (`!(f : A -> B).
       (!x y. f(x) = f(y) ==> x = y) /\ (!y. ?x. f x = y) <=>
       ?g. (!y. f(g(y)) = y) /\ (!x. g(f(x)) = x)`,
  GEN_TAC THEN
  MP_TAC (SPECL [`f : A -> B`; `UNIV : A set`; `UNIV : B set`]
                BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
  REWRITE_TAC [IN_UNIV]);;

export_thm BIJECTIVE_LEFT_RIGHT_INVERSE;;

logfile "function-thm";;

let FUNCTION_FACTORS_RIGHT = prove
 (`!(f : A -> C) (g : B -> C). (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [FUN_EQ_THM; o_THM; GSYM SKOLEM_THM] THEN
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
  REFL_TAC);;

export_thm FUNCTION_FACTORS_RIGHT;;

let FUNCTION_FACTORS_LEFT = prove
 (`!(f : A -> C) (g : A -> B).
     (!x y. (g x = g y) ==> (f x = f y)) <=> ?h. f = h o g`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `!h. ((f : A -> C) = h o (g : A -> B)) <=> !y x. (y = g x) ==> (h y = f x)`
   (fun th -> REWRITE_TAC [th]) THENL
  [GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; o_THM] THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REFL_TAC];
   REWRITE_TAC [GSYM SKOLEM_THM] THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXISTS_TAC `(f : A -> C) (@z. y = (g : A -> B) z)` THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MATCH_MP_TAC EQ_SYM THEN
    CONV_TAC SELECT_CONV THEN
    EXISTS_TAC `x : A` THEN
    REFL_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(g : A -> B) x`) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM
      (fun th ->
         MP_TAC (SPEC `x : A` th) THEN
         MP_TAC (SPEC `y : A` th)) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST_VAR_TAC THEN
     MATCH_ACCEPT_TAC EQ_SYM]]);;

export_thm FUNCTION_FACTORS_LEFT;;

let SURJECTIVE_FORALL_THM = prove
 (`!(f:A->B). (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))`,
  GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
    DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC];
   DISCH_THEN (fun th -> ONCE_REWRITE_TAC [GSYM th]) THEN
   GEN_TAC THEN
   EXISTS_TAC `x : A` THEN
   REFL_TAC]);;

export_thm SURJECTIVE_FORALL_THM;;

let SURJECTIVE_EXISTS_THM = prove
 (`!(f:A->B). (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))`,
  GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    EXISTS_TAC `(f : A -> B) x` THEN
    FIRST_ASSUM ACCEPT_TAC;
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
    DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
    EXISTS_TAC `x : A` THEN
    FIRST_ASSUM ACCEPT_TAC];
    DISCH_THEN (MP_TAC o SPEC `\y:B. !x:A. ~(f x = y)`) THEN
    REWRITE_TAC [GSYM NOT_FORALL_THM; GSYM NOT_EXISTS_THM] THEN
    MATCH_MP_TAC (TAUT `((Y <=> X) ==> Z) ==> ((~X <=> ~Y) ==> Z)`) THEN
    DISCH_THEN (fun th -> ONCE_REWRITE_TAC [th]) THEN
    GEN_TAC THEN
    EXISTS_TAC `x : A` THEN
    REFL_TAC]);;

export_thm SURJECTIVE_EXISTS_THM;;

logfile "set-thm";;

let SURJECTIVE_IMAGE_THM = prove
 (`!(f:A->B). (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})`,
  GEN_TAC THEN
  REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   GEN_TAC THEN
   X_GEN_TAC `y : B` THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
   DISCH_THEN (X_CHOOSE_THEN `z : A` SUBST_VAR_TAC) THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    EXISTS_TAC `z : A` THEN
    ASM_REWRITE_TAC []];
   DISCH_THEN (MP_TAC o SPEC `\ (y:B). T`) THEN
   REWRITE_TAC [] THEN
   CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [EQ_SYM_EQ])) THEN
   DISCH_THEN ACCEPT_TAC]);;

export_thm SURJECTIVE_IMAGE_THM;;

let IMAGE_INJECTIVE_IMAGE_OF_SUBSET = prove
 (`!(f:A->B) s.
     ?t. t SUBSET s /\
         IMAGE f s = IMAGE f t /\
         (!x y. x IN t /\ y IN t /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
    `?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\ f(g(y)) = y`
    STRIP_ASSUME_TAC THENL
  [REWRITE_TAC [GSYM SURJECTIVE_ON_RIGHT_INVERSE] THEN
   ONCE_REWRITE_TAC [CONJ_SYM] THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   REWRITE_TAC [IN_IMAGE];
   EXISTS_TAC `IMAGE (g:B->A) (IMAGE (f:A->B) s)` THEN
   REPEAT STRIP_TAC THENL
   [REWRITE_TAC [SUBSET] THEN
    X_GEN_TAC `z : A` THEN
    ONCE_REWRITE_TAC [IN_IMAGE] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST1_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x : B`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (CONJUNCTS_THEN2 ACCEPT_TAC (K ALL_TAC));
    REWRITE_TAC [EXTENSION; IN_IMAGE; IN_ELIM] THEN
    X_GEN_TAC `z : B` THEN
    EQ_TAC THENL
    [STRIP_TAC THEN
     FIRST_X_ASSUM SUBST_VAR_TAC THEN
     EXISTS_TAC `(g : B -> A) ((f : A -> B) x)` THEN
     CONJ_TAC THENL
     [FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x`) THEN
      MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC FUN_IN_IMAGE THEN
       FIRST_ASSUM ACCEPT_TAC;
       DISCH_THEN (ACCEPT_TAC o SYM o CONJUNCT2)];
      EXISTS_TAC `(f : A -> B) x` THEN
      REWRITE_TAC [] THEN
      EXISTS_TAC `x : A` THEN
      ASM_REWRITE_TAC []];
     STRIP_TAC THEN
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
     EXISTS_TAC `(g : B -> A) ((f : A -> B) x'')` THEN
     REWRITE_TAC [] THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x''`) THEN
     MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN (ACCEPT_TAC o CONJUNCT1)]];
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(g : B -> A) ((f : A -> B) x)` THEN
    CONJ_TAC THENL
    [MATCH_MP_TAC EQ_SYM THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM (K ALL_TAC) THEN
     POP_ASSUM MP_TAC THEN
     REWRITE_TAC [IN_IMAGE] THEN
     STRIP_TAC THEN
     REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
     AP_TERM_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x''`) THEN
     MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
     CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN (ACCEPT_TAC o CONJUNCT2)];
     MATCH_MP_TAC EQ_TRANS THEN
     EXISTS_TAC `(g : B -> A) ((f : A -> B) y)` THEN
     CONJ_TAC THENL
     [ASM_REWRITE_TAC [];
      POP_ASSUM (K ALL_TAC) THEN
      POP_ASSUM MP_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [IN_IMAGE] THEN
      STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
      AP_TERM_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x'`) THEN
      MATCH_MP_TAC (TAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)`) THEN
      CONJ_TAC THENL
      [MATCH_MP_TAC FUN_IN_IMAGE THEN
       FIRST_ASSUM ACCEPT_TAC;
       DISCH_THEN (ACCEPT_TAC o CONJUNCT2)]]]]]);;

export_thm IMAGE_INJECTIVE_IMAGE_OF_SUBSET;;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image under a function.                   *)
(* ------------------------------------------------------------------------- *)

let INJECTIVE_ON_IMAGE = prove
 (`!(f:A->B) u.
    (!s t. s SUBSET u /\ t SUBSET u /\ IMAGE f s = IMAGE f t ==> s = t) <=>
    (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [SUBSET; IN_IMAGE; EXTENSION] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`(x:A) INSERT EMPTY`;
                                  `(y:A) INSERT EMPTY`]) THEN
   REWRITE_TAC [IN_SING] THEN
   MATCH_MP_TAC (TAUT `(X /\ (Y ==> Z)) ==> ((X ==> Y) ==> Z)`) THEN
   REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [];
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    REWRITE_TAC [UNWIND_THM2] THEN
    ASM_REWRITE_TAC [];
    FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
    REWRITE_TAC []];
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x`) THEN
   MATCH_MP_TAC (TAUT `(Y ==> W /\ (X ==> Z)) /\ (Z ==> X /\ (W ==> Y)) ==>
                       ((W <=> X) ==> (Y <=> Z))`) THEN
   CONJ_TAC THENL
   [STRIP_TAC THEN
    CONJ_TAC THENL
    [EXISTS_TAC `x : A` THEN
     ASM_REWRITE_TAC [];
     DISCH_THEN (X_CHOOSE_THEN `z : A` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `(x : A) = z` (fun th -> ASM_REWRITE_TAC [th]) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     CONJ_TAC THEN
     FIRST_X_ASSUM (fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC)];
    STRIP_TAC THEN
    CONJ_TAC THENL
    [EXISTS_TAC `x : A` THEN
     ASM_REWRITE_TAC [];
     DISCH_THEN (X_CHOOSE_THEN `z : A` STRIP_ASSUME_TAC) THEN
     SUBGOAL_THEN `(x : A) = z` (fun th -> ASM_REWRITE_TAC [th]) THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC [] THEN
     CONJ_TAC THEN
     FIRST_X_ASSUM (fun th -> MATCH_MP_TAC th THEN FIRST_ASSUM ACCEPT_TAC)]]]);;

export_thm INJECTIVE_ON_IMAGE;;

let INJECTIVE_IMAGE = prove
 (`!(f:A->B).
    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN MP_TAC(ISPECL [`f:A->B`; `UNIV : A set`] INJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC[IN_UNIV; SUBSET_UNIV]);;

export_thm INJECTIVE_IMAGE;;

let SURJECTIVE_ON_IMAGE = prove
 (`!(f:A->B) u v.
        (!t. t SUBSET v ==> ?s. s SUBSET u /\ IMAGE f s = t) <=>
        (!y. y IN v ==> ?x. x IN u /\ f x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EXTENSION; SUBSET; IN_IMAGE] THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   X_GEN_TAC `y:B` THEN
   DISCH_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `{y:B}`) THEN
   REWRITE_TAC [IN_SING] THEN
   MATCH_MP_TAC (TAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
   CONJ_TAC THENL
   [GEN_TAC THEN
    DISCH_THEN SUBST_VAR_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    EXISTS_TAC `x : A` THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   DISCH_TAC THEN
   X_GEN_TAC `t : B set` THEN
   DISCH_TAC THEN
   EXISTS_TAC `{x | x IN u /\ (f:A->B) x IN t}` THEN
   REWRITE_TAC [IN_ELIM] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (X_CHOOSE_THEN `z : A` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x : B`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x : B`) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (X_CHOOSE_THEN `z : A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z : A` THEN
    ASM_REWRITE_TAC []]]);;

export_thm SURJECTIVE_ON_IMAGE;;

let SURJECTIVE_IMAGE = prove
 (`!(f:A->B). (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  MP_TAC (ISPECL [`f:A->B`; `UNIV : A set`; `UNIV : B set`]
                 SURJECTIVE_ON_IMAGE) THEN
  REWRITE_TAC [IN_UNIV; SUBSET_UNIV]);;

export_thm SURJECTIVE_IMAGE;;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

logfile "set-size-thm";;

let CARD_EQ_BIJECTION = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?(f : A -> B).
                (!x. x IN s ==> f(x) IN t) /\
                (!y. y IN t ==> ?x. x IN s /\ f x = y) /\
                !x y. x IN s /\ y IN s /\ (f x = f y) ==> (x = y)`,
  MP_TAC CARD_LE_INJ THEN
  REPEAT (MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
  DISCH_THEN (fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[LE_REFL] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC [SURJECTIVE_IFF_INJECTIVE_GEN] THEN
  REWRITE_TAC [SUBSET; IN_IMAGE] THEN
  REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x : A` THEN
   ASM_REWRITE_TAC [];
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm CARD_EQ_BIJECTION;;

let CARD_EQ_BIJECTIONS = prove
 (`!s t. FINITE s /\ FINITE t /\ CARD s = CARD t
   ==> ?(f : A -> B) g.
                  (!x. x IN s ==> f(x) IN t /\ g (f x) = x) /\
                  (!y. y IN t ==> g(y) IN s /\ f (g y) = y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP CARD_EQ_BIJECTION) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC [SURJECTIVE_ON_RIGHT_INVERSE] THEN
  GEN_TAC THEN
  REWRITE_TAC [LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `(f : A -> B) x`) THEN
   MATCH_MP_TAC (TAUT `X /\ (Y ==> Z) ==> ((X ==> Y) ==> Z)`) THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC THEN
    ASM_REWRITE_TAC []];
   FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   FIRST_X_ASSUM (MP_TAC o SPEC `y : B`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC]);;

export_thm CARD_EQ_BIJECTIONS;;

let BIJECTIONS_HAS_SIZE = prove
 (`!s t (f : A -> B) g n.
        (!x. x IN s ==> f(x) IN t /\ g (f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f (g y) = y) /\
        s HAS_SIZE n
        ==> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = IMAGE (f:A->B) s` SUBST_ALL_TAC THENL
  [REWRITE_TAC [EXTENSION; IN_IMAGE] THEN
   X_GEN_TAC `y : B` THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `(g : B -> A) y` THEN
    ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
    ONCE_REWRITE_TAC [CONJ_SYM] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC];
   MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM
     (fun th ->
        MP_TAC (SPEC `x : A` th) THEN
        MP_TAC (SPEC `y : A` th)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN
     (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM)) THEN
   DISCH_THEN
     (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONV_TAC o LAND_CONV o REWR_CONV o SYM)) THEN
   REFL_TAC]);;

export_thm BIJECTIONS_HAS_SIZE;;

let BIJECTIONS_HAS_SIZE_EQ = prove
 (`!s t (f:A->B) g.
        (!x. x IN s ==> f(x) IN t /\ g (f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f (g y) = y)
        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [MATCH_MP_TAC
     (ONCE_REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
        BIJECTIONS_HAS_SIZE) THEN
   MAP_EVERY EXISTS_TAC [`f:A->B`; `g:B->A`] THEN
   CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC];
   MATCH_MP_TAC
     (ONCE_REWRITE_RULE [TAUT `a /\ b /\ c ==> d <=> a /\ b ==> c ==> d`]
        BIJECTIONS_HAS_SIZE) THEN
   MAP_EVERY EXISTS_TAC [`g:B->A`; `f:A->B`] THEN
   CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm BIJECTIONS_HAS_SIZE_EQ;;

let BIJECTIONS_CARD_EQ = prove
 (`!s t (f:A->B) g.
        (FINITE s \/ FINITE t) /\
        (!x. x IN s ==> f(x) IN t /\ g(f x) = x) /\
        (!y. y IN t ==> g(y) IN s /\ f(g y) = y)
        ==> CARD s = CARD t`,
  REPEAT GEN_TAC THEN
  DISCH_THEN (CONJUNCTS_THEN2
   MP_TAC (MP_TAC o MATCH_MP BIJECTIONS_HAS_SIZE_EQ)) THEN
  REWRITE_TAC [HAS_SIZE] THEN
  REPEAT STRIP_TAC THENL
  [FIRST_X_ASSUM (MP_TAC o SPEC `CARD (s : A set)`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
   REFL_TAC;
   FIRST_X_ASSUM (MP_TAC o SPEC `CARD (t : B set)`) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONJUNCTS_THEN2 (K ALL_TAC) SUBST1_TAC) THEN
   REFL_TAC]);;

export_thm BIJECTIONS_CARD_EQ;;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Examples/card.ml)                    *)
(* ------------------------------------------------------------------------- *)

(***
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
***)

logfile_end ();;

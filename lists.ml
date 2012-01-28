(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "ind_types.ml";;

(* ------------------------------------------------------------------------- *)
(* Standard tactic for list induction using MATCH_MP_TAC list_INDUCT         *)
(* ------------------------------------------------------------------------- *)

let LIST_INDUCT_TAC =
  let list_INDUCT = prove
   (`!P:(A)list->bool. P [] /\ (!h t. P t ==> P (CONS h t)) ==> !l. P l`,
    MATCH_ACCEPT_TAC list_INDUCT) in
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "list-thm";;

let NOT_CONS_NIL = prove
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC[distinctness "list"]);;

export_thm NOT_CONS_NIL;;

let CONS_11 = prove
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC[injectivity "list"]);;

export_thm CONS_11;;

let list_CASES = prove
 (`!l:(A)list. (l = []) \/ ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

export_thm list_CASES;;

let list_cases = prove_cases_thm list_INDUCT;;

export_thm list_cases;;

(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "list-dest-def";;

let HD = new_recursive_definition list_RECURSION
  `!h t. HD (CONS (h:A) t) = h`;;

export_thm HD;;

let TL = new_recursive_definition list_RECURSION
  `!h t. TL (CONS (h:A) t) = t`;;

export_thm TL;;

let (NULL_NIL,NULL_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(NULL ([] : A list) <=> T) /\
     (!h t. NULL (CONS (h:A) t) <=> F)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm NULL_NIL;;
export_thm NULL_CONS;;

let NULL = CONJ NULL_NIL NULL_CONS;;

let (case_list_nil,case_list_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!b f. case_list b f [] = (b:B)) /\
     (!b f h t. case_list b f (CONS h t) = f (h:A) t)` in
  CONJ_PAIR def;;

export_thm case_list_nil;;
export_thm case_list_cons;;

let case_list_def = CONJ case_list_nil case_list_cons;;

logfile "list-dest-thm";;

let NULL_EQ_NIL = prove
 (`!l. NULL (l : A list) <=> l = []`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [NULL; NOT_CONS_NIL]);;

export_thm NULL_EQ_NIL;;

let case_list_id = prove
  (`!(l : A list). case_list [] CONS l = l`,
   GEN_TAC THEN
   MP_TAC (ISPEC `l : A list` list_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_list_def]);;

export_thm case_list_id;;

let CONS_HD_TL = prove
 (`!(l : A list). ~(l = []) ==> CONS (HD l) (TL l) = l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [NOT_CONS_NIL; HD; TL]);;

export_thm CONS_HD_TL;;

(* ------------------------------------------------------------------------- *)
(* Length.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-length-def";;

let (LENGTH_NIL,LENGTH_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(LENGTH [] = 0) /\
     (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))` in
  CONJ_PAIR def;;

export_thm LENGTH_NIL;;
export_thm LENGTH_CONS;;

let LENGTH = CONJ LENGTH_NIL LENGTH_CONS;;

logfile "list-length-thm";;

let LENGTH_EQ_NIL = prove
 (`!l:A list. (LENGTH l = 0) <=> (l = [])`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC]);;

export_thm LENGTH_EQ_NIL;;

let LENGTH_EQ_CONS = prove
 (`!l n. (LENGTH l = SUC n) <=> ?h t. (l = CONS (h:A) t) /\ (LENGTH t = n)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; NOT_SUC; NOT_CONS_NIL] THEN
  ASM_REWRITE_TAC[SUC_INJ; CONS_11] THEN MESON_TAC[]);;

export_thm LENGTH_EQ_CONS;;

let LENGTH_TL = prove
 (`!(l:A list). ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL; ARITH; SUC_SUB1]);;

export_thm LENGTH_TL;;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-set-def";;

let (set_of_list_nil,set_of_list_cons) =
  let def = new_recursive_definition list_RECURSION
    `(set_of_list ([]:A list) = {}) /\
     (!h t. set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))` in
  CONJ_PAIR def;;

export_thm set_of_list_nil;;
export_thm set_of_list_cons;;

let set_of_list = CONJ set_of_list_nil set_of_list_cons;;

let list_of_set = new_definition
  `!(s : A set).
     list_of_set s = @l. (set_of_list l = s) /\ (LENGTH l = CARD s)`;;

let LIST_OF_SET_PROPERTIES = prove
 (`!(s : A set).
     FINITE(s) ==> (set_of_list (list_of_set s) = s) /\
                   (LENGTH (list_of_set s) = CARD s)`,
  REWRITE_TAC [list_of_set] THEN
  CONV_TAC (BINDER_CONV (RAND_CONV SELECT_CONV)) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REPEAT STRIP_TAC THENL
  [EXISTS_TAC `[] : A list` THEN
   REWRITE_TAC [CARD_CLAUSES; LENGTH; set_of_list];
   EXISTS_TAC `CONS (x:A) l` THEN
   ASM_REWRITE_TAC [LENGTH; set_of_list] THEN
   MP_TAC (SPECL [`x:A`; `s : A set`] (CONJUNCT2 CARD_CLAUSES)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (ACCEPT_TAC o SYM)]);;

export_thm LIST_OF_SET_PROPERTIES;;

logfile "list-set-thm";;

let SET_OF_LIST_OF_SET = prove
 (`!(s : A set). FINITE s ==> (set_of_list (list_of_set s) = s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `s : A set` LIST_OF_SET_PROPERTIES) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (ACCEPT_TAC o CONJUNCT1));;

export_thm SET_OF_LIST_OF_SET;;

let LENGTH_LIST_OF_SET = prove
 (`!(s : A set). FINITE s ==> LENGTH (list_of_set s) = CARD s`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `s : A set` LIST_OF_SET_PROPERTIES) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (ACCEPT_TAC o CONJUNCT2));;

export_thm LENGTH_LIST_OF_SET;;

let FINITE_SET_OF_LIST = prove
 (`!(l : A list). FINITE (set_of_list l)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; FINITE_EMPTY];
   ASM_REWRITE_TAC [set_of_list; FINITE_INSERT]]);;

export_thm FINITE_SET_OF_LIST;;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!(l : A list). set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list];
   REWRITE_TAC [set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]]);;

export_thm SET_OF_LIST_EQ_EMPTY;;

let CARD_SET_OF_LIST_LE = prove
 (`!(l : A list). CARD (set_of_list l) <= LENGTH l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [CARD_EMPTY; set_of_list; LE_0];
   REWRITE_TAC [set_of_list; LENGTH] THEN
   MP_TAC (SPECL [`h:A`; `set_of_list (t : A list)`]
                 (CONJUNCT2 CARD_CLAUSES)) THEN
   REWRITE_TAC [FINITE_SET_OF_LIST] THEN
   DISCH_THEN SUBST1_TAC THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `SUC (CARD (set_of_list (t : A list)))` THEN
   ASM_REWRITE_TAC [LE_SUC] THEN
   COND_CASES_TAC THENL
   [MATCH_ACCEPT_TAC SUC_LE;
    REWRITE_TAC [LE_SUC; LE_REFL]]]);;

export_thm CARD_SET_OF_LIST_LE;;

(* ------------------------------------------------------------------------- *)
(* Append.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-append-def";;

let (NIL_APPEND,CONS_APPEND) =
  let def = new_recursive_definition list_RECURSION
    `(!(l : A list). APPEND [] l = l) /\
     (!(l : A list) h t. APPEND (CONS h t) l = CONS h (APPEND t l))` in
  CONJ_PAIR def;;

export_thm NIL_APPEND;;
export_thm CONS_APPEND;;

let APPEND = CONJ NIL_APPEND CONS_APPEND;;

logfile "list-append-thm";;

let APPEND_NIL = prove
 (`!l:A list. APPEND l [] = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_NIL;;

let APPEND_ASSOC = prove
 (`!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_ASSOC;;

let LENGTH_APPEND = prove
 (`!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES]);;

export_thm LENGTH_APPEND;;

let APPEND_EQ_NIL = prove
 (`!l m. (APPEND (l:A list) m = []) <=> (l = []) /\ (m = [])`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; NOT_CONS_NIL]);;

export_thm APPEND_EQ_NIL;;

let HD_APPEND = prove
 (`!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; APPEND; NOT_CONS_NIL]);;

export_thm HD_APPEND;;

let SET_OF_LIST_APPEND = prove
 (`!(l1 : A list) l2.
     set_of_list (APPEND l1 l2) = set_of_list l1 UNION set_of_list l2`,
  ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [APPEND; set_of_list; UNION_EMPTY];
   ASM_REWRITE_TAC [APPEND; set_of_list] THEN
   ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
   REWRITE_TAC [UNION_ASSOC]]);;

export_thm SET_OF_LIST_APPEND;;

let NULL_APPEND = prove
 (`!l m. NULL (APPEND (l : A list) m) <=> NULL l /\ NULL m`,
  ASM_REWRITE_TAC [NULL_EQ_NIL; APPEND_EQ_NIL]);;

export_thm NULL_APPEND;;

(* ------------------------------------------------------------------------- *)
(* Map.                                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "list-map-def";;

let (MAP_NIL,MAP_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!(f : A -> B). MAP f NIL = NIL) /\
     (!(f : A -> B) h t. MAP f (CONS h t) = CONS (f h) (MAP f t))` in
  CONJ_PAIR def;;

export_thm MAP_NIL;;
export_thm MAP_CONS;;

let MAP = CONJ MAP_NIL MAP_CONS;;

logfile "list-map-thm";;

let MAP_APPEND = prove
 (`!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

export_thm MAP_APPEND;;

let LENGTH_MAP = prove
 (`!l. !f:A->B. LENGTH (MAP f l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]);;

export_thm LENGTH_MAP;;

let MAP_o = prove
 (`!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM]);;

export_thm MAP_o;;

let MAP_EQ_NIL  = prove
 (`!(f:A->B) l. MAP f l = [] <=> l = []`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; NOT_CONS_NIL]);;

export_thm MAP_EQ_NIL;;

let INJECTIVE_MAP = prove
 (`!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>
            (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`[x:A]`; `[y:A]`]) THEN
    ASM_REWRITE_TAC[MAP; CONS_11];
    REPEAT LIST_INDUCT_TAC THEN ASM_SIMP_TAC[MAP; NOT_CONS_NIL; CONS_11] THEN
    ASM_MESON_TAC[]]);;

export_thm INJECTIVE_MAP;;

let SURJECTIVE_MAP = prove
 (`!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [X_GEN_TAC `y:B` THEN FIRST_X_ASSUM(MP_TAC o SPEC `[y:B]`) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    LIST_INDUCT_TAC THEN REWRITE_TAC[MAP; CONS_11; NOT_CONS_NIL; MAP_EQ_NIL];
    MATCH_MP_TAC list_INDUCT] THEN
  ASM_MESON_TAC[MAP]);;

export_thm SURJECTIVE_MAP;;

let MAP_ID = prove
 (`!l. MAP (\x. (x:A)) l = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP]);;

export_thm MAP_ID;;

let MAP_I = prove
 (`MAP (I:A->A) = I`,
  REWRITE_TAC[FUN_EQ_THM; I_DEF; MAP_ID]);;

export_thm MAP_I;;

let SET_OF_LIST_MAP = prove
 (`!(f : A -> B) l.
     set_of_list (MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES];
   ASM_REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES]]);;

export_thm SET_OF_LIST_MAP;;

(* ------------------------------------------------------------------------- *)
(* Quantifiers.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "list-quant-def";;

let (ALL_NIL,ALL_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!p. ALL p ([] : A list) <=> T) /\
     (!p h t. ALL p (CONS (h:A) t) <=> p h /\ ALL p t)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm ALL_NIL;;
export_thm ALL_CONS;;

let ALL = CONJ ALL_NIL ALL_CONS;;

let (EX_NIL,EX_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!p. EX p ([] : A list) <=> F) /\
     (!p h t. EX p (CONS (h:A) t) <=> p h \/ EX p t)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm EX_NIL;;
export_thm EX_CONS;;

let EX = CONJ EX_NIL EX_CONS;;

logfile "list-quant-thm";;

let MAP_EQ = prove
 (`!(f:A->B) (g:A->B) l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

export_thm MAP_EQ;;

let NOT_EX = prove
 (`!P l. ~(EX P l) <=> ALL (\x. ~(P (x:A))) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

export_thm NOT_EX;;

let NOT_ALL = prove
 (`!P l. ~(ALL P l) <=> EX (\x. ~(P (x:A))) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[EX; ALL; DE_MORGAN_THM]);;

export_thm NOT_ALL;;

let ALL_MAP = prove
 (`!P f l. ALL P (MAP (f:A->B) l) <=> ALL (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; MAP; o_THM]);;

export_thm ALL_MAP;;

let ALL_T = prove
 (`!l. ALL (\x. T) (l:A list)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL]);;

export_thm ALL_T;;

let ALL_MP = prove
 (`!P Q l. ALL (\x. P x ==> Q (x:A)) l /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

export_thm ALL_MP;;

let AND_ALL = prove
 (`!P Q l. ALL P l /\ ALL Q l <=> ALL (\x. P (x:A) /\ Q x) l`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; CONJ_ACI]);;

export_thm AND_ALL;;

let EX_MAP = prove
 (`!P f l. EX P (MAP (f:A->B) l) <=> EX (P o f) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; EX; o_THM]);;

export_thm EX_MAP;;

let EXISTS_EX = prove
 (`!P l. (?x. EX (P x) l) <=> EX (\s. ?x. P (x:A) (s:B)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX] THEN
  ASM_MESON_TAC[]);;

export_thm EXISTS_EX;;

let FORALL_ALL = prove
 (`!P l. (!x. ALL (P x) l) <=> ALL (\s. !x. P (x:A) (s:B)) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN
  ASM_MESON_TAC[]);;

export_thm FORALL_ALL;;

let ALL_APPEND = prove
 (`!P l1 l2. ALL (P:A->bool) (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; APPEND; GSYM CONJ_ASSOC]);;

export_thm ALL_APPEND;;

let MONO_ALL = prove
 (`!P Q l. (!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

export_thm MONO_ALL;;

monotonicity_theorems := [MONO_ALL] @ !monotonicity_theorems;;

let ALL_SET_OF_LIST = prove
 (`!P l. ALL P l <=> !(x:A). x IN set_of_list l ==> P x`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; ALL; NOT_IN_EMPTY];
   REWRITE_TAC [set_of_list; ALL; IN_INSERT] THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
    [ASM_REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC];
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     REWRITE_TAC [];
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC []]]]);;

export_thm ALL_SET_OF_LIST;;

let EX_SET_OF_LIST = prove
 (`!P l. EX P l <=> ?(x:A). x IN set_of_list l /\ P x`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; EX; NOT_IN_EMPTY];
   REWRITE_TAC [set_of_list; EX; IN_INSERT] THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THENL
    [EXISTS_TAC `h:A` THEN
     ASM_REWRITE_TAC [];
     EXISTS_TAC `x:A` THEN
     ASM_REWRITE_TAC []];
    REPEAT STRIP_TAC THENL
    [FIRST_X_ASSUM SUBST_VAR_TAC THEN
     ASM_REWRITE_TAC [];
     DISJ2_TAC THEN
     EXISTS_TAC `x:A` THEN
     ASM_REWRITE_TAC []]]]);;

export_thm EX_SET_OF_LIST;;

(* ------------------------------------------------------------------------- *)
(* Filter.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-filter-def";;

let (FILTER_NIL,FILTER_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!P. FILTER (P:A->bool) [] = []) /\
     (!P h t. FILTER (P:A->bool) (CONS h t) =
        if P h then CONS h (FILTER P t) else FILTER P t)` in
  CONJ_PAIR def;;

export_thm FILTER_NIL;;
export_thm FILTER_CONS;;

let FILTER = CONJ FILTER_NIL FILTER_CONS;;

logfile "list-filter-thm";;

let FILTER_APPEND = prove
 (`!P l1 l2.
     FILTER (P:A->bool) (APPEND l1 l2) =
     APPEND (FILTER P l1) (FILTER P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm FILTER_APPEND;;

let FILTER_MAP = prove
 (`!P (f:A->B) l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FILTER; o_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP]);;

export_thm FILTER_MAP;;

let LENGTH_FILTER = prove
 (`!p (l : A list). LENGTH (FILTER p l) <= LENGTH l`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [FILTER; LE_REFL];
   REWRITE_TAC [FILTER] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `SUC (LENGTH (FILTER p (t : A list)))` THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL
    [REWRITE_TAC [LENGTH; LE_REFL];
     MATCH_ACCEPT_TAC SUC_LE];
    ASM_REWRITE_TAC [LENGTH; LE_SUC]]]);;

export_thm LENGTH_FILTER;;

let SET_OF_LIST_FILTER = prove
 (`!p (l : A list). set_of_list (FILTER p l) SUBSET set_of_list l`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [FILTER; SUBSET_REFL];
   REWRITE_TAC [FILTER] THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `h INSERT set_of_list (FILTER p (t : A list))` THEN
   CONJ_TAC THENL
   [COND_CASES_TAC THENL
    [REWRITE_TAC [set_of_list; SUBSET_REFL];
     ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
     REWRITE_TAC [SUBSET_UNION]];
    REWRITE_TAC [set_of_list] THEN
    ONCE_REWRITE_TAC [GSYM INSERT_UNION_SING] THEN
    ASM_REWRITE_TAC [UNION_SUBSET; SUBSET_UNION] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `set_of_list (t : A list)` THEN
    ASM_REWRITE_TAC [UNION_SUBSET; SUBSET_UNION]]]);;

export_thm SET_OF_LIST_FILTER;;

(* ------------------------------------------------------------------------- *)
(* Last.                                                                     *)
(* ------------------------------------------------------------------------- *)

logfile "list-last-def";;

let LAST = new_recursive_definition list_RECURSION
  `!h t. LAST (CONS (h:A) t) = if t = [] then h else LAST t`;;

export_thm LAST;;

logfile "list-last-thm";;

let LAST_SING = prove
 (`!(h:A). LAST [h] = h`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

export_thm LAST_SING;;

let LAST_MULTIPLE = prove
 (`!h k t. LAST (CONS (h:A) (CONS k t)) = LAST (CONS k t)`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

export_thm LAST_MULTIPLE;;

let LAST_CLAUSES = CONJ LAST_SING LAST_MULTIPLE;;

let LAST_APPEND = prove
 (`!(p:A list) q. LAST (APPEND p q) = if q = [] then LAST p else LAST q`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LAST; APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

export_thm LAST_APPEND;;

let LAST_SET_OF_LIST = prove
 (`!(l : A list). ~(l = []) ==> LAST l IN set_of_list l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [];
   STRIP_TAC THEN
   REWRITE_TAC [LAST; set_of_list; IN_INSERT] THEN
   COND_CASES_TAC THENL
   [DISJ1_TAC THEN
    REFL_TAC;
    DISJ2_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm LAST_SET_OF_LIST;;

(* ------------------------------------------------------------------------- *)
(* Reverse.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "list-reverse-def";;

let (REVERSE_NIL,REVERSE_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(REVERSE ([] : A list) = []) /\
     (!x l. REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])` in
  CONJ_PAIR def;;

export_thm REVERSE_NIL;;
export_thm REVERSE_CONS;;

let REVERSE = CONJ REVERSE_NIL REVERSE_CONS;;

logfile "list-reverse-thm";;

let REVERSE_APPEND = prove
 (`!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

export_thm REVERSE_APPEND;;

let REVERSE_REVERSE = prove
 (`!l:A list. REVERSE (REVERSE l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND; APPEND]);;

export_thm REVERSE_REVERSE;;

let LENGTH_REVERSE = prove
 (`!l:A list. LENGTH (REVERSE l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [LENGTH; REVERSE; LENGTH_APPEND; ADD_CLAUSES]);;

export_thm LENGTH_REVERSE;;

let SET_OF_LIST_REVERSE = prove
 (`!l:A list. set_of_list (REVERSE l) = set_of_list l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [set_of_list; REVERSE; SET_OF_LIST_APPEND] THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  MATCH_ACCEPT_TAC INSERT_UNION_SING);;

export_thm SET_OF_LIST_REVERSE;;

(* ------------------------------------------------------------------------- *)
(* fold.                                                                     *)
(* ------------------------------------------------------------------------- *)

logfile "list-fold-def";;

let (foldr_nil,foldr_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!f b. foldr (f : A -> B -> B) (b : B) ([] : A list) = b) /\
     (!f b h t.
        foldr (f : A -> B -> B) (b : B) (CONS (h : A) t) =
        f h (foldr f b t))` in
  CONJ_PAIR def;;

export_thm foldr_nil;;
export_thm foldr_cons;;

let foldr_def = CONJ foldr_nil foldr_cons;;

let foldl_def = new_definition
  `!(f : B -> A -> B) b l.
      foldl f b l = foldr (c_comb f) b (REVERSE l)`;;

export_thm foldl_def;;

logfile "list-fold-thm";;

let foldr_with_cons = prove
  (`!(l1 : A list) l2. foldr CONS l2 l1 = APPEND l1 l2`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
   LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC [foldr_def; APPEND];
    ASM_REWRITE_TAC [foldr_def; APPEND]]);;

export_thm foldr_with_cons;;

let foldr_with_cons_nil = prove
  (`!(l : A list). foldr CONS [] l = l`,
   REWRITE_TAC [foldr_with_cons; APPEND_NIL]);;

export_thm foldr_with_cons_nil;;

let foldr_append = prove
  (`!(f : A -> B -> B) b l1 l2.
      foldr f b (APPEND l1 l2) = foldr f (foldr f b l2) l1`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
   LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC [foldr_def; APPEND];
    ASM_REWRITE_TAC [foldr_def; APPEND]]);;

export_thm foldr_append;;

let foldr_append_assoc = prove
  (`!g (f : A -> B -> B) b l1 l2.
      (!s. g b s = s) /\
      (!x s1 s2. g (f x s1) s2 = f x (g s1 s2)) ==>
      (foldr f b (APPEND l1 l2) = g (foldr f b l1) (foldr f b l2))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [foldr_append] THEN
   SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
   LIST_INDUCT_TAC THENL
   [ASM_REWRITE_TAC [foldr_def];
    ASM_REWRITE_TAC [foldr_def]]);;

export_thm foldr_append_assoc;;

let foldl_nil = prove
  (`!(f : B -> A -> B) b. foldl f b [] = b`,
   REWRITE_TAC [foldl_def; REVERSE; foldr_def]);;

export_thm foldl_nil;;

let foldl_cons = prove
  (`!(f : B -> A -> B) b h t. foldl f b (CONS h t) = foldl f (f b h) t`,
   REWRITE_TAC [foldl_def; REVERSE; foldr_append; foldr_def; c_comb]);;

export_thm foldl_cons;;

let foldl_with_cons = prove
  (`!(l1 : A list) l2. foldl (c_comb CONS) l2 l1 = APPEND (REVERSE l1) l2`,
   REWRITE_TAC [foldl_def; cc_eq_id; foldr_with_cons]);;

export_thm foldl_with_cons;;

let foldl_with_cons_nil = prove
  (`!(l : A list). foldl (c_comb CONS) [] l = REVERSE l`,
   REWRITE_TAC [foldl_with_cons; APPEND_NIL]);;

export_thm foldl_with_cons_nil;;

let foldr_reverse = prove
  (`!(f : A -> B -> B) b l. foldr f b (REVERSE l) = foldl (c_comb f) b l`,
   REWRITE_TAC [foldl_def; cc_eq_id]);;

export_thm foldr_reverse;;

let foldl_reverse = prove
  (`!(f : B -> A -> B) b l. foldl f b (REVERSE l) = foldr (c_comb f) b l`,
   REWRITE_TAC [foldl_def; REVERSE_REVERSE]);;

export_thm foldl_reverse;;

let foldl_append = prove
  (`!(f : B -> A -> B) b l1 l2.
      foldl f b (APPEND l1 l2) = foldl f (foldl f b l1) l2`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [foldl_def; REVERSE_APPEND; foldr_append]);;

export_thm foldl_append;;

let foldl_append_assoc = prove
  (`!g (f : B -> A -> B) b l1 l2.
      (!s. g s b = s) /\
      (!s1 s2 x. g s1 (f s2 x) = f (g s1 s2) x) ==>
      (foldl f b (APPEND l1 l2) = g (foldl f b l1) (foldl f b l2))`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [foldl_def; REVERSE_APPEND] THEN
   MATCH_MP_TAC foldr_append_assoc THEN
   ASM_REWRITE_TAC [c_comb]);;

export_thm foldl_append_assoc;;

(* ------------------------------------------------------------------------- *)
(* nth.                                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "list-nth-def";;

let (EL_0,EL_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!l. EL 0 (l : A list) = HD l) /\
     (!n l. EL (SUC n) (l : A list) = EL n (TL l))` in
  let zero = prove
    (`!(h:A) t. EL 0 (CONS h t) = h`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!(h:A) t n. n < LENGTH t ==> EL (SUC n) (CONS h t) = EL n t`,
     REWRITE_TAC [def; TL]) in
  (zero,suc);;

export_thm EL_0;;
export_thm EL_SUC;;

let EL = CONJ EL_0 EL_SUC;;

logfile "list-nth-thm";;

let EL_APPEND = prove
 (`!k l m.
     k < LENGTH l + LENGTH m ==>
     EL k (APPEND l m) = if k < LENGTH l then EL k (l : A list)
                         else EL (k - LENGTH l) m`,
  INDUCT_TAC THENL
  [LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT_REFL; SUB_0; APPEND];
    REWRITE_TAC [APPEND; EL_0; LENGTH; LT_0]];
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT; SUB_0; APPEND];
    POP_ASSUM (K ALL_TAC) THEN
    GEN_TAC THEN
    REWRITE_TAC [LENGTH; ADD; LT_SUC; APPEND] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`h:A`; `APPEND (t : A list) m`; `k : num`] EL_SUC) THEN
    ASM_REWRITE_TAC [LENGTH_APPEND] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`t : A list`; `m : A list`]) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    COND_CASES_TAC THENL
    [ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC EL_SUC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC [] THEN
     AP_THM_TAC THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC SUB_SUC THEN
     ASM_REWRITE_TAC [GSYM NOT_LT]]]]);;

export_thm EL_APPEND;;

let LAST_EL = prove
 (`!l. ~((l : A list) = []) ==> LAST l = EL (LENGTH l - 1) l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [];
   REWRITE_TAC [NOT_CONS_NIL; LAST; LENGTH] THEN
   POP_ASSUM MP_TAC THEN
   COND_CASES_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [LENGTH; SUB_REFL; ONE; EL_0];
    REWRITE_TAC [SUC_SUB1] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (SPEC `LENGTH (t : A list)` num_CASES) THEN
    STRIP_TAC THENL
    [POP_ASSUM MP_TAC THEN
     ASM_REWRITE_TAC [LENGTH_EQ_NIL];
     ASM_REWRITE_TAC [SUC_SUB1] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC EL_SUC THEN
     ASM_REWRITE_TAC [SUC_LT]]]]);;

export_thm LAST_EL;;

let nth_eq = prove
  (`!l (m : A list).
      LENGTH l = LENGTH m /\
      (!i. i < LENGTH l ==> EL i l = EL i m) ==>
      l = m`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LENGTH_EQ_NIL] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; SUC_INJ; CONS_11] THEN
     REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `0` th)) THEN
      REWRITE_TAC [LT_0; EL_0];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `SUC i` th)) THEN
      ASM_REWRITE_TAC [LT_SUC] THEN
      SUBGOAL_THEN
        `!(a:A) b c d. (a = c) /\ (b = d) ==> ((a = b) ==> (c = d))`
        MATCH_MP_TAC THENL
      [POP_ASSUM_LIST (K ALL_TAC) THEN
       REPEAT STRIP_TAC THEN
       REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
       REFL_TAC;
       CONJ_TAC THENL
       [MATCH_MP_TAC EL_SUC THEN
        ASM_REWRITE_TAC [];
        MATCH_MP_TAC EL_SUC THEN
        FIRST_ASSUM ACCEPT_TAC]]]]]);;

export_thm nth_eq;;

let nth_map = prove
  (`!f l i. i < LENGTH l ==> EL i (MAP (f : A -> B) l) = f (EL i l)`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT];
    REWRITE_TAC [LENGTH; MAP] THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [EL_0];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LT_SUC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN
       `!(a:B) b c d. (c = a) /\ (d = b) ==> ((a = b) ==> (c = d))`
       MATCH_MP_TAC THENL
     [POP_ASSUM_LIST (K ALL_TAC) THEN
      REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
      REFL_TAC;
      CONJ_TAC THENL
      [MATCH_MP_TAC EL_SUC THEN
       ASM_REWRITE_TAC [LENGTH_MAP];
       AP_TERM_TAC THEN
       MATCH_MP_TAC EL_SUC THEN
       FIRST_ASSUM ACCEPT_TAC]]]]);;

export_thm nth_map;;

let EL_SET_OF_LIST = prove
 (`!(l : A list) i. i < LENGTH l ==> EL i l IN set_of_list l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; LT];
   REWRITE_TAC [LENGTH; set_of_list; IN_INSERT] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [EL_0];
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [LT_SUC] THEN
    STRIP_TAC THEN
    DISJ2_TAC THEN
    ASM_SIMP_TAC [EL_SUC]]]);;

export_thm EL_SET_OF_LIST;;

let SET_OF_LIST_EL = prove
 (`!(x : A) l. x IN set_of_list l <=> ?i. i < LENGTH l /\ x = EL i l`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [SPEC_TAC (`l : A list`,`l : A list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [set_of_list; NOT_IN_EMPTY];
    REWRITE_TAC [set_of_list; IN_INSERT] THEN
    STRIP_TAC THENL
    [FIRST_X_ASSUM SUBST_VAR_TAC THEN
     EXISTS_TAC `0` THEN
     REWRITE_TAC [LENGTH; LT_0; EL_0];
     FIRST_X_ASSUM
       (fun th -> FIRST_X_ASSUM (fun th' -> STRIP_ASSUME_TAC (MP th th'))) THEN
     FIRST_X_ASSUM SUBST_VAR_TAC THEN
     EXISTS_TAC `SUC i` THEN
     ASM_REWRITE_TAC [LENGTH; LT_SUC] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC EL_SUC THEN
     FIRST_ASSUM ACCEPT_TAC]];
   STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   MATCH_MP_TAC EL_SET_OF_LIST THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm SET_OF_LIST_EL;;

let ALL_EL = prove
 (`!P (l : A list). ALL P l <=> !i. i < LENGTH l ==> P (EL i l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL_SET_OF_LIST] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_MP_TAC EL_SET_OF_LIST THEN
   FIRST_ASSUM ACCEPT_TAC;
   REWRITE_TAC [SET_OF_LIST_EL] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm ALL_EL;;

let EX_EL = prove
 (`!P (l : A list). EX P l <=> ?i. i < LENGTH l /\ P (EL i l)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EX_SET_OF_LIST] THEN
  EQ_TAC THENL
  [REWRITE_TAC [SET_OF_LIST_EL] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   EXISTS_TAC `i:num` THEN
   ASM_REWRITE_TAC [];
   REPEAT STRIP_TAC THEN
   EXISTS_TAC `EL i (l : A list)` THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EL_SET_OF_LIST THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm EX_EL;;

(* ------------------------------------------------------------------------- *)
(* Replicate.                                                                *)
(* ------------------------------------------------------------------------- *)

logfile "list-replicate-def";;

let (REPLICATE_0,REPLICATE_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!x. REPLICATE 0 (x:A) = []) /\
     (!x n. REPLICATE (SUC n) (x:A) = CONS x (REPLICATE n x))` in
  CONJ_PAIR def;;

export_thm REPLICATE_0;;
export_thm REPLICATE_SUC;;

let REPLICATE = CONJ REPLICATE_0 REPLICATE_SUC;;

logfile "list-replicate-thm";;

let LENGTH_REPLICATE = prove
 (`!n x. LENGTH (REPLICATE n (x:A)) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE]);;

export_thm LENGTH_REPLICATE;;

let nth_replicate = prove
  (`!n x i. i < n ==> EL i (REPLICATE n (x : A)) = x`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    REPEAT GEN_TAC THEN
    MP_TAC (SPEC `i : num` num_CASES) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [EL_0; REPLICATE];
     POP_ASSUM SUBST_VAR_TAC THEN
     ASM_REWRITE_TAC [REPLICATE; LT_SUC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPECL [`x:A`; `n':num`]) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) THEN
     MATCH_MP_TAC EL_SUC THEN
     ASM_REWRITE_TAC [LENGTH_REPLICATE]]]);;

export_thm nth_replicate;;

let SET_OF_LIST_REPLICATE = prove
 (`!n (x : A). set_of_list (REPLICATE n x) = if n = 0 then {} else {x}`,
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE; set_of_list];
   GEN_TAC THEN
   ASM_REWRITE_TAC [REPLICATE; set_of_list; NOT_SUC] THEN
   COND_CASES_TAC THENL
   [REFL_TAC;
    REWRITE_TAC [INSERT_INSERT]]]);;

export_thm SET_OF_LIST_REPLICATE;;

(* ------------------------------------------------------------------------- *)
(* Member.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-member-def";;

let (MEM_NIL,MEM_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!x. MEM (x:A) [] <=> F) /\
     (!x h t. MEM (x:A) (CONS h t) <=> (x = h) \/ MEM x t)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm MEM_NIL;;
export_thm MEM_CONS;;

let MEM = CONJ MEM_NIL MEM_CONS;;

logfile "list-member-thm";;

let ALL_IMP = prove
 (`!P Q l. (!x. MEM (x:A) l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

export_thm ALL_IMP;;

let EX_IMP = prove
 (`!P Q l. (!x. MEM (x:A) l /\ P x ==> Q x) /\ EX P l ==> EX Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; EX] THEN ASM_MESON_TAC[]);;

export_thm EX_IMP;;

let ALL_MEM = prove
 (`!P l. (!x. MEM (x:A) l ==> P x) <=> ALL P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MEM] THEN
  ASM_MESON_TAC[]);;

export_thm ALL_MEM;;

let MEM_APPEND = prove
 (`!x l1 l2. MEM (x:A) (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; DISJ_ACI]);;

export_thm MEM_APPEND;;

let MEM_MAP = prove
 (`!f y l. MEM y (MAP (f:A->B) l) <=> ?x. MEM x l /\ (y = f x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; MAP] THEN MESON_TAC[]);;

export_thm MEM_MAP;;

let MEM_FILTER = prove
 (`!P l x. MEM (x:A) (FILTER P l) <=> P x /\ MEM x l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; FILTER] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[MEM] THEN
  ASM_MESON_TAC[]);;

export_thm MEM_FILTER;;

let EX_MEM = prove
 (`!P l. (?x. P (x:A) /\ MEM x l) <=> EX P l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[EX; MEM] THEN
  ASM_MESON_TAC[]);;

export_thm EX_MEM;;

let MEM_EL = prove
 (`!l n. n < LENGTH (l : A list) ==> MEM (EL n l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJUNCT1 LT; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL_0; EL_SUC; LT_SUC]);;

export_thm MEM_EL;;

let MEM_EXISTS_EL = prove
 (`!l x. MEM (x : A) l <=> ?i. i < LENGTH l /\ x = EL i l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MEM; LENGTH; LT];
   REWRITE_TAC [MEM; LENGTH] THEN
   GEN_TAC THEN
   EQ_TAC THENL
   [STRIP_TAC THENL
    [EXISTS_TAC `0` THEN
     ASM_REWRITE_TAC [LT_0; EL];
     FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
     ASM_REWRITE_TAC [] THEN
     STRIP_TAC THEN
     EXISTS_TAC `SUC i` THEN
     ASM_REWRITE_TAC [LT_SUC] THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC EL_SUC THEN
     FIRST_ASSUM ACCEPT_TAC];
    STRIP_TAC THEN
    MP_TAC (SPEC `i:num` num_CASES) THEN
    STRIP_TAC THENL
    [DISJ1_TAC THEN
     ASM_REWRITE_TAC [EL_0];
     DISJ2_TAC THEN
     UNDISCH_TAC `i < SUC (LENGTH (t : A list))` THEN
     ASM_REWRITE_TAC [LT_SUC] THEN
     STRIP_TAC THEN
     EXISTS_TAC `n:num` THEN
     ASM_REWRITE_TAC [] THEN
     MATCH_MP_TAC EL_SUC THEN
     FIRST_ASSUM ACCEPT_TAC]]]);;

export_thm MEM_EXISTS_EL;;

let MEM_LIST_OF_SET = prove
 (`!(s : A set). FINITE s ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN
  DISCH_THEN (MP_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  DISCH_THEN
    (fun th -> GEN_REWRITE_TAC (BINDER_CONV o funpow 2 RAND_CONV) [GSYM th]) THEN
  SPEC_TAC (`list_of_set (s : A set)`, `l : A list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MEM; set_of_list; NOT_IN_EMPTY];
   ASM_REWRITE_TAC[MEM; set_of_list; IN_INSERT]]);;

export_thm MEM_LIST_OF_SET;;

let IN_SET_OF_LIST = prove
 (`!(x:A) l. MEM x l <=> x IN (set_of_list l)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; MEM; set_of_list];
   ASM_REWRITE_TAC [IN_INSERT; MEM; set_of_list]]);;

export_thm IN_SET_OF_LIST;;

let MEM_REVERSE = prove
 (`!l x. MEM (x : A) (REVERSE l) <=> MEM x l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE] THEN
  REWRITE_TAC [MEM_APPEND] THEN
  ONCE_REWRITE_TAC [DISJ_SYM] THEN
  REWRITE_TAC [GSYM MEM_APPEND] THEN
  ASM_REWRITE_TAC [APPEND; MEM]);;

export_thm MEM_REVERSE;;

(* ------------------------------------------------------------------------- *)
(* Concat.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-concat-def";;

let (concat_nil,concat_cons) =
  let def = new_recursive_definition list_RECURSION
    `(concat [] = ([] : A list)) /\
     (!h t. concat (CONS (h : A list) t) = APPEND h (concat t))` in
  CONJ_PAIR def;;

export_thm concat_nil;;
export_thm concat_cons;;

let concat_def = CONJ concat_nil concat_cons;;

logfile "list-concat-thm";;

let null_concat = prove
  (`!l. NULL (concat l) <=> ALL NULL (l : (A list) list)`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [concat_def; ALL; NULL; NULL_APPEND]);;

export_thm null_concat;;

(* ------------------------------------------------------------------------- *)
(* Take and drop.                                                            *)
(* ------------------------------------------------------------------------- *)

logfile "list-take-drop-def";;

let (take_0,take_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!l. take 0 (l : A list) = []) /\
     (!n l. take (SUC n) (l : A list) = CONS (HD l) (take n (TL l)))` in
  let zero = prove
    (`!l. take 0 (l : A list) = []`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!n h t.
        n <= LENGTH t ==>
        take (SUC n) (CONS h t) = CONS (h : A) (take n t)`,
     REWRITE_TAC [def; HD; TL]) in
  (zero,suc);;

export_thm take_0;;
export_thm take_suc;;

let take_def = CONJ take_0 take_suc;;

let (drop_0,drop_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!l. drop 0 (l : A list) = l) /\
     (!n l. drop (SUC n) (l : A list) = drop n (TL l))` in
  let zero = prove
    (`!l. drop 0 (l : A list) = l`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!n h t.
        n <= LENGTH t ==>
        drop (SUC n) (CONS (h : A) t) = drop n t`,
     REWRITE_TAC [def; TL]) in
  (zero,suc);;

export_thm drop_0;;
export_thm drop_suc;;

let drop_def = CONJ drop_0 drop_suc;;

logfile "list-take-drop-thm";;

let take_drop = prove
  (`!n (l : A list). n <= LENGTH l ==> APPEND (take n l) (drop n l) = l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [take_0; drop_0; APPEND];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC] THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] drop_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [APPEND; CONS_11] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm take_drop;;

let length_take = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (take n l) = n`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; take_def];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC] THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [LENGTH; SUC_INJ] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm length_take;;

let length_drop = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (drop n l) = LENGTH l - n`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n:num`; `l:A list`] take_drop) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th]))) THEN
   REWRITE_TAC [LENGTH_APPEND] THEN
   MP_TAC (SPECL [`n:num`; `l:A list`] length_take) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUB2]);;

export_thm length_drop;;

let nth_take = prove
  (`!n l i. n <= LENGTH (l : A list) /\ i < n ==> EL i (take n l) = EL i l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC; take_def] THEN
     INDUCT_TAC THENL
     [STRIP_TAC THEN
      MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [EL_0];
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [LT_SUC] THEN
      STRIP_TAC THEN
      MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `i < LENGTH (t : A list)` ASSUME_TAC THENL
      [MATCH_MP_TAC LTE_TRANS THEN
       EXISTS_TAC `n : num` THEN
       ASM_REWRITE_TAC [];
       MP_TAC (SPECL [`h:A`; `t:A list`; `i:num`] EL_SUC) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC (SPECL [`h:A`; `take n (t:A list)`; `i:num`] EL_SUC) THEN
       MP_TAC (SPECL [`n:num`; `t:A list`] length_take) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC []]]]]);;

export_thm nth_take;;

let nth_drop = prove
  (`!n (l : A list) i. n + i < LENGTH l ==> EL i (drop n l) = EL (n + i) l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [ADD; drop_def];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LT];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LT_SUC; ADD] THEN
     REPEAT STRIP_TAC THEN
     MP_TAC (SPECL [`h:A`; `t:A list`; `n + i : num`] EL_SUC) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPECL [`t : A list`; `i : num`]) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (SUBST1_TAC o SYM) THEN
     AP_TERM_TAC THEN
     MATCH_MP_TAC drop_suc THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `SUC (n + i)` THEN
     ASM_REWRITE_TAC [LE_SUC_LT] THEN
     REWRITE_TAC [GSYM ADD_SUC; LE_ADD]]]);;

export_thm nth_drop;;

let drop_length = prove
  (`!l. drop (LENGTH l) (l : A list) = []`,
   GEN_TAC THEN
   REWRITE_TAC [GSYM LENGTH_EQ_NIL] THEN
   MP_TAC (SPECL [`LENGTH (l : A list)`; `l : A list`] length_drop) THEN
   REWRITE_TAC [LE_REFL; SUB_REFL]);;

export_thm drop_length;;

let take_length = prove
  (`!l. take (LENGTH l) (l : A list) = l`,
   GEN_TAC THEN
   MP_TAC (SPECL [`LENGTH (l : A list)`; `l : A list`] take_drop) THEN
   REWRITE_TAC [LE_REFL] THEN
   DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) THEN
   REWRITE_TAC [drop_length; APPEND_NIL]);;

export_thm take_length;;

(* ------------------------------------------------------------------------- *)
(* Interval.                                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "list-interval-def";;

let (interval_0,interval_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!m. interval m 0 = []) /\
     (!m n. interval m (SUC n) = CONS m (interval (SUC m) n))` in
  CONJ_PAIR def;;

export_thm interval_0;;
export_thm interval_suc;;

let interval_def = CONJ interval_0 interval_suc;;

logfile "list-interval-thm";;

let length_interval = prove
  (`!m n. LENGTH (interval m n) = n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   SIMP_TAC [LENGTH; interval_def; SUC_INJ]);;

export_thm length_interval;;

let nth_interval = prove
  (`!m n i. i < n ==> EL i (interval m n) = m + i`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    ALL_TAC] THEN
   REWRITE_TAC [interval_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `i : num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [EL_0; ADD_0];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [LT_SUC; ADD_SUC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`SUC m`; `n' : num`]) THEN
    ASM_REWRITE_TAC [ADD] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EL_SUC THEN
    ASM_REWRITE_TAC [length_interval]]);;

export_thm nth_interval;;

(* ------------------------------------------------------------------------- *)
(* Zipwith.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "list-zipwith-def";;

let (zipwith_nil,zipwith_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!f l. zipwith (f : A -> B -> C) [] l = []) /\
     (!f h t l.
        zipwith (f : A -> B -> C) (CONS h t) l =
        CONS (f h (HD l)) (zipwith f t (TL l)))` in
  let znil = prove
    (`!f. zipwith (f : A -> B -> C) [] [] = []`,
     REWRITE_TAC [def])
  and zcons = prove
    (`!f h1 h2 t1 t2.
        LENGTH t1 = LENGTH t2 ==>
        zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
        CONS (f h1 h2) (zipwith f t1 t2)`,
     REWRITE_TAC [def; HD; TL]) in
  (znil,zcons);;

export_thm zipwith_nil;;
export_thm zipwith_cons;;

let zipwith_def = CONJ zipwith_nil zipwith_cons;;

logfile "list-zipwith-thm";;

let length_zipwith = prove
  (`!(f : A -> B -> C) l1 l2 n.
      LENGTH l1 = n /\ LENGTH l2 = n ==> LENGTH (zipwith f l1 l2) = n`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   INDUCT_TAC THEN
   REWRITE_TAC [NOT_SUC; LENGTH] THENL
   [REWRITE_TAC [zipwith_nil; LENGTH];
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [SUC_INJ] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`f : A -> B -> C`; `h : A`; `h' : B`;
                   `t : A list`; `t' : B list`] zipwith_cons) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm length_zipwith;;

(* ------------------------------------------------------------------------- *)
(* Nub.                                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "list-nub-def";;

let (setify_nil,setify_cons) =
  let def = new_recursive_definition list_RECURSION
    `(setify ([] : A list) = []) /\
     (!h t.
        setify (CONS (h:A) t) =
        if MEM h t then setify t else CONS h (setify t))` in
  CONJ_PAIR def;;

export_thm setify_nil;;
export_thm setify_cons;;

let setify_def = CONJ setify_nil setify_cons;;

let nub_def = new_definition
  `!l. nub (l : A list) = REVERSE (setify (REVERSE l))`;;

export_thm nub_def;;

logfile "list-nub-thm";;

let length_setify = prove
  (`!l. LENGTH (setify (l : A list)) <= LENGTH l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [LENGTH; setify_def; LE_REFL] THEN
   BOOL_CASES_TAC `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [LE];
    ASM_REWRITE_TAC [LE_SUC; LENGTH]]);;

export_thm length_setify;;

let mem_setify = prove
  (`!l x. MEM (x : A) (setify l) <=> MEM x l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [MEM; setify_def] THEN
   GEN_TAC THEN
   ASM_CASES_TAC `(x : A) = h` THENL
   [ASM_REWRITE_TAC [] THEN
    ASM_CASES_TAC `MEM (h : A) t` THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [MEM]];
    ASM_REWRITE_TAC [] THEN
    BOOL_CASES_TAC `MEM (h : A) t` THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [MEM]]]);;

export_thm mem_setify;;

let set_of_list_setify = prove
  (`!(l : A list). set_of_list (setify l) = set_of_list l`,
   REWRITE_TAC [EXTENSION; GSYM IN_SET_OF_LIST; mem_setify]);;

export_thm set_of_list_setify;;

let setify_idempotent = prove
  (`!l. setify (setify l) = setify (l : A list)`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [MEM; setify_def] THEN
   ASM_CASES_TAC `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [setify_def; mem_setify]]);;

export_thm setify_idempotent;;

let length_nub = prove
  (`!l. LENGTH (nub (l : A list)) <= LENGTH l`,
   GEN_TAC THEN
   REWRITE_TAC [nub_def; LENGTH_REVERSE] THEN
   CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM LENGTH_REVERSE])) THEN
   MATCH_ACCEPT_TAC length_setify);;

export_thm length_nub;;

let mem_nub = prove
  (`!l x. MEM (x : A) (nub l) <=> MEM x l`,
   REWRITE_TAC [nub_def; MEM_REVERSE; mem_setify]);;

export_thm mem_nub;;

let set_of_list_nub = prove
  (`!(l : A list). set_of_list (nub l) = set_of_list l`,
   REWRITE_TAC [EXTENSION; GSYM IN_SET_OF_LIST; mem_nub]);;

export_thm set_of_list_nub;;

let nub_idempotent = prove
  (`!l. nub (nub l) = nub (l : A list)`,
   REWRITE_TAC [nub_def; REVERSE_REVERSE; setify_idempotent]);;

export_thm nub_idempotent;;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_cons h t =
  try let cons = mk_const("CONS",[type_of h,aty]) in
      mk_comb(mk_comb(cons,h),t)
  with Failure _ -> failwith "mk_cons";;

let mk_list (tms,ty) =
  try let nil = mk_const("NIL",[ty,aty]) in
      if tms = [] then nil else
      let cons = mk_const("CONS",[ty,aty]) in
      itlist (mk_binop cons) tms nil
  with Failure _ -> failwith "mk_list";;

let mk_flist tms =
  try mk_list(tms,type_of(hd tms))
  with Failure _ -> failwith "mk_flist";;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec LIST_CONV conv tm =
  if is_cons tm then
    COMB2_CONV (RAND_CONV conv) (LIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then REFL tm
  else failwith "LIST_CONV";;

logfile_end ();;

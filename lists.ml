(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2014                         *)
(* ========================================================================= *)

needs "ind_types.ml";;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "list-thm";;

let NOT_CONS_NIL = prove
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC [distinctness "list"]);;

export_thm NOT_CONS_NIL;;

let CONS_11 = prove
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC [injectivity "list"]);;

export_thm CONS_11;;

let list_cases = prove
  (`!(l : A list). l = [] \/ ?h t. l = CONS h t`,
   MATCH_ACCEPT_TAC (prove_cases_thm list_INDUCT));;

export_thm list_cases;;

(* ------------------------------------------------------------------------- *)
(* Standard tactic for list induction using MATCH_MP_TAC list_INDUCT         *)
(* ------------------------------------------------------------------------- *)

let LIST_INDUCT_TAC =
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL [ALL_TAC; GEN_TAC THEN GEN_TAC THEN DISCH_TAC];;

let LIST_CASES_TAC = CASES_TAC list_cases;;

(* ------------------------------------------------------------------------- *)
(* Destructors.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "list-dest-def";;

let HD = new_recursive_definition list_RECURSION
  `!(h : A) t. HD (CONS h t) = h`;;

export_thm HD;;

let TL = new_recursive_definition list_RECURSION
  `!(h : A) t. TL (CONS h t) = t`;;

export_thm TL;;

let (NULL_NIL,NULL_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(NULL ([] : A list) <=> T) /\
     (!(h : A) t. NULL (CONS h t) <=> F)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm NULL_NIL;;
export_thm NULL_CONS;;

let NULL = CONJ NULL_NIL NULL_CONS;;

let (case_list_nil,case_list_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!b f. case_list b f [] = b) /\
     (!b (f : A -> A list -> B) h t. case_list b f (CONS h t) = f h t)` in
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
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [case_list_def]);;

export_thm case_list_id;;

let CONS_HD_TL = prove
 (`!(l : A list). ~NULL l ==> CONS (HD l) (TL l) = l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [NULL; HD; TL]);;

export_thm CONS_HD_TL;;

(* ------------------------------------------------------------------------- *)
(* Length.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-length-def";;

let (LENGTH_NIL,LENGTH_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(LENGTH [] = 0) /\
     (!(h : A) t. LENGTH (CONS h t) = SUC (LENGTH t))` in
  CONJ_PAIR def;;

export_thm LENGTH_NIL;;
export_thm LENGTH_CONS;;

let LENGTH = CONJ LENGTH_NIL LENGTH_CONS;;

logfile "list-length-thm";;

let NULL_LENGTH = prove
 (`!(l : A list). (LENGTH l = 0) <=> NULL l`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [LENGTH; NULL; NOT_SUC]);;

export_thm NULL_LENGTH;;

let LENGTH_EQ_NIL = prove
 (`!(l : A list). (LENGTH l = 0) <=> (l = [])`,
  REWRITE_TAC [NULL_LENGTH; NULL_EQ_NIL]);;

export_thm LENGTH_EQ_NIL;;

let LENGTH_EQ_CONS = prove
 (`!(l : A list) n.
      LENGTH l = SUC n <=> ?h t. (l = CONS h t) /\ (LENGTH t = n)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; NOT_SUC; NOT_CONS_NIL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  GEN_TAC THEN
  REWRITE_TAC [LENGTH; SUC_INJ; CONS_11] THEN
  ASM_CASES_TAC `LENGTH (t : A list) = n` THENL
  [ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `h : A` THEN
   EXISTS_TAC `t : A list` THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [NOT_EXISTS_THM] THEN
   REPEAT STRIP_TAC THEN
   UNDISCH_TAC `~(LENGTH (t : A list) = n)` THEN
   ASM_REWRITE_TAC []]);;

export_thm LENGTH_EQ_CONS;;

let LENGTH_TL = prove
 (`!(l : A list). ~NULL l ==> LENGTH (TL l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN
  REWRITE_TAC [NULL; LENGTH; TL; SUC_SUB1]);;

export_thm LENGTH_TL;;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-set-def";;

let (set_of_list_nil,set_of_list_cons) =
  let def = new_recursive_definition list_RECURSION
    `(set_of_list ([] : A list) = {}) /\
     (!(h : A) t. set_of_list (CONS h t) = h INSERT (set_of_list t))` in
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
   EXISTS_TAC `CONS (x : A) l` THEN
   ASM_REWRITE_TAC [LENGTH; set_of_list] THEN
   MP_TAC (SPECL [`x:A`; `s : A set`] (CONJUNCT2 CARD_CLAUSES)) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (ACCEPT_TAC o SYM)]);;

export_thm LIST_OF_SET_PROPERTIES;;

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

let (MEM_NIL,MEM_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!(x : A). MEM x [] <=> F) /\
     (!(x : A) h t. MEM x (CONS h t) <=> (x = h) \/ MEM x t)` in
  (CONJ_PAIR o PURE_REWRITE_RULE [EQ_CLAUSES]) def;;

export_thm MEM_NIL;;
export_thm MEM_CONS;;

let MEM = CONJ MEM_NIL MEM_CONS;;

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

let NULL_SET_OF_LIST = prove
 (`!(l : A list). set_of_list l = {} <=> NULL l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; NULL];
   REWRITE_TAC [set_of_list; NULL; NOT_INSERT_EMPTY]]);;

export_thm NULL_SET_OF_LIST;;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!(l : A list). set_of_list l = {} <=> l = []`,
  REWRITE_TAC [NULL_SET_OF_LIST; NULL_EQ_NIL]);;

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

let NOT_EX = prove
 (`!p (l : A list). ~(EX p l) <=> ALL (\x. ~(p x)) l`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [EX; ALL];
   ASM_REWRITE_TAC [EX; ALL; DE_MORGAN_THM]]);;

export_thm NOT_EX;;

let NOT_ALL_NOT = prove
 (`!p (l : A list). ~ALL (\x. ~(p x)) l <=> EX p l`,
  REWRITE_TAC [GSYM NOT_EX]);;

export_thm NOT_ALL_NOT;;

let NOT_ALL = prove
 (`!p (l : A list). ~(ALL p l) <=> EX (\x. ~(p x)) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [GSYM NOT_ALL_NOT] THEN
  CONV_TAC (DEPTH_CONV ETA_CONV) THEN
  REFL_TAC);;

export_thm NOT_ALL;;

let NOT_EX_NOT = prove
 (`!p (l : A list). ~EX (\x. ~(p x)) l <=> ALL p l`,
  REWRITE_TAC [GSYM NOT_ALL]);;

export_thm NOT_EX_NOT;;

let ALL_SET_OF_LIST = prove
 (`!p (l : A list). ALL p l <=> !x. x IN set_of_list l ==> p x`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; ALL; NOT_IN_EMPTY];
   ALL_TAC] THEN
  REWRITE_TAC [set_of_list; ALL; IN_INSERT] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC [];
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISJ1_TAC THEN
    REFL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    DISJ2_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]]);;

export_thm ALL_SET_OF_LIST;;

let EX_SET_OF_LIST = prove
 (`!p (l : A list). EX p l <=> ?x. x IN set_of_list l /\ p x`,
  REPEAT GEN_TAC THEN
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM NOT_NOT_THM))) THEN
  PURE_REWRITE_TAC [NOT_EX] THEN
  REWRITE_TAC [ALL_SET_OF_LIST; NOT_FORALL_THM; NOT_IMP]);;

export_thm EX_SET_OF_LIST;;

let MEM_SET_OF_LIST = prove
 (`!l (x : A). MEM x l <=> x IN (set_of_list l)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; MEM; set_of_list];
   ASM_REWRITE_TAC [IN_INSERT; MEM; set_of_list]]);;

export_thm MEM_SET_OF_LIST;;

let MEM_LIST_OF_SET = prove
 (`!(s : A set). FINITE s ==> !x. MEM x (list_of_set s) <=> x IN s`,
  GEN_TAC THEN
  DISCH_THEN (ASSUME_TAC o MATCH_MP SET_OF_LIST_OF_SET) THEN
  ASM_REWRITE_TAC [MEM_SET_OF_LIST]);;

export_thm MEM_LIST_OF_SET;;

let ALL_T = prove
 (`!(l : A list). ALL (\x. T) l`,
  REWRITE_TAC [ALL_SET_OF_LIST]);;

export_thm ALL_T;;

let ALL_F = prove
 (`!(l : A list). ALL (\x. F) l <=> NULL l`,
  REWRITE_TAC
    [ALL_SET_OF_LIST; GSYM NULL_SET_OF_LIST; GSYM NOT_EXISTS_THM;
     MEMBER_NOT_EMPTY]);;

export_thm ALL_F;;

let ALL_MP = prove
 (`!p q (l : A list).
     ALL (\x. p x ==> q x) l /\ ALL p l ==> ALL q l`,
  REWRITE_TAC [ALL_SET_OF_LIST; IMP_IMP] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm ALL_MP;;

let AND_ALL = prove
 (`!p q (l : A list).
    ALL (\x. p x /\ q x) l <=> ALL p l /\ ALL q l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL_SET_OF_LIST; IMP_IMP] THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x : A`) THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm AND_ALL;;

let EXISTS_EX = prove
 (`!(p : A -> B -> bool) l. (?x. EX (p x) l) <=> EX (\y. ?x. p x y) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EX_SET_OF_LIST; IMP_IMP; RIGHT_AND_EXISTS_THM] THEN
  MATCH_ACCEPT_TAC SWAP_EXISTS_THM);;

export_thm EXISTS_EX;;

let FORALL_ALL = prove
 (`!(p : A -> B -> bool) l. (!x. ALL (p x) l) <=> ALL (\y. !x. p x y) l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL_SET_OF_LIST; RIGHT_IMP_FORALL_THM] THEN
  MATCH_ACCEPT_TAC SWAP_FORALL_THM);;

export_thm FORALL_ALL;;

let ALL_IMP = prove
 (`!p q (l : A list).
     (!x. MEM x l /\ p x ==> q x) /\ ALL p l ==> ALL q l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL_SET_OF_LIST; MEM_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm ALL_IMP;;

let EX_IMP = prove
 (`!p q (l : A list).
    (!x. MEM x l /\ p x ==> q x) /\ EX p l ==> EX q l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [EX_SET_OF_LIST; MEM_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `x : A` THEN
  CONJ_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   CONJ_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm EX_IMP;;

let ALL_MEM = prove
 (`!p (l : A list). (!x. MEM x l ==> p x) <=> ALL p l`,
  REWRITE_TAC [ALL_SET_OF_LIST; MEM_SET_OF_LIST]);;

export_thm ALL_MEM;;

let EX_MEM = prove
 (`!p (l : A list). (?x. MEM x l /\ p x) <=> EX p l`,
  REWRITE_TAC [MEM_SET_OF_LIST; EX_SET_OF_LIST]);;

export_thm EX_MEM;;

let MONO_ALL = prove
 (`!p q (l : A list). (!x. p x ==> q x) ==> ALL p l ==> ALL q l`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [ALL_SET_OF_LIST] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

monotonicity_theorems := [MONO_ALL] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Appending lists.                                                          *)
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

let (concat_nil,concat_cons) =
  let def = new_recursive_definition list_RECURSION
    `(concat [] = ([] : A list)) /\
     (!h t. concat (CONS (h : A list) t) = APPEND h (concat t))` in
  CONJ_PAIR def;;

export_thm concat_nil;;
export_thm concat_cons;;

let concat_def = CONJ concat_nil concat_cons;;

logfile "list-append-thm";;

let APPEND_NIL = prove
 (`!(l : A list). APPEND l [] = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_NIL;;

let APPEND_ASSOC = prove
 (`!(l1 : A list) l2 l3.
     APPEND l1 (APPEND l2 l3) = APPEND (APPEND l1 l2) l3`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_ASSOC;;

let APPEND_SING = prove
 (`!(h : A) t. APPEND [h] t = CONS h t`,
  REWRITE_TAC [APPEND]);;

export_thm APPEND_SING;;

let LENGTH_APPEND = prove
 (`!(l1 : A list) l2. LENGTH (APPEND l1 l2) = LENGTH l1 + LENGTH l2`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND; LENGTH; ADD_CLAUSES]);;

export_thm LENGTH_APPEND;;

let NULL_APPEND = prove
 (`!(l1 : A list) l2. NULL (APPEND l1 l2) <=> NULL l1 /\ NULL l2`,
  REWRITE_TAC [GSYM NULL_LENGTH; LENGTH_APPEND; ADD_EQ_0]);;

export_thm NULL_APPEND;;

let APPEND_EQ_NIL = prove
 (`!(l1 : A list) l2. (APPEND l1 l2 = []) <=> (l1 = []) /\ (l2 = [])`,
  REWRITE_TAC [GSYM NULL_EQ_NIL; NULL_APPEND]);;

export_thm APPEND_EQ_NIL;;

let APPEND_LCANCEL_IMP = prove
 (`!(l : A list) l1 l2. APPEND l l1 = APPEND l l2 ==> l1 = l2`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NIL_APPEND];
   ASM_REWRITE_TAC [CONS_APPEND; CONS_11]]);;

export_thm APPEND_LCANCEL_IMP;;

let APPEND_LCANCEL = prove
 (`!(l : A list) l1 l2. APPEND l l1 = APPEND l l2 <=> l1 = l2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC APPEND_LCANCEL_IMP;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

export_thm APPEND_LCANCEL;;

let APPEND_RCANCEL_IMP = prove
 (`!(l : A list) l1 l2. APPEND l1 l = APPEND l2 l ==> l1 = l2`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [LIST_INDUCT_TAC THENL
   [REWRITE_TAC [];
    POP_ASSUM_LIST (K ALL_TAC) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
      `LENGTH (APPEND (CONS h t) l : A list) = LENGTH (APPEND [] l : A list)`
      MP_TAC THENL
    [ASM_REWRITE_TAC [];
     REWRITE_TAC
       [LENGTH_APPEND; ZERO_ADD; EQ_ADD_RCANCEL_0; LENGTH; NOT_SUC]]];
   LIST_INDUCT_TAC THENL
   [POP_ASSUM_LIST (K ALL_TAC) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
      `LENGTH (APPEND (CONS h t) l : A list) = LENGTH (APPEND [] l : A list)`
      MP_TAC THENL
    [ASM_REWRITE_TAC [];
     REWRITE_TAC
       [LENGTH_APPEND; ZERO_ADD; EQ_ADD_RCANCEL_0; LENGTH; NOT_SUC]];
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [CONS_APPEND; CONS_11] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]]);;

export_thm APPEND_RCANCEL_IMP;;

let APPEND_RCANCEL = prove
 (`!(l : A list) l1 l2. APPEND l1 l = APPEND l2 l <=> l1 = l2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [MATCH_ACCEPT_TAC APPEND_RCANCEL_IMP;
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC]);;

export_thm APPEND_RCANCEL;;

let APPEND_LINJ = prove
 (`!(l1 : A list) l1' l2 l2'.
     LENGTH l1 = LENGTH l1' /\ APPEND l1 l2 = APPEND l1' l2' ==> l1 = l1'`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`l1' : A list`, `l1' : A list`) THEN
  SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
  LIST_INDUCT_TAC THENL
  [LIST_INDUCT_TAC THENL
   [REWRITE_TAC [];
    REWRITE_TAC [LENGTH_NIL; LENGTH_CONS; NOT_SUC]];
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH_NIL; LENGTH_CONS; NOT_SUC];
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [CONS_APPEND; LENGTH_CONS; SUC_INJ; CONS_11] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]]);;

export_thm APPEND_LINJ;;

let APPEND_RINJ = prove
 (`!(l1 : A list) l1' l2 l2'.
     LENGTH l2 = LENGTH l2' /\ APPEND l1 l2 = APPEND l1' l2' ==> l2 = l2'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l1 : A list) = l1'` (SUBST_VAR_TAC o SYM) THENL
  [MATCH_MP_TAC APPEND_LINJ THEN
   EXISTS_TAC `l2 : A list` THEN
   EXISTS_TAC `l2' : A list` THEN
   ASM_REWRITE_TAC [] THEN
   SUBGOAL_THEN
     `LENGTH (APPEND (l1 : A list) l2) = LENGTH (APPEND (l1' : A list) l2')`
     MP_TAC THENL
   [ASM_REWRITE_TAC [];
    POP_ASSUM (K ALL_TAC) THEN
    ASM_REWRITE_TAC [LENGTH_APPEND; EQ_ADD_RCANCEL]];
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [APPEND_LCANCEL]]);;

export_thm APPEND_RINJ;;

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

let EX_APPEND = prove
 (`!p (l1 : A list) l2. EX p (APPEND l1 l2) <=> EX p l1 \/ EX p l2`,
  REWRITE_TAC
    [EX_SET_OF_LIST; SET_OF_LIST_APPEND; IN_UNION; GSYM EXISTS_OR_THM;
     RIGHT_OR_DISTRIB]);;

export_thm EX_APPEND;;

let ALL_APPEND = prove
 (`!p (l1 : A list) l2. ALL p (APPEND l1 l2) <=> ALL p l1 /\ ALL p l2`,
  REWRITE_TAC [GSYM NOT_EX_NOT; EX_APPEND; DE_MORGAN_THM]);;

export_thm ALL_APPEND;;

let MEM_APPEND = prove
 (`!l1 l2 (x:A). MEM x (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  REWRITE_TAC [MEM_SET_OF_LIST; SET_OF_LIST_APPEND; IN_UNION]);;

export_thm MEM_APPEND;;

let MEM_APPEND_DECOMPOSE_LEFT = prove
 (`!(x:A) l. MEM x l <=> ?l1 l2. ~(MEM x l1) /\ l = APPEND l1 (CONS x l2)`,
  REPEAT STRIP_TAC THEN
  EQ_TAC THENL
  [SPEC_TAC (`l : A list`,`l : A list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [MEM];
    ASM_CASES_TAC `x:A = h` THENL
    [ASM_REWRITE_TAC [MEM] THEN
     EXISTS_TAC `[] : A list` THEN
     EXISTS_TAC `t : A list` THEN
     REWRITE_TAC [MEM; APPEND];
     ASM_REWRITE_TAC [MEM] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM
       (fun th ->
          MP_TAC th THEN
          ANTS_TAC THENL
          [FIRST_ASSUM ACCEPT_TAC;
           STRIP_TAC]) THEN
     POP_ASSUM SUBST_VAR_TAC THEN
     EXISTS_TAC `CONS (h:A) l1` THEN
     EXISTS_TAC `l2 : A list` THEN
     ASM_REWRITE_TAC [MEM; APPEND]]];
   STRIP_TAC THEN
   ASM_REWRITE_TAC [MEM_APPEND; MEM]]);;

export_thm MEM_APPEND_DECOMPOSE_LEFT;;

let null_concat = prove
  (`!l. NULL (concat l) <=> ALL NULL (l : (A list) list)`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [concat_def; ALL; NULL; NULL_APPEND]);;

export_thm null_concat;;

(* ------------------------------------------------------------------------- *)
(* List map.                                                                 *)
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

let LENGTH_MAP = prove
 (`!(f : A -> B) l. LENGTH (MAP f l) = LENGTH l`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [MAP; LENGTH]);;

export_thm LENGTH_MAP;;

let MAP_APPEND = prove
 (`!(f : A -> B) l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [MAP; APPEND]);;

export_thm MAP_APPEND;;

let MAP_o = prove
 (`!(f : B -> C) (g : A -> B) l. MAP (f o g) l = MAP f (MAP g l)`,
  GEN_TAC THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [MAP; o_THM]);;

export_thm MAP_o;;

let MAP_o' = prove
  (`!(f : B -> C) (g : A -> B). MAP f o MAP g = MAP (f o g)`,
   REWRITE_TAC [FUN_EQ_THM; MAP_o; o_THM]);;

export_thm MAP_o';;

let NULL_MAP = prove
 (`!(f : A -> B) l. NULL (MAP f l) <=> NULL l`,
  REWRITE_TAC [GSYM NULL_LENGTH; LENGTH_MAP]);;

export_thm NULL_MAP;;

let MAP_EQ_NIL = prove
 (`!(f : A -> B) l. MAP f l = [] <=> l = []`,
  REWRITE_TAC [GSYM NULL_EQ_NIL; NULL_MAP]);;

export_thm MAP_EQ_NIL;;

let INJECTIVE_MAP = prove
 (`!(f : A -> B).
      (!l1 l2. MAP f l1 = MAP f l2 ==> l1 = l2) <=>
      (!x y. f x = f y ==> x = y)`,
  GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`[x : A]`; `[y : A]`]) THEN
   ASM_REWRITE_TAC [MAP; CONS_11];
   ALL_TAC] THEN
  STRIP_TAC THEN
  LIST_INDUCT_TAC THENL
  [GEN_TAC THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   REWRITE_TAC [MAP_EQ_NIL; MAP];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MAP_EQ_NIL; MAP; NOT_CONS_NIL];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [CONS_11; MAP] THEN
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm INJECTIVE_MAP;;

let SURJECTIVE_MAP = prove
 (`!(f : A -> B). (!ys. ?xs. MAP f xs = ys) <=> (!y. ?x. f x = y)`,
  GEN_TAC THEN
  EQ_TAC THENL
  [REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `[y : B]`) THEN
   DISCH_THEN (CHOOSE_THEN MP_TAC) THEN
   LIST_CASES_TAC `xs : A list` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [MAP; NOT_CONS_NIL];
    DISCH_THEN (CHOOSE_THEN (CHOOSE_THEN SUBST1_TAC)) THEN
    REWRITE_TAC [MAP; CONS_11] THEN
    STRIP_TAC THEN
    EXISTS_TAC `h : A` THEN
    FIRST_ASSUM ACCEPT_TAC];
   STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
   [EXISTS_TAC `[] : A list` THEN
    REWRITE_TAC [MAP];
    POP_ASSUM STRIP_ASSUME_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `h : B`) THEN
    STRIP_TAC THEN
    EXISTS_TAC `CONS (x : A) xs` THEN
    ASM_REWRITE_TAC [MAP; CONS_11]]]);;

export_thm SURJECTIVE_MAP;;

let MAP_ID = prove
 (`!l. MAP (\x. (x : A)) l = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [MAP]);;

export_thm MAP_ID;;

let MAP_I = prove
 (`MAP (I : A -> A) = I`,
  REWRITE_TAC [FUN_EQ_THM; I_DEF; MAP_ID]);;

export_thm MAP_I;;

let MAP_EQ = prove
 (`!(f : A -> B) (g : A -> B) l.
     ALL (\x. f x = g x) l ==> MAP f l = MAP g l`,
  GEN_TAC THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MAP];
   ALL_TAC] THEN
  REWRITE_TAC [MAP; ALL; CONS_11] THEN
  REPEAT STRIP_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm MAP_EQ;;

let SET_OF_LIST_MAP = prove
 (`!(f : A -> B) l.
     set_of_list (MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES];
   ASM_REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES]]);;

export_thm SET_OF_LIST_MAP;;

let ALL_MAP = prove
 (`!p (f : A -> B) l. ALL p (MAP f l) <=> ALL (p o f) l`,
  REWRITE_TAC [ALL_SET_OF_LIST; SET_OF_LIST_MAP; FORALL_IN_IMAGE; o_THM]);;

export_thm ALL_MAP;;

let EX_MAP = prove
 (`!p (f : A -> B) l. EX p (MAP f l) <=> EX (p o f) l`,
  REWRITE_TAC [GSYM NOT_ALL_NOT; ALL_MAP; o_DEF]);;

export_thm EX_MAP;;

let MEM_MAP = prove
 (`!(f : A -> B) l y. MEM y (MAP f l) <=> ?x. y = f x /\ MEM x l`,
  REWRITE_TAC [MEM_SET_OF_LIST; SET_OF_LIST_MAP; IN_IMAGE]);;

export_thm MEM_MAP;;

(* ------------------------------------------------------------------------- *)
(* Filter.                                                                   *)
(* ------------------------------------------------------------------------- *)

logfile "list-filter-def";;

let (FILTER_NIL,FILTER_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(!(p : A -> bool). FILTER p [] = []) /\
     (!(p : A -> bool) h t.
        FILTER p (CONS h t) =
        if p h then CONS h (FILTER p t) else FILTER p t)` in
  CONJ_PAIR def;;

export_thm FILTER_NIL;;
export_thm FILTER_CONS;;

let FILTER = CONJ FILTER_NIL FILTER_CONS;;

logfile "list-filter-thm";;

let FILTER_APPEND = prove
 (`!(p : A -> bool) l1 l2.
     FILTER p (APPEND l1 l2) =
     APPEND (FILTER p l1) (FILTER p l2)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [FILTER; APPEND];
   ALL_TAC] THEN
  GEN_TAC THEN
  ASM_REWRITE_TAC [FILTER; APPEND] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [APPEND];
   REWRITE_TAC []]);;

export_thm FILTER_APPEND;;

let FILTER_MAP = prove
 (`!p (f : A -> B) l. FILTER p (MAP f l) = MAP f (FILTER (p o f) l)`,
  GEN_TAC THEN
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [MAP; FILTER];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [MAP; FILTER; o_THM] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [MAP];
   REWRITE_TAC []]);;

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
 (`!p (l : A list).
     set_of_list (FILTER p l) = set_of_list l DIFF { x | ~p x }`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [FILTER; set_of_list; EMPTY_DIFF];
   ALL_TAC] THEN
  REWRITE_TAC [FILTER] THEN
  ONCE_REWRITE_TAC [COND_RAND] THEN
  ASM_REWRITE_TAC [set_of_list; INSERT_DIFF; IN_ELIM] THEN
  BOOL_CASES_TAC `(p : A -> bool) h` THEN
  REWRITE_TAC []);;

export_thm SET_OF_LIST_FILTER;;

let ALL_FILTER = prove
 (`!p q (l : A list). ALL p (FILTER q l) <=> ALL (\x. q x ==> p x) l`,
  REWRITE_TAC
    [ALL_SET_OF_LIST; SET_OF_LIST_FILTER; IN_DIFF; IN_ELIM; IMP_IMP]);;

export_thm ALL_FILTER;;

let EX_FILTER = prove
 (`!p q (l : A list). EX p (FILTER q l) <=> EX (\x. q x /\ p x) l`,
  REWRITE_TAC
    [EX_SET_OF_LIST; SET_OF_LIST_FILTER; IN_DIFF; IN_ELIM; CONJ_ASSOC]);;

export_thm EX_FILTER;;

let MEM_FILTER = prove
 (`!p l (x : A). MEM x (FILTER p l) <=> MEM x l /\ p x`,
  REWRITE_TAC [MEM_SET_OF_LIST; SET_OF_LIST_FILTER; IN_DIFF; IN_ELIM]);;

export_thm MEM_FILTER;;

(* ------------------------------------------------------------------------- *)
(* Reverse.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "list-reverse-def";;

let (REVERSE_NIL,REVERSE_CONS) =
  let def = new_recursive_definition list_RECURSION
    `(REVERSE ([] : A list) = []) /\
     (!(h : A) t. REVERSE (CONS h t) = APPEND (REVERSE t) [h])` in
  CONJ_PAIR def;;

export_thm REVERSE_NIL;;
export_thm REVERSE_CONS;;

let REVERSE = CONJ REVERSE_NIL REVERSE_CONS;;

logfile "list-reverse-thm";;

let REVERSE_APPEND = prove
 (`!(l1 : A list) l2.
     REVERSE (APPEND l1 l2) = APPEND (REVERSE l2) (REVERSE l1)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

export_thm REVERSE_APPEND;;

let REVERSE_REVERSE = prove
 (`!(l : A list). REVERSE (REVERSE l) = l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE; REVERSE_APPEND; APPEND]);;

export_thm REVERSE_REVERSE;;

let LENGTH_REVERSE = prove
 (`!(l : A list). LENGTH (REVERSE l) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [LENGTH; REVERSE; LENGTH_APPEND; ADD_CLAUSES]);;

export_thm LENGTH_REVERSE;;

let SET_OF_LIST_REVERSE = prove
 (`!(l : A list). set_of_list (REVERSE l) = set_of_list l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [set_of_list; REVERSE; SET_OF_LIST_APPEND] THEN
  ONCE_REWRITE_TAC [UNION_COMM] THEN
  MATCH_ACCEPT_TAC INSERT_UNION_SING);;

export_thm SET_OF_LIST_REVERSE;;

let MEM_REVERSE = prove
 (`!l (x : A). MEM x (REVERSE l) <=> MEM x l`,
  REWRITE_TAC [MEM_SET_OF_LIST; SET_OF_LIST_REVERSE]);;

export_thm MEM_REVERSE;;

let MAP_REVERSE = prove
 (`!(f : A -> B) l. REVERSE (MAP f l) = MAP f (REVERSE l)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [MAP; REVERSE; MAP_APPEND]);;

export_thm MAP_REVERSE;;

(* ------------------------------------------------------------------------- *)
(* fold.                                                                     *)
(* ------------------------------------------------------------------------- *)

logfile "list-fold-def";;

let (foldr_nil,foldr_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!(f : A -> B -> B) b. foldr f b [] = b) /\
     (!(f : A -> B -> B) b h t. foldr f b (CONS h t) = f h (foldr f b t))` in
  CONJ_PAIR def;;

export_thm foldr_nil;;
export_thm foldr_cons;;

let foldr_def = CONJ foldr_nil foldr_cons;;

let foldl_def = new_definition
  `!(f : B -> A -> B) b l.
      foldl f b l = foldr (C f) b (REVERSE l)`;;

export_thm foldl_def;;

logfile "list-fold-thm";;

let foldr_suc = prove
  (`!(l : A list) k. foldr (\x n. SUC n) k l = LENGTH l + k`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [foldr_nil; LENGTH; ADD_CLAUSES];
    ASM_REWRITE_TAC [foldr_cons; LENGTH; ADD_CLAUSES]]);;

export_thm foldr_suc;;

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
   REWRITE_TAC [foldl_def; REVERSE; foldr_append; foldr_def; C_THM]);;

export_thm foldl_cons;;

let foldl_suc = prove
  (`!l : A list. !k. foldl (\n x. SUC n) k l = LENGTH l + k`,
   REWRITE_TAC [foldl_def; C_DEF; foldr_suc; LENGTH_REVERSE]);;

export_thm foldl_suc;;

let foldl_with_cons = prove
  (`!(l1 : A list) l2. foldl (C CONS) l2 l1 = APPEND (REVERSE l1) l2`,
   REWRITE_TAC [foldl_def; CC_EQ_I; foldr_with_cons]);;

export_thm foldl_with_cons;;

let foldl_with_cons_nil = prove
  (`!(l : A list). foldl (C CONS) [] l = REVERSE l`,
   REWRITE_TAC [foldl_with_cons; APPEND_NIL]);;

export_thm foldl_with_cons_nil;;

let foldr_reverse = prove
  (`!(f : A -> B -> B) b l. foldr f b (REVERSE l) = foldl (C f) b l`,
   REWRITE_TAC [foldl_def; CC_EQ_I]);;

export_thm foldr_reverse;;

let foldl_reverse = prove
  (`!(f : B -> A -> B) b l. foldl f b (REVERSE l) = foldr (C f) b l`,
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
   ASM_REWRITE_TAC [C_THM]);;

export_thm foldl_append_assoc;;

(* ------------------------------------------------------------------------- *)
(* The last element of the list.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "list-last-def";;

let LAST = new_recursive_definition list_RECURSION
  `!(h:A) t. LAST (CONS h t) = if NULL t then h else LAST t`;;

export_thm LAST;;

logfile "list-last-thm";;

let LAST_SING = prove
 (`!(x : A). LAST [x] = x`,
  REWRITE_TAC [LAST; NULL]);;

export_thm LAST_SING;;

let LAST_MULTIPLE = prove
 (`!(x1 : A) x2 l. LAST (CONS x1 (CONS x2 l)) = LAST (CONS x2 l)`,
  REWRITE_TAC [LAST; NULL]);;

export_thm LAST_MULTIPLE;;

let LAST_CLAUSES = CONJ LAST_SING LAST_MULTIPLE;;

(* ------------------------------------------------------------------------- *)
(* Element indices.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "list-nth-def";;

let (nth_zero,nth_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(l : A list). nth l 0 = HD l) /\
     (!(l : A list) n. nth l (SUC n) = nth (TL l) n)` in
  let zero = prove
    (`!(h : A) t. nth (CONS h t) 0 = h`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!(h : A) t n. n < LENGTH t ==> nth (CONS h t) (SUC n) = nth t n`,
     REWRITE_TAC [def; TL]) in
  (zero,suc);;

export_thm nth_zero;;
export_thm nth_suc;;

let nth_def = CONJ nth_zero nth_suc;;

logfile "list-nth-thm";;

let nth_append = prove
 (`!(l1 : A list) l2 k.
     k < LENGTH l1 + LENGTH l2 ==>
     nth (APPEND l1 l2) k =
     if k < LENGTH l1 then nth l1 k
     else nth l2 (k - LENGTH l1)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
  SPEC_TAC (`k : num`, `k : num`) THEN
  INDUCT_TAC THENL
  [LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT_REFL; SUB_0; APPEND];
    REWRITE_TAC [APPEND; nth_zero; LENGTH; LT_0]];
   ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; LT; SUB_0; APPEND];
   ALL_TAC] THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [LENGTH; ADD; LT_SUC; APPEND] THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`h : A`; `APPEND (t : A list) l2`; `k : num`] nth_suc) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC [LENGTH_APPEND];
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t : A list`) THEN
  ANTS_TAC THENL
  [FIRST_ASSUM ACCEPT_TAC;
   ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THENL
  [ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC nth_suc THEN
   FIRST_ASSUM ACCEPT_TAC;
   ASM_REWRITE_TAC [] THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC EQ_SYM THEN
   MATCH_MP_TAC SUB_SUC THEN
   ASM_REWRITE_TAC [GSYM NOT_LT]]);;

export_thm nth_append;;

let last_nth = prove
 (`!(l : A list). ~NULL l ==> nth l (LENGTH l - 1) = LAST l`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NULL];
   ALL_TAC] THEN
  REWRITE_TAC [NULL; LAST; LENGTH] THEN
  POP_ASSUM MP_TAC THEN
  COND_CASES_TAC THENL
  [DISCH_THEN (K ALL_TAC) THEN
   POP_ASSUM (SUBST_VAR_TAC o REWRITE_RULE [NULL_EQ_NIL]) THEN
   REWRITE_TAC [LENGTH; SUC_SUB1; nth_zero];
   ALL_TAC] THEN
  REWRITE_TAC [SUC_SUB1] THEN
  DISCH_THEN (SUBST1_TAC o SYM) THEN
  MP_TAC (SPEC `LENGTH (t : A list)` num_CASES) THEN
  ASM_REWRITE_TAC [NULL_LENGTH] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [SUC_SUB1] THEN
  MATCH_MP_TAC nth_suc THEN
  ASM_REWRITE_TAC [SUC_LT]);;

export_thm last_nth;;

let square_equality_lemma = prove
  (`!(a:A) b c d. (c = a) /\ (d = b) ==> ((a = b) ==> (c = d))`,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

let nth_eq = prove
  (`!l1 (l2 : A list).
      LENGTH l1 = LENGTH l2 /\
      (!i. i < LENGTH l1 ==> nth l1 i = nth l2 i) ==>
      l1 = l2`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LENGTH_EQ_NIL] THEN
    REPEAT STRIP_TAC;
    ALL_TAC] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; NOT_SUC];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LENGTH; SUC_INJ; CONS_11] THEN
   REPEAT STRIP_TAC THENL
   [FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
    REWRITE_TAC [LT_0; nth_zero];
    ALL_TAC] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `SUC i`) THEN
   ASM_REWRITE_TAC [LT_SUC] THEN
   MATCH_MP_TAC square_equality_lemma THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC nth_suc THEN
    ASM_REWRITE_TAC [];
    MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC nth_suc THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm nth_eq;;

let nth_map = prove
  (`!(f : A -> B) l i. i < LENGTH l ==> nth (MAP f l) i = f (nth l i)`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT];
    ALL_TAC] THEN
   REWRITE_TAC [LENGTH; MAP] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [nth_zero];
    ALL_TAC] THEN
   POP_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [LT_SUC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `i : num`) THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC square_equality_lemma THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC nth_suc THEN
    ASM_REWRITE_TAC [LENGTH_MAP];
    AP_TERM_TAC THEN
    MATCH_MP_TAC nth_suc THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm nth_map;;

let set_of_list_nth = prove
 (`!(l : A list). set_of_list l = IMAGE (nth l) { i | i < LENGTH l }`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; LT; EMPTY_GSPEC; set_of_list; IMAGE_EMPTY];
   ALL_TAC] THEN
  ASM_REWRITE_TAC
    [LENGTH; set_of_list; IN_INSERT; INSERT_NUMSEG_LT'; IMAGE_INSERT;
     nth_zero] THEN
  POP_ASSUM (K ALL_TAC) THEN
  AP_TERM_TAC THEN
  REWRITE_TAC [EXTENSION] THEN
  GEN_TAC THEN
  EQ_TAC THENL
  [SPEC_TAC (`x : A`, `x : A`) THEN
   REWRITE_TAC [FORALL_IN_IMAGE; IN_ELIM] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [IN_IMAGE] THEN
   EXISTS_TAC `SUC x` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_SYM THEN
    MATCH_MP_TAC nth_suc THEN
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC [IN_ELIM_THM] THEN
    EXISTS_TAC `x : num` THEN
    ASM_REWRITE_TAC []];
   SPEC_TAC (`x : A`, `x : A`) THEN
   REWRITE_TAC [FORALL_IN_IMAGE; IN_ELIM_THM] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [IN_IMAGE] THEN
   EXISTS_TAC `i : num` THEN
   ASM_REWRITE_TAC [IN_ELIM] THEN
   MATCH_MP_TAC nth_suc THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm set_of_list_nth;;

let all_nth = prove
 (`!p (l : A list). ALL p l <=> !i. i < LENGTH l ==> p (nth l i)`,
  REWRITE_TAC [ALL_SET_OF_LIST; set_of_list_nth; FORALL_IN_IMAGE; IN_ELIM]);;

export_thm all_nth;;

let ex_nth = prove
 (`!p (l : A list). EX p l <=> ?i. i < LENGTH l /\ p (nth l i)`,
  REWRITE_TAC [EX_SET_OF_LIST; set_of_list_nth; EXISTS_IN_IMAGE; IN_ELIM]);;

export_thm ex_nth;;

let mem_nth = prove
 (`!l (x : A). MEM x l <=> ?i. i < LENGTH l /\ x = nth l i`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [CONJ_SYM] THEN
  REWRITE_TAC [MEM_SET_OF_LIST; set_of_list_nth; IN_IMAGE; IN_ELIM]);;

export_thm mem_nth;;

(* ------------------------------------------------------------------------- *)
(* Replicate.                                                                *)
(* ------------------------------------------------------------------------- *)

logfile "list-replicate-def";;

let (REPLICATE_0,REPLICATE_SUC) =
  let def = new_recursive_definition num_RECURSION
    `(!(x : A). REPLICATE x 0 = []) /\
     (!(x : A) n. REPLICATE x (SUC n) = CONS x (REPLICATE x n))` in
  CONJ_PAIR def;;

export_thm REPLICATE_0;;
export_thm REPLICATE_SUC;;

let REPLICATE = CONJ REPLICATE_0 REPLICATE_SUC;;

logfile "list-replicate-thm";;

let LENGTH_REPLICATE = prove
 (`!(x : A) n. LENGTH (REPLICATE x n) = n`,
  GEN_TAC THEN
  INDUCT_TAC THEN
  ASM_REWRITE_TAC [LENGTH; REPLICATE]);;

export_thm LENGTH_REPLICATE;;

let NULL_REPLICATE = prove
 (`!(x : A) n. NULL (REPLICATE x n) <=> n = 0`,
  REWRITE_TAC [GSYM NULL_LENGTH; LENGTH_REPLICATE]);;

export_thm NULL_REPLICATE;;

let APPEND_EQ_REPLICATE = prove
 (`!(x : A) n l1 l2.
     APPEND l1 l2 = REPLICATE x n <=>
     REPLICATE x (LENGTH l1) = l1 /\
     REPLICATE x (LENGTH l2) = l2 /\
     LENGTH l1 + LENGTH l2 = n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REPEAT GEN_TAC THEN
   REWRITE_TAC [REPLICATE_0; ADD_EQ_0; LENGTH_EQ_NIL; APPEND_EQ_NIL] THEN
   EQ_TAC THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [LENGTH_NIL; REPLICATE_0];
   LIST_INDUCT_TAC THENL
   [POP_ASSUM_LIST (K ALL_TAC) THEN
    GEN_TAC THEN
    REWRITE_TAC [NIL_APPEND; LENGTH_NIL; REPLICATE_0; ZERO_ADD] THEN
    EQ_TAC THENL
    [STRIP_TAC THEN
     SUBGOAL_THEN `LENGTH (l2 : A list) = SUC n` SUBST1_TAC THENL
     [ASM_REWRITE_TAC [LENGTH_REPLICATE];
      ASM_REWRITE_TAC []];
     DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
     FIRST_ASSUM (ACCEPT_TAC o SYM)];
    POP_ASSUM (K ALL_TAC) THEN
    GEN_TAC THEN
    ASM_REWRITE_TAC
      [CONS_APPEND; REPLICATE_SUC; CONS_11; LENGTH_CONS; SUC_ADD; SUC_INJ;
       GSYM CONJ_ASSOC] THEN
    AP_THM_TAC THEN
    AP_TERM_TAC THEN
    MATCH_ACCEPT_TAC EQ_SYM_EQ]]);;

export_thm APPEND_EQ_REPLICATE;;

let REPLICATE_ADD = prove
 (`!(x : A) m n.
     REPLICATE x (m + n) = APPEND (REPLICATE x m) (REPLICATE x n)`,
  REPEAT GEN_TAC THEN
  MATCH_MP_TAC EQ_SYM THEN
  REWRITE_TAC [APPEND_EQ_REPLICATE; LENGTH_REPLICATE]);;

export_thm REPLICATE_ADD;;

let MAP_REPLICATE = prove
 (`!(f : A -> B) x n. MAP f (REPLICATE x n) = REPLICATE (f x) n`,
  GEN_TAC THEN
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE_0; MAP_NIL];
   ASM_REWRITE_TAC [REPLICATE_SUC; MAP_CONS]]);;

export_thm MAP_REPLICATE;;

let nth_replicate = prove
  (`!(x : A) n i. i < n ==> nth (REPLICATE x n) i = x`,
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   NUM_CASES_TAC `i : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [REPLICATE; nth_zero];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `m : num` SUBST1_TAC) THEN
   REWRITE_TAC [LT_SUC] THEN
   STRIP_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `m : num`) THEN
   ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
   DISCH_THEN (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [REPLICATE] THEN
   MATCH_MP_TAC nth_suc THEN
   ASM_REWRITE_TAC [LENGTH_REPLICATE]);;

export_thm nth_replicate;;

let SET_OF_LIST_REPLICATE = prove
 (`!(x : A) n. set_of_list (REPLICATE x n) = if n = 0 then {} else {x}`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [REPLICATE; set_of_list];
   ASM_REWRITE_TAC [REPLICATE; set_of_list; NOT_SUC] THEN
   COND_CASES_TAC THENL
   [REFL_TAC;
    REWRITE_TAC [INSERT_INSERT]]]);;

export_thm SET_OF_LIST_REPLICATE;;

let MEM_REPLICATE = prove
 (`!(x : A) n y. MEM y (REPLICATE x n) <=> y = x /\ ~(n = 0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MEM_SET_OF_LIST; SET_OF_LIST_REPLICATE] THEN
  COND_CASES_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY];
   REWRITE_TAC [IN_SING]]);;

export_thm MEM_REPLICATE;;

(* ------------------------------------------------------------------------- *)
(* Take and drop.                                                            *)
(* ------------------------------------------------------------------------- *)

logfile "list-take-drop-def";;

let (take_zero,take_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(l : A list). take 0 l = []) /\
     (!n (l : A list). take (SUC n) l = CONS (HD l) (take n (TL l)))` in
  let zero = prove
    (`!(l : A list). take 0 l = []`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!n (h : A) t.
        n <= LENGTH t ==>
        take (SUC n) (CONS h t) = CONS h (take n t)`,
     REWRITE_TAC [def; HD; TL]) in
  (zero,suc);;

export_thm take_zero;;
export_thm take_suc;;

let take_def = CONJ take_zero take_suc;;

let (drop_zero,drop_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(l : A list). drop 0 l = l) /\
     (!n (l : A list). drop (SUC n) l = drop n (TL l))` in
  let zero = prove
    (`!(l : A list). drop 0 l = l`,
     REWRITE_TAC [def; HD])
  and suc = prove
    (`!n (h : A) t.
        n <= LENGTH t ==>
        drop (SUC n) (CONS h t) = drop n t`,
     REWRITE_TAC [def; TL]) in
  (zero,suc);;

export_thm drop_zero;;
export_thm drop_suc;;

let drop_def = CONJ drop_zero drop_suc;;

logfile "list-take-drop-thm";;

let take_one = prove
  (`!(h : A) t. take 1 (CONS h t) = [h]`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`0`; `h : A`; `t : A list`] take_suc) THEN
   REWRITE_TAC [LE_0; ONE; take_zero]);;

export_thm take_one;;

let take_drop = prove
  (`!n (l : A list). n <= LENGTH l ==> APPEND (take n l) (drop n l) = l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [take_zero; drop_zero; APPEND];
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
  (`!n (l : A list). n <= LENGTH l ==> LENGTH (take n l) = n`,
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

let length_drop_add = prove
  (`!n (l : A list). n <= LENGTH l ==> n + LENGTH (drop n l) = LENGTH l`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`] take_drop) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (CONV_TAC o RAND_CONV o RAND_CONV o REWR_CONV o SYM) THEN
   REWRITE_TAC [LENGTH_APPEND] THEN
   MP_TAC (SPECL [`n : num`; `l : A list`] length_take) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC);;

export_thm length_drop_add;;

let length_drop = prove
  (`!n (l : A list). n <= LENGTH l ==> LENGTH (drop n l) = LENGTH l - n`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`] length_drop_add) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   REWRITE_TAC [ADD_SUB2]);;

export_thm length_drop;;

let nth_take_drop = prove
  (`!n (l : A list) i.
      n <= LENGTH l /\ i < LENGTH l ==>
      nth l i = if i < n then nth (take n l) i else nth (drop n l) (i - n)`,
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`] take_drop) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN
     (fun th ->
       (CONV_TAC o LAND_CONV o RAND_CONV o
        RAND_CONV o REWR_CONV o SYM) th THEN
       (CONV_TAC o RAND_CONV o LAND_CONV o
        LAND_CONV o REWR_CONV o SYM) th) THEN
   REWRITE_TAC [LENGTH_APPEND] THEN
   STRIP_TAC THEN
   MP_TAC
     (SPECL [`take n l : A list`; `drop n l : A list`; `i : num`]
        nth_append) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`] length_take) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REFL_TAC);;

export_thm nth_take_drop;;

let nth_take = prove
  (`!n (l : A list) i. n <= LENGTH l /\ i < n ==> nth (take n l) i = nth l i`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`; `i : num`] nth_take_drop) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LTE_TRANS THEN
    EXISTS_TAC `n : num` THEN
    ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    MATCH_ACCEPT_TAC EQ_SYM]);;

export_thm nth_take;;

let nth_drop = prove
  (`!n (l : A list) i. n + i < LENGTH l ==> nth (drop n l) i = nth l (n + i)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n : num`; `l : A list`; `n + i : num`] nth_take_drop) THEN
   ANTS_TAC THENL
   [ASM_REWRITE_TAC [] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `SUC (n + i)` THEN
    ASM_REWRITE_TAC [LE_SUC_LT] THEN
    REWRITE_TAC [ADD1; GSYM ADD_ASSOC; LE_ADD];
    ALL_TAC] THEN
   SUBGOAL_THEN `n + i < (n : num) <=> F` SUBST1_TAC THENL
   [REWRITE_TAC [NOT_LT; LE_ADD];
    REWRITE_TAC [ADD_SUB2] THEN
    MATCH_ACCEPT_TAC EQ_SYM]);;

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

let drop_add = prove
  (`!m n (l : A list).
       m + n <= LENGTH l ==>
       drop (m + n) l = drop m (drop n l)`,
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [ADD_0; drop_zero];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [ADD_SUC; LENGTH_NIL; LE_ZERO; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [ADD_SUC; LENGTH_CONS; LE_SUC] THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`m + n : num`; `h : A`; `t : A list`] drop_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC (SPECL [`n : num`; `h : A`; `t : A list`] drop_suc) THEN
     ANTS_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `m + n : num` THEN
      ASM_REWRITE_TAC [LE_ADDR];
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []]]]);;

export_thm drop_add;;

let take_add = prove
  (`!m n (l : A list).
       m + n <= LENGTH l ==>
       take (m + n) l = APPEND (take m l) (take n (drop m l))`,
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC APPEND_RCANCEL_IMP THEN
   EXISTS_TAC `drop (m + n) (l : A list)` THEN
   MP_TAC (SPECL [`m + n : num`; `l : A list`] take_drop) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   ONCE_REWRITE_TAC [ADD_SYM] THEN
   MP_TAC (SPECL [`n : num`; `m : num`; `l : A list`] drop_add) THEN
   ANTS_TAC THENL
   [ONCE_REWRITE_TAC [ADD_SYM] THEN
    FIRST_X_ASSUM ACCEPT_TAC;
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [GSYM APPEND_ASSOC] THEN
    MP_TAC (SPECL [`n : num`; `drop m l : A list`] take_drop) THEN
    ANTS_TAC THENL
    [SUBGOAL_THEN `m + n <= m + LENGTH (drop m l : A list)` MP_TAC THENL
     [SUBGOAL_THEN `m + LENGTH (drop m l : A list) = LENGTH (l : A list)`
        SUBST1_TAC THENL
      [MATCH_MP_TAC length_drop_add THEN
       MATCH_MP_TAC LE_TRANS THEN
       EXISTS_TAC `m + n : num` THEN
       ASM_REWRITE_TAC [LE_ADD];
       FIRST_X_ASSUM ACCEPT_TAC];
      REWRITE_TAC [LE_ADD_LCANCEL]];
     DISCH_THEN SUBST1_TAC THEN
     MATCH_MP_TAC EQ_SYM THEN
     MATCH_MP_TAC take_drop THEN
     MATCH_MP_TAC LE_TRANS THEN
     EXISTS_TAC `m + n : num` THEN
     ASM_REWRITE_TAC [LE_ADD]]]);;

export_thm take_add;;

let take_replicate = prove
  (`!m n (x : A).
       m <= n ==>
       take m (REPLICATE x n) = REPLICATE x m`,
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [`m : num`; `REPLICATE (x : A) n`] take_drop) THEN
   ASM_REWRITE_TAC [LENGTH_REPLICATE; APPEND_EQ_REPLICATE] THEN
   STRIP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   AP_TERM_TAC THEN
   MATCH_MP_TAC length_take THEN
   ASM_REWRITE_TAC [LENGTH_REPLICATE]);;

export_thm take_replicate;;

let drop_replicate = prove
  (`!m n (x : A).
       m <= n ==>
       drop m (REPLICATE x n) = REPLICATE x (n - m)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPECL [`m : num`; `REPLICATE (x : A) n`] take_drop) THEN
   ASM_REWRITE_TAC [LENGTH_REPLICATE; APPEND_EQ_REPLICATE] THEN
   STRIP_TAC THEN
   POP_ASSUM (K ALL_TAC) THEN
   POP_ASSUM (SUBST1_TAC o SYM) THEN
   POP_ASSUM (K ALL_TAC) THEN
   AP_TERM_TAC THEN
   MP_TAC (ISPECL [`m : num`; `REPLICATE (x : A) n`] length_drop) THEN
   ASM_REWRITE_TAC [LENGTH_REPLICATE]);;

export_thm drop_replicate;;

let drop_append = prove
  (`!l1 l2 : A list. drop (LENGTH l1) (APPEND l1 l2) = l2`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`l1 : A list`, `l1 : A list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH_NIL; drop_zero; NIL_APPEND];
    REWRITE_TAC [LENGTH_CONS; CONS_APPEND] THEN
    POP_ASSUM (CONV_TAC o RAND_CONV o REWR_CONV o SYM) THEN
    MATCH_MP_TAC drop_suc THEN
    REWRITE_TAC [LENGTH_APPEND; LE_ADD]]);;

export_thm drop_append;;

let take_append = prove
  (`!l1 l2 : A list. take (LENGTH l1) (APPEND l1 l2) = l1`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`LENGTH (l1 : A list)`;
                  `APPEND l1 l2 : A list`] take_drop) THEN
   REWRITE_TAC [drop_append; APPEND_RCANCEL; LENGTH_APPEND; LE_ADD]);;

export_thm take_append;;

(* ------------------------------------------------------------------------- *)
(* Interval.                                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "list-interval-def";;

let (interval_zero,interval_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!m. interval m 0 = []) /\
     (!m n. interval m (SUC n) = CONS m (interval (SUC m) n))` in
  CONJ_PAIR def;;

export_thm interval_zero;;
export_thm interval_suc;;

let interval_def = CONJ interval_zero interval_suc;;

logfile "list-interval-thm";;

let length_interval = prove
  (`!m n. LENGTH (interval m n) = n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   SIMP_TAC [LENGTH; interval_def; SUC_INJ]);;

export_thm length_interval;;

let map_suc_interval = prove
  (`!m n. MAP SUC (interval m n) = interval (SUC m) n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [interval_zero; MAP];
    GEN_TAC THEN
    ASM_REWRITE_TAC [interval_suc; MAP]]);;

export_thm map_suc_interval;;

let nth_interval = prove
  (`!m n i. i < n ==> nth (interval m n) i = m + i`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    ALL_TAC] THEN
   REWRITE_TAC [interval_def] THEN
   REPEAT GEN_TAC THEN
   NUM_CASES_TAC `i : num` THENL
   [DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [nth_zero; ADD_CLAUSES];
    ALL_TAC] THEN
   DISCH_THEN (X_CHOOSE_THEN `j : num` SUBST1_TAC) THEN
   REWRITE_TAC [LT_SUC; ADD_CLAUSES] THEN
   STRIP_TAC THEN
   REWRITE_TAC [GSYM SUC_ADD] THEN
   FIRST_X_ASSUM (MP_TAC o SPECL [`SUC m`; `j : num`]) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (SUBST1_TAC o SYM) THEN
   MATCH_MP_TAC nth_suc THEN
   ASM_REWRITE_TAC [length_interval]);;

export_thm nth_interval;;

(* ------------------------------------------------------------------------- *)
(* Zip.                                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "list-zip-def";;

let (zipwith_nil,zipwith_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!(f : A -> B -> C) l. zipwith f [] l = []) /\
     (!f h t l.
        zipwith f (CONS h t) l =
        CONS (f h (HD l)) (zipwith f t (TL l)))` in
  let znil = prove
    (`!(f : A -> B -> C). zipwith f [] [] = []`,
     REWRITE_TAC [def])
  and zcons = prove
    (`!(f : A -> B -> C) h1 h2 t1 t2.
        LENGTH t1 = LENGTH t2 ==>
        zipwith f (CONS h1 t1) (CONS h2 t2) =
        CONS (f h1 h2) (zipwith f t1 t2)`,
     REWRITE_TAC [def; HD; TL]) in
  (znil,zcons);;

export_thm zipwith_nil;;
export_thm zipwith_cons;;

let zipwith_def = CONJ zipwith_nil zipwith_cons;;

let zip_def = new_definition
  `!(l1 : A list) (l2 : B list). zip l1 l2 = zipwith (,) l1 l2`;;

export_thm zip_def;;

let unzip_def = new_definition
  `unzip = foldr (\ (x : A, y : B) (xs,ys). (CONS x xs, CONS y ys)) ([],[])`;;

export_thm unzip_def;;

logfile "list-zip-thm";;

let zip_nil = prove
 (`zip [] [] = ([] : (A # B) list)`,
  REWRITE_TAC [zip_def; zipwith_nil]);;

export_thm zip_nil;;

let zip_cons = prove
 (`!(x : A) (y : B) xs ys.
     LENGTH xs = LENGTH ys ==>
     zip (CONS x xs) (CONS y ys) = CONS (x,y) (zip xs ys)`,
  REWRITE_TAC [zip_def] THEN
  MATCH_ACCEPT_TAC zipwith_cons);;

export_thm zip_cons;;

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

let length_zip = prove
  (`!(l1 : A list) (l2 : B list) n.
      LENGTH l1 = n /\ LENGTH l2 = n ==> LENGTH (zip l1 l2) = n`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [zip_def] THEN
   MATCH_ACCEPT_TAC length_zipwith);;

export_thm length_zip;;

let nth_zipwith = prove
  (`!(f : A -> B -> C) l1 l2 n i.
      LENGTH l1 = n /\ LENGTH l2 = n /\ i < n ==>
      nth (zipwith f l1 l2) i = f (nth l1 i) (nth l2 i)`,
   GEN_TAC THEN
   (LIST_INDUCT_TAC THEN
    LIST_INDUCT_TAC THEN
    INDUCT_TAC THEN
    INDUCT_TAC THEN
    REWRITE_TAC [NOT_SUC; LENGTH; LT_ZERO; LT_0; SUC_INJ; LT_SUC]) THENL
   [POP_ASSUM_LIST (K ALL_TAC) THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (SPECL [`f : A -> B -> C`; `h : A`; `h' : B`;
                   `t : A list`; `t' : B list`] zipwith_cons) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [nth_zero];
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`f : A -> B -> C`; `h : A`; `h' : B`;
                   `t : A list`; `t' : B list`] zipwith_cons) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (ISPECL [`h : A`; `t : A list`; `i : num`] nth_suc) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (ISPECL [`h' : B`; `t' : B list`; `i : num`] nth_suc) THEN
    ANTS_TAC THENL
    [ASM_REWRITE_TAC [];
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC (ISPECL [`(f : A -> B -> C) h h'`; `zipwith (f : A -> B -> C) t t'`;
                    `i : num`] nth_suc) THEN
    ANTS_TAC THENL
    [MP_TAC (ISPECL [`f : A -> B -> C`; `t : A list`; `t' : B list`;
                     `n : num`] length_zipwith) THEN
     ANTS_TAC THENL
     [ASM_REWRITE_TAC [];
      ALL_TAC] THEN
     DISCH_THEN SUBST1_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `n : num` THEN
    ASM_REWRITE_TAC []]);;

export_thm nth_zipwith;;

let nth_zip = prove
  (`!(l1 : A list) (l2 : B list) n i.
      LENGTH l1 = n /\ LENGTH l2 = n /\ i < n ==>
      nth (zip l1 l2) i = (nth l1 i, nth l2 i)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [zip_def] THEN
   MATCH_ACCEPT_TAC nth_zipwith);;

export_thm nth_zip;;

let zipwith_sing = prove
 (`!(f : A -> B -> C) x y. zipwith f [x] [y] = [f x y]`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`f : A -> B -> C`;
                 `x : A`;
                 `y : B`;
                 `[] : A list`;
                 `[] : B list`] zipwith_cons) THEN
  REWRITE_TAC [LENGTH_NIL] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [zipwith_nil]);;

export_thm zipwith_sing;;

let zip_sing = prove
 (`!(x : A) (y : B). zip [x] [y] = [(x,y)]`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [zip_def] THEN
  MATCH_ACCEPT_TAC zipwith_sing);;

export_thm zip_sing;;

let zipwith_append = prove
 (`!(f : A -> B -> C) x1 x2 y1 y2.
     LENGTH x1 = LENGTH y1 /\
     LENGTH x2 = LENGTH y2 ==>
     zipwith f (APPEND x1 x2) (APPEND y1 y2) =
     APPEND (zipwith f x1 y1) (zipwith f x2 y2)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`x1 : A list`, `x1 : A list`) THEN
  SPEC_TAC (`y1 : B list`, `y1 : B list`) THEN
  MATCH_MP_TAC list_INDUCT THEN
  CONJ_TAC THENL
  [REWRITE_TAC [LENGTH_NIL; LENGTH_EQ_NIL] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [zipwith_nil; NIL_APPEND];
   ALL_TAC] THEN
  X_GEN_TAC `h2 : B` THEN
  X_GEN_TAC `t2 : B list` THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  REWRITE_TAC [LENGTH_CONS; LENGTH_EQ_CONS] THEN
  DISCH_THEN
    (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `h1 : A`
          (X_CHOOSE_THEN `t1 : A list` STRIP_ASSUME_TAC))
       STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (SPECL [`f : A -> B -> C`;
                 `h1 : A`;
                 `h2 : B`;
                 `t1 : A list`;
                 `t2 : B list`] zipwith_cons) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [CONS_APPEND] THEN
  MP_TAC (SPECL [`f : A -> B -> C`;
                 `h1 : A`;
                 `h2 : B`;
                 `APPEND t1 x2 : A list`;
                 `APPEND t2 y2 : B list`] zipwith_cons) THEN
  ASM_REWRITE_TAC [LENGTH_APPEND] THEN
  DISCH_THEN SUBST1_TAC THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm zipwith_append;;

let zip_append = prove
 (`!(x1 : A list) x2 (y1 : B list) y2.
     LENGTH x1 = LENGTH y1 /\
     LENGTH x2 = LENGTH y2 ==>
     zip (APPEND x1 x2) (APPEND y1 y2) =
     APPEND (zip x1 y1) (zip x2 y2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [zip_def] THEN
  MATCH_ACCEPT_TAC zipwith_append);;

export_thm zip_append;;

let unzip_nil = prove
 (`unzip [] = ([] : A list, [] : B list)`,
  REWRITE_TAC [unzip_def; foldr_def]);;

export_thm unzip_nil;;

let unzip_cons = prove
 (`!h (x : A) (y : B) t xs ys.
     unzip (CONS h t) = (CONS x xs, CONS y ys) <=>
     h = (x,y) /\ unzip t = (xs,ys)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `h : A # B` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `a : A`
       (X_CHOOSE_THEN `b : B` SUBST_VAR_TAC)) THEN
  X_CHOOSE_THEN `xt : A list`
    (X_CHOOSE_THEN `yt : B list` MP_TAC)
  (ISPEC `unzip (t : (A # B) list)` PAIR_SURJECTIVE) THEN
  REWRITE_TAC [unzip_def; foldr_def] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [CONS_11; PAIR_EQ] THEN
  BOOL_CASES_TAC `(b : B) = y` THEN
  REWRITE_TAC [CONJ_ASSOC]);;

export_thm unzip_cons;;

let unzip_eq_nil1 = prove
 (`!(l : (A # B) list) ys. unzip l = ([],ys) <=> l = [] /\ ys = []`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `l : (A # B) list` list_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `h : A # B`
          (X_CHOOSE_THEN `t : (A # B) list` SUBST_VAR_TAC))) THENL
  [REWRITE_TAC [unzip_nil; PAIR_EQ] THEN
   MATCH_ACCEPT_TAC EQ_SYM_EQ;
   MP_TAC (ISPEC `h : A # B` PAIR_SURJECTIVE) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `a : A`
        (X_CHOOSE_THEN `b : B` SUBST_VAR_TAC)) THEN
   MP_TAC (ISPEC `unzip t : A list # B list ` PAIR_SURJECTIVE) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `xt : A list`
        (X_CHOOSE_THEN `yt : B list` MP_TAC)) THEN
   REWRITE_TAC [unzip_def; foldr_def] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [NOT_CONS_NIL; PAIR_EQ]]);;

export_thm unzip_eq_nil1;;

let unzip_eq_nil2 = prove
 (`!(l : (A # B) list) xs. unzip l = (xs,[]) <=> l = [] /\ xs = []`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `l : (A # B) list` list_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (X_CHOOSE_THEN `h : A # B`
          (X_CHOOSE_THEN `t : (A # B) list` SUBST_VAR_TAC))) THENL
  [REWRITE_TAC [unzip_nil; PAIR_EQ] THEN
   MATCH_ACCEPT_TAC EQ_SYM_EQ;
   MP_TAC (ISPEC `h : A # B` PAIR_SURJECTIVE) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `a : A`
        (X_CHOOSE_THEN `b : B` SUBST_VAR_TAC)) THEN
   MP_TAC (ISPEC `unzip t : A list # B list ` PAIR_SURJECTIVE) THEN
   DISCH_THEN
     (X_CHOOSE_THEN `xt : A list`
        (X_CHOOSE_THEN `yt : B list` MP_TAC)) THEN
   REWRITE_TAC [unzip_def; foldr_def] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [NOT_CONS_NIL; PAIR_EQ]]);;

export_thm unzip_eq_nil2;;

let zip_unzip = prove
 (`!l (xs : A list) (ys : B list).
     unzip l = (xs,ys) <=> LENGTH xs = LENGTH ys /\ l = zip xs ys`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [unzip_nil; PAIR_EQ] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `xs : A list` list_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `x : A`
           (X_CHOOSE_THEN `xt : A list` SUBST_VAR_TAC))) THENL
   [MP_TAC (ISPEC `ys : B list` list_cases) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `y : B`
            (X_CHOOSE_THEN `yt : B list` SUBST_VAR_TAC))) THENL
    [REWRITE_TAC [zip_nil; LENGTH];
     REWRITE_TAC [NOT_CONS_NIL; LENGTH; NOT_SUC]];
    REWRITE_TAC [NOT_CONS_NIL] THEN
    MP_TAC (ISPEC `ys : B list` list_cases) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `y : B`
            (X_CHOOSE_THEN `yt : B list` SUBST_VAR_TAC))) THENL
    [REWRITE_TAC [LENGTH; NOT_SUC];
     REWRITE_TAC [LENGTH; SUC_INJ] THEN
     STRIP_TAC THEN
     MP_TAC
       (SPECL [`x : A`; `y : B`; `xt : A list`; `yt : B list`] zip_cons) THEN
     ASM_REWRITE_TAC [] THEN
     POP_ASSUM (SUBST1_TAC o SYM) THEN
     REWRITE_TAC [NOT_CONS_NIL]]];
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `xs : A list` list_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `x : A`
           (X_CHOOSE_THEN `xt : A list` SUBST_VAR_TAC))) THENL
   [REWRITE_TAC [unzip_eq_nil1; NOT_CONS_NIL] THEN
    MP_TAC (ISPEC `ys : B list` list_cases) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `y : B`
            (X_CHOOSE_THEN `yt : B list` SUBST_VAR_TAC))) THENL
    [REWRITE_TAC [zip_nil; NOT_CONS_NIL];
     REWRITE_TAC [LENGTH; NOT_SUC]];
    MP_TAC (ISPEC `ys : B list` list_cases) THEN
    DISCH_THEN
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `y : B`
            (X_CHOOSE_THEN `yt : B list` SUBST_VAR_TAC))) THENL
    [REWRITE_TAC [unzip_eq_nil2; NOT_CONS_NIL; LENGTH; NOT_SUC];
     ASM_REWRITE_TAC [LENGTH; SUC_INJ; unzip_cons] THEN
     ASM_CASES_TAC `LENGTH (xt : A list) = LENGTH (yt : B list)` THENL
     [MP_TAC
        (SPECL [`x : A`; `y : B`; `xt : A list`; `yt : B list`] zip_cons) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [CONS_11];
      ASM_REWRITE_TAC []]]]]);;

export_thm zip_unzip;;

(* ------------------------------------------------------------------------- *)
(* Nub.                                                                      *)
(* ------------------------------------------------------------------------- *)

logfile "list-nub-def";;

let (setify_nil,setify_cons) =
  let def = new_recursive_definition list_RECURSION
    `(setify ([] : A list) = []) /\
     (!(h : A) t.
        setify (CONS h t) =
        if MEM h t then setify t else CONS h (setify t))` in
  CONJ_PAIR def;;

export_thm setify_nil;;
export_thm setify_cons;;

let setify_def = CONJ setify_nil setify_cons;;

let nub_def = new_definition
  `!(l : A list). nub l = REVERSE (setify (REVERSE l))`;;

export_thm nub_def;;

logfile "list-nub-thm";;

let length_setify = prove
  (`!(l : A list). LENGTH (setify l) <= LENGTH l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [LENGTH; setify_def; LE_REFL] THEN
   BOOL_CASES_TAC `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [LE];
    ASM_REWRITE_TAC [LE_SUC; LENGTH]]);;

export_thm length_setify;;

let mem_setify = prove
  (`!l (x : A). MEM x (setify l) <=> MEM x l`,
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
   REWRITE_TAC [EXTENSION; GSYM MEM_SET_OF_LIST; mem_setify]);;

export_thm set_of_list_setify;;

let setify_idempotent = prove
  (`!(l : A list). setify (setify l) = setify l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [MEM; setify_def] THEN
   ASM_CASES_TAC `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [setify_def; mem_setify]]);;

export_thm setify_idempotent;;

let length_nub = prove
  (`!(l : A list). LENGTH (nub l) <= LENGTH l`,
   GEN_TAC THEN
   REWRITE_TAC [nub_def; LENGTH_REVERSE] THEN
   CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM LENGTH_REVERSE])) THEN
   MATCH_ACCEPT_TAC length_setify);;

export_thm length_nub;;

let mem_nub = prove
  (`!l (x : A). MEM x (nub l) <=> MEM x l`,
   REWRITE_TAC [nub_def; MEM_REVERSE; mem_setify]);;

export_thm mem_nub;;

let set_of_list_nub = prove
  (`!(l : A list). set_of_list (nub l) = set_of_list l`,
   REWRITE_TAC [EXTENSION; GSYM MEM_SET_OF_LIST; mem_nub]);;

export_thm set_of_list_nub;;

let nub_idempotent = prove
  (`!(l : A list). nub (nub l) = nub l`,
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

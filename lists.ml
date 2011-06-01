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
(* Basic definitions.                                                        *)
(* ------------------------------------------------------------------------- *)

logfile "list-dest-def";;

let HD = new_recursive_definition list_RECURSION
  `HD(CONS (h:A) t) = h`;;

export_thm HD;;

let TL = new_recursive_definition list_RECURSION
  `TL(CONS (h:A) t) = t`;;

export_thm TL;;

logfile "list-append-def";;

let APPEND = new_recursive_definition list_RECURSION
  `(!l:(A)list. APPEND [] l = l) /\
   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))`;;

export_thm APPEND;;

logfile "list-reverse-def";;

let REVERSE = new_recursive_definition list_RECURSION
  `(REVERSE [] = []) /\
   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])`;;

export_thm REVERSE;;

logfile "list-length-def";;

let LENGTH = new_recursive_definition list_RECURSION
  `(LENGTH [] = 0) /\
   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))`;;

export_thm LENGTH;;

logfile "list-map-def";;

let MAP = new_recursive_definition list_RECURSION
  `(!f:A->B. MAP f NIL = NIL) /\
   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))`;;

export_thm MAP;;

logfile "list-last-def";;

let LAST = new_recursive_definition list_RECURSION
  `!h t. LAST (CONS (h:A) t) = if t = [] then h else LAST t`;;

export_thm LAST;;

(***
let BUTLAST = new_recursive_definition list_RECURSION
 `(BUTLAST ([] : A list) = []) /\
  (!h t. BUTLAST (CONS (h:A) t) = if t = [] then [] else CONS h (BUTLAST t))`;;
***)

logfile "list-replicate-def";;

let REPLICATE = new_recursive_definition num_RECURSION
  `(!x. REPLICATE 0 (x:A) = []) /\
   (!x n. REPLICATE (SUC n) (x:A) = CONS x (REPLICATE n x))`;;

export_thm REPLICATE;;

logfile "list-dest-def";;

let NULL = new_recursive_definition list_RECURSION
  `(NULL ([] : A list) = T) /\
   (!h t. NULL (CONS (h:A) t) = F)`;;

export_thm NULL;;

logfile "list-quant-def";;

let ALL = new_recursive_definition list_RECURSION
  `(!P. ALL P ([] : A list) = T) /\
   (!P h t. ALL P (CONS (h:A) t) <=> P h /\ ALL P t)`;;

export_thm ALL;;

let EX = new_recursive_definition list_RECURSION
  `(!P. EX P ([] : A list) = F) /\
   (!P h t. EX P (CONS (h:A) t) <=> P h \/ EX P t)`;;

export_thm EX;;

(***
let ITLIST = new_recursive_definition list_RECURSION
  `(!(f:A->B->B) b. ITLIST f [] b = b) /\
   (!(f:A->B->B) b h t. ITLIST f (CONS h t) b = f h (ITLIST f t b))`;;
***)

logfile "list-member-def";;

let MEM = new_recursive_definition list_RECURSION
  `(!x. MEM (x:A) [] <=> F) /\
   (!x h t. MEM (x:A) (CONS h t) <=> (x = h) \/ MEM x t)`;;

export_thm MEM;;

(***
let ALL2_DEF = new_recursive_definition list_RECURSION
  `(!P l2. ALL2 (P:A->B->bool) ([]:A list) (l2:B list) <=> (l2 = [])) /\
   (!P l2 h1 t1. ALL2 (P:A->B->bool) (CONS (h1:A) t1) (l2:B list) <=>
        if l2 = [] then F
        else P h1 (HD l2) /\ ALL2 P t1 (TL l2))`;;

let ALL2 = prove
 (`(!P. ALL2 (P:A->B->bool) [] [] <=> T) /\
   (!P. ALL2 (P:A->B->bool) (CONS h1 t1) [] <=> F) /\
   (!P. ALL2 (P:A->B->bool) [] (CONS h2 t2) <=> F) /\
   (!P. ALL2 (P:A->B->bool) (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\ ALL2 P t1 t2)`,
  REWRITE_TAC[distinctness "list"; ALL2_DEF; HD; TL]);;

let MAP2_DEF = new_recursive_definition list_RECURSION
  `(!f l. MAP2 (f:A->B->C) [] l = []) /\
   (!f l h1 t1. MAP2 (f:A->B->C) (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))`;;

let MAP2 = prove
 (`(!f. MAP2 (f:A->B->C) [] [] = []) /\
   (!f h1 t1 h2 t2. MAP2 (f:A->B->C) (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))`,
  REWRITE_TAC[MAP2_DEF; HD; TL]);;
***)

logfile "list-nth-def";;

let EL =
  let def = new_recursive_definition num_RECURSION
      `(!l. EL 0 (l : A list) = HD l) /\
       (!n l. EL (SUC n) (l : A list) = EL n (TL l))` in
  prove
  (`(!h t. EL 0 (CONS (h : A) t) = h) /\
    (!h t n. n < LENGTH t ==> EL (SUC n) (CONS (h : A) t) = EL n t)`,
   REWRITE_TAC [def; HD; TL]);;

export_thm EL;;

logfile "list-filter-def";;

let FILTER = new_recursive_definition list_RECURSION
  `(!P. FILTER (P:A->bool) [] = []) /\
   (!P h t. FILTER (P:A->bool) (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)`;;

export_thm FILTER;;

(***
let ASSOC = new_recursive_definition list_RECURSION
  `!a h t. ASSOC a (CONS (h:A#B) t) = if FST h = a then SND h else ASSOC a t`;;

let ITLIST2_DEF = new_recursive_definition list_RECURSION
  `(!f b l2. ITLIST2 (f:A->B->C->C) [] l2 b = b) /\
   (!f b l2 h1 t1. ITLIST2 (f:A->B->C->C) (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))`;;

let ITLIST2 = prove
 (`(!f b. ITLIST2 (f:A->B->C->C) [] [] b = b) /\
   (!f b h1 t1 h2 t2. ITLIST2 (f:A->B->C->C) (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))`,
  REWRITE_TAC[ITLIST2_DEF; HD; TL]);;

let ZIP_DEF = new_recursive_definition list_RECURSION
  `(!l2. ZIP ([]:A list) (l2:B list) = []) /\
   (!l2 h1 t1. ZIP (CONS (h1:A) t1) (l2:B list) = CONS (h1,HD l2) (ZIP t1 (TL l2)))`;;

let ZIP = prove
 (`(ZIP ([]:A list) ([]:B list) = []) /\
   (!h1 h2 t1 t2. ZIP (CONS (h1:A) t1) (CONS (h2:B) t2) = CONS (h1,h2) (ZIP t1 t2))`,
  REWRITE_TAC[ZIP_DEF; HD; TL]);;
***)

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

logfile "list-thm";;

let NOT_CONS_NIL = prove
 (`!(h:A) t. ~(CONS h t = [])`,
  REWRITE_TAC[distinctness "list"]);;

export_thm NOT_CONS_NIL;;

logfile "list-last-thm";;

let LAST_CLAUSES = prove
 (`(!h. LAST [h:A] = h) /\
   (!h k t. LAST (CONS (h:A) (CONS k t)) = LAST (CONS k t))`,
  REWRITE_TAC[LAST; NOT_CONS_NIL]);;

export_thm LAST_CLAUSES;;

logfile "list-append-thm";;

let APPEND_NIL = prove
 (`!l:A list. APPEND l [] = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_NIL;;

let APPEND_ASSOC = prove
 (`!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm APPEND_ASSOC;;

logfile "list-reverse-thm";;

let REVERSE_APPEND = prove
 (`!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; REVERSE; APPEND_NIL; APPEND_ASSOC]);;

export_thm REVERSE_APPEND;;

let REVERSE_REVERSE = prove
 (`!l:A list. REVERSE(REVERSE l) = l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[REVERSE; REVERSE_APPEND; APPEND]);;

export_thm REVERSE_REVERSE;;

logfile "list-thm";;

let CONS_11 = prove
 (`!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\ (t1 = t2)`,
  REWRITE_TAC[injectivity "list"]);;

export_thm CONS_11;;

let list_CASES = prove
 (`!l:(A)list. (l = []) \/ ?h t. l = CONS h t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[CONS_11; NOT_CONS_NIL] THEN
  MESON_TAC[]);;

export_thm list_CASES;;

logfile "list-append-thm";;

let LENGTH_APPEND = prove
 (`!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LENGTH; ADD_CLAUSES]);;

export_thm LENGTH_APPEND;;

logfile "list-map-thm";;

let MAP_APPEND = prove
 (`!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; APPEND]);;

export_thm MAP_APPEND;;

let LENGTH_MAP = prove
 (`!l. !f:A->B. LENGTH (MAP f l) = LENGTH l`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MAP; LENGTH]);;

export_thm LENGTH_MAP;;

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

logfile "list-map-thm";;

let MAP_o = prove
 (`!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; o_THM]);;

export_thm MAP_o;;

logfile "list-quant-thm";;

let MAP_EQ = prove
 (`!(f:A->B) (g:A->B) l. ALL (\x. f x = g x) l ==> (MAP f l = MAP g l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MAP; ALL] THEN ASM_MESON_TAC[]);;

export_thm MAP_EQ;;

logfile "list-member-thm";;

let ALL_IMP = prove
 (`!P Q l. (!x. MEM (x:A) l /\ P x ==> Q x) /\ ALL P l ==> ALL Q l`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[MEM; ALL] THEN ASM_MESON_TAC[]);;

export_thm ALL_IMP;;

logfile "list-quant-thm";;

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

(***
let MAP_EQ_ALL2 = prove
 (`!(f:A->B) l m. ALL2 (\x y. f x = f y) l m ==> (MAP f l = MAP f m)`,
  GEN_TAC THEN REPEAT LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; ALL2; CONS_11] THEN
  ASM_MESON_TAC[]);;

let ALL2_MAP = prove
 (`!P (f:A->B) l. ALL2 P (MAP f l) l <=> ALL (\a. P (f a) a) l`,
  GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP; ALL]);;

let MAP_EQ_DEGEN = prove
 (`!l f. ALL (\x. f(x) = (x:A)) l ==> (MAP f l = l)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL; MAP; CONS_11] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let ALL2_AND_RIGHT = prove
 (`!l m P Q. ALL2 (\x y. P x /\ Q (x:A) (y:B)) l m <=> ALL P l /\ ALL2 Q l m`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL; ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ITLIST_APPEND = prove
 (`!f a l1 l2. ITLIST (f:A->B->B) (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ITLIST; APPEND]);;

let ITLIST_EXTRA = prove
 (`!(f:A->B->B) b l a. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)`,
  REWRITE_TAC[ITLIST_APPEND; ITLIST]);;
***)

logfile "list-quant-thm";;

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

logfile "list-member-thm";;

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

logfile "list-replicate-thm";;

let LENGTH_REPLICATE = prove
 (`!n x. LENGTH (REPLICATE n (x:A)) = n`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[LENGTH; REPLICATE]);;

export_thm LENGTH_REPLICATE;;

logfile "list-quant-thm";;

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

logfile "list-member-thm";;

let MEM_APPEND = prove
 (`!x l1 l2. MEM (x:A) (APPEND l1 l2) <=> MEM x l1 \/ MEM x l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; APPEND; DISJ_ACI]);;

export_thm MEM_APPEND;;

let MEM_MAP = prove
 (`!f y l. MEM y (MAP (f:A->B) l) <=> ?x. MEM x l /\ (y = f x)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MEM; MAP] THEN MESON_TAC[]);;

export_thm MEM_MAP;;

logfile "list-filter-thm";;

let FILTER_APPEND = prove
 (`!P l1 l2. FILTER (P:A->bool) (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[FILTER; APPEND] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[APPEND]);;

export_thm FILTER_APPEND;;

let FILTER_MAP = prove
 (`!P (f:A->B) l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)`,
  GEN_TAC THEN GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[MAP; FILTER; o_THM] THEN COND_CASES_TAC THEN
  REWRITE_TAC[MAP]);;

export_thm FILTER_MAP;;

logfile "list-member-thm";;

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

(***
let MAP_FST_ZIP = prove
 (`!l1 l2. (LENGTH (l1 : A list) = LENGTH (l2 : B list)) ==> (MAP FST (ZIP l1 l2) = l1)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let MAP_SND_ZIP = prove
 (`!l1 l2. (LENGTH (l1 : A list) = LENGTH (l2 : B list)) ==> (MAP SND (ZIP l1 l2) = l2)`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; SUC_INJ; MAP; FST; ZIP; NOT_SUC]);;

let MEM_ASSOC = prove
 (`!l x. MEM (x,ASSOC x l) (l:(A#B)list) <=> MEM x (MAP FST l)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[MEM; MAP; ASSOC] THEN
  GEN_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[PAIR; FST]);;
***)

logfile "list-quant-thm";;

let ALL_APPEND = prove
 (`!P l1 l2. ALL (P:A->bool) (APPEND l1 l2) <=> ALL P l1 /\ ALL P l2`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL; APPEND; GSYM CONJ_ASSOC]);;

export_thm ALL_APPEND;;

logfile "list-nth-thm";;

let EL_0 = prove
 (`!(h:A) t. EL 0 (CONS h t) = h`,
  ACCEPT_TAC (CONJUNCT1 EL));;

export_thm EL_0;;

let EL_SUC = prove
 (`!(h:A) t n. n < LENGTH t ==> EL (SUC n) (CONS h t) = EL n t`,
  ACCEPT_TAC (CONJUNCT2 EL));;

export_thm EL_SUC;;

logfile "list-member-thm";;

let MEM_EL = prove
 (`!l n. n < LENGTH (l : A list) ==> MEM (EL n l) l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[MEM; CONJUNCT1 LT; LENGTH] THEN
  INDUCT_TAC THEN ASM_SIMP_TAC[EL; HD; LT_SUC; TL]);;

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

(***
let ALL2_MAP2 = prove
 (`!P (f:A->C) (g:B->C) l m.
     ALL2 P (MAP f l) (MAP g m) = ALL2 (\x y. P (f x) (g y)) l m`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2; MAP]);;

let AND_ALL2 = prove
 (`!P Q l m.
     ALL2 P l m /\ ALL2 Q l m <=> ALL2 (\x y. P (x:A) (y:B) /\ Q x y) l m`,
  GEN_TAC THEN GEN_TAC THEN CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL2] THEN
  REWRITE_TAC[CONJ_ACI]);;

let ALL2_ALL = prove
 (`!P l. ALL2 P l l <=> ALL (\x. P (x:A) x) l`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[ALL2; ALL]);;
***)

logfile "list-append-thm";;

let APPEND_EQ_NIL = prove
 (`!l m. (APPEND (l:A list) m = []) <=> (l = []) /\ (m = [])`,
  LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC[APPEND; NOT_CONS_NIL]);;

export_thm APPEND_EQ_NIL;;

(***
let LENGTH_MAP2 = prove
 (`!(f:A->B->C) l m. (LENGTH l = LENGTH m) ==> (LENGTH (MAP2 f l m) = LENGTH m)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[LENGTH; NOT_CONS_NIL; NOT_SUC; MAP2; SUC_INJ]);;
***)

logfile "list-map-thm";;

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

(***
let APPEND_BUTLAST_LAST = prove
 (`!(l:A list). ~(l = []) ==> APPEND (BUTLAST l) [LAST l] = l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LAST; BUTLAST; NOT_CONS_NIL] THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[APPEND]);;
***)

logfile "list-last-thm";;

let LAST_APPEND = prove
 (`!(p:A list) q. LAST(APPEND p q) = if q = [] then LAST p else LAST q`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[APPEND; LAST; APPEND_EQ_NIL] THEN
  MESON_TAC[]);;

export_thm LAST_APPEND;;

logfile "list-length-thm";;

let LENGTH_TL = prove
 (`!(l:A list). ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; TL; ARITH; SUC_SUB1]);;

export_thm LENGTH_TL;;

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

(*** No longer true with new definition of EL
let EL_TL = prove
 (`!n l. EL n (TL l) = EL (n + 1) l`,
  REWRITE_TAC[GSYM ADD1; EL]);;

let EL_CONS = prove
 (`!n h t. EL n (CONS (h : A) t) = if n = 0 then h else EL (n - 1) t`,
  INDUCT_TAC THEN REWRITE_TAC[EL; HD; TL; NOT_SUC; SUC_SUB1]);;
***)

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

logfile "list-append-thm";;

let HD_APPEND = prove
 (`!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[HD; APPEND; NOT_CONS_NIL]);;

export_thm HD_APPEND;;

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
(* Extra monotonicity theorems for inductive definitions.                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-quant-thm";;

let MONO_ALL = prove
 (`!P Q l. (!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[ALL] THEN ASM_MESON_TAC[]);;

export_thm MONO_ALL;;

(***
let MONO_ALL2 = prove
 (`(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'`,
  DISCH_TAC THEN
  SPEC_TAC(`l':B list`,`l':B list`) THEN SPEC_TAC(`l:A list`,`l:A list`) THEN
  LIST_INDUCT_TAC THEN REWRITE_TAC[ALL2_DEF] THEN
  GEN_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[]);;
***)

monotonicity_theorems := [MONO_ALL(***; MONO_ALL2***)] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec LIST_CONV conv tm =
  if is_cons tm then
    COMB2_CONV (RAND_CONV conv) (LIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then REFL tm
  else failwith "LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-set-def";;

let set_of_list = new_recursive_definition list_RECURSION
  `(set_of_list ([]:A list) = {}) /\
   (!h t. set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))`;;

export_thm set_of_list;;

let list_of_set = new_definition
  `!(s : A set).
     list_of_set s = @l. (set_of_list l = s) /\ (LENGTH l = CARD s)`;;

let LIST_OF_SET_PROPERTIES = prove
 (`!(s : A set).
     FINITE(s) ==> (set_of_list(list_of_set s) = s) /\
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

logfile "list-member-thm";;

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

logfile "list-set-thm";;

let FINITE_SET_OF_LIST = prove
 (`!(l : A list). FINITE (set_of_list l)`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; FINITE_EMPTY];
   ASM_REWRITE_TAC [set_of_list; FINITE_INSERT]]);;

export_thm FINITE_SET_OF_LIST;;

logfile "list-member-thm";;

let IN_SET_OF_LIST = prove
 (`!(x:A) l. x IN (set_of_list l) <=> MEM x l`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NOT_IN_EMPTY; MEM; set_of_list];
   ASM_REWRITE_TAC [IN_INSERT; MEM; set_of_list]]);;

export_thm IN_SET_OF_LIST;;

logfile "list-append-thm";;

let SET_OF_LIST_APPEND = prove
 (`!(l1 : A list) l2.
     set_of_list (APPEND l1 l2) = set_of_list l1 UNION set_of_list l2`,
  REWRITE_TAC [EXTENSION; IN_SET_OF_LIST; IN_UNION; MEM_APPEND]);;

export_thm SET_OF_LIST_APPEND;;

logfile "list-map-thm";;

let SET_OF_LIST_MAP = prove
 (`!(f : A -> B) l.
     set_of_list (MAP f l) = IMAGE f (set_of_list l)`,
  GEN_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES];
   ASM_REWRITE_TAC [set_of_list; MAP; IMAGE_CLAUSES]]);;

export_thm SET_OF_LIST_MAP;;

logfile "list-set-thm";;

let SET_OF_LIST_EQ_EMPTY = prove
 (`!(l : A list). set_of_list l = {} <=> l = []`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [set_of_list];
   REWRITE_TAC [set_of_list; NOT_CONS_NIL; NOT_INSERT_EMPTY]]);;

export_thm SET_OF_LIST_EQ_EMPTY;;

(***
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
  `!r s. pairwise r s <=> !x y. (x:A) IN s /\ y IN s /\ ~(x = y) ==> r x y`;;

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
***)

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

logfile "list-set-thm";;

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

(***
let HAS_SIZE_SET_OF_LIST = prove
 (`!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\x y. ~(x = y)) l`,
  REWRITE_TAC[HAS_SIZE; FINITE_SET_OF_LIST] THEN LIST_INDUCT_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; LENGTH; set_of_list; PAIRWISE; ALL;
               FINITE_SET_OF_LIST; GSYM ALL_MEM; IN_SET_OF_LIST] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[SUC_INJ] THEN
  ASM_MESON_TAC[CARD_SET_OF_LIST_LE; ARITH_RULE `~(SUC n <= n)`]);;
***)

(* ------------------------------------------------------------------------- *)
(* Type of characters, like the HOL88 "ascii" type.                          *)
(* ------------------------------------------------------------------------- *)

let char_INDUCT,char_RECURSION = define_type
 "char = ASCII bool bool bool bool bool bool bool bool";;

new_type_abbrev("string",`:char list`);;

(***
(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = prove
 (`INFINITE(:string)`,
  MP_TAC num_INFINITE THEN REWRITE_TAC[INFINITE; CONTRAPOS_THM] THEN
  DISCH_THEN(MP_TAC o ISPEC `LENGTH:string->num` o MATCH_MP FINITE_IMAGE) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN MESON_TAC[LENGTH_REPLICATE]);;
***)

logfile_end ();;

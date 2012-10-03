(* ========================================================================= *)
(* Theory of wellfounded relations.                                          *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "relations.ml";;

(* ------------------------------------------------------------------------- *)
(* Definition of wellfoundedness for arbitrary (infix) relation <<           *)
(* ------------------------------------------------------------------------- *)

logfile "relation-well-founded-def";;

let WF = new_definition
  `!(r : A -> A -> bool).
     WF r <=> !p. (?x. p x) ==> ?x. p x /\ !y. r y x ==> ~p y`;;

export_thm WF;;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to equality.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "relation-well-founded-thm";;

let WF_EQ = prove
 (`!(r : A -> A -> bool).
     WF r <=> !p. (?x. p x) <=> ?x. p x /\ !y. r y x ==> ~p y`,
  GEN_TAC THEN
  REWRITE_TAC [WF] THEN
  AP_TERM_TAC THEN
  ABS_TAC THEN
  ASM_CASES_TAC `?x. p (x:A)` THENL
  [ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [CONTRAPOS_THM] THEN
   STRIP_TAC THEN
   EXISTS_TAC `x:A` THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm WF_EQ;;

(* ------------------------------------------------------------------------- *)
(* Equivalence of wellfounded induction.                                     *)
(* ------------------------------------------------------------------------- *)

let WF_IND = prove
 (`!(r : A -> A -> bool).
     WF r <=> !p. (!x. (!y. r y x ==> p y) ==> p x) ==> !x. p x`,
  GEN_TAC THEN
  REWRITE_TAC [WF] THEN
  EQ_TAC THENL
  [DISCH_TAC THEN
   GEN_TAC THEN
   POP_ASSUM (MP_TAC o SPEC `\x:A. ~p(x)`) THEN
   REWRITE_TAC [GSYM NOT_FORALL_THM] THEN
   ASM_CASES_TAC `!(x:A). p x` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `~p (x:A)` THEN
    REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC];
   DISCH_TAC THEN
   GEN_TAC THEN
   POP_ASSUM (MP_TAC o SPEC `\x:A. ~p(x)`) THEN
   REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [CONJ_SYM] THEN
   FIRST_X_ASSUM
     (MP_TAC o SPEC `x:A` o REWRITE_RULE [RIGHT_IMP_FORALL_THM]) THEN
   ASM_REWRITE_TAC [NOT_FORALL_THM; NOT_IMP]]);;

export_thm WF_IND;;

(* ------------------------------------------------------------------------- *)
(* Equivalence of the "infinite descending chains" version.                  *)
(* ------------------------------------------------------------------------- *)

logfile "relation-natural-thm";;

let WF_DCHAIN = prove
 (`!(r : A -> A -> bool). WF r <=> ~(?f. !n. r (f (SUC n)) (f n))`,
  GEN_TAC THEN
  REWRITE_TAC [WF; TAUT `(a <=> ~b) <=> (~a <=> b)`; NOT_FORALL_THM] THEN
  EQ_TAC THENL
  [DISCH_THEN CHOOSE_TAC THEN
   POP_ASSUM (MP_TAC o REWRITE_RULE [NOT_IMP]) THEN
   DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) ASSUME_TAC) THEN
   SUBGOAL_THEN `!(x:A). ?y. p x ==> p y /\ r y x` MP_TAC THENL
   [GEN_TAC THEN
    ASM_CASES_TAC `(p : A -> bool) x` THENL
    [ASM_REWRITE_TAC [] THEN
     ONCE_REWRITE_TAC [CONJ_SYM] THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `x:A` o REWRITE_RULE [NOT_EXISTS_THM]) THEN
     ASM_REWRITE_TAC [NOT_FORALL_THM; NOT_IMP];
     ASM_REWRITE_TAC []];
    REWRITE_TAC[SKOLEM_THM] THEN
    DISCH_THEN (X_CHOOSE_THEN `f:A->A` STRIP_ASSUME_TAC) THEN
    CHOOSE_THEN STRIP_ASSUME_TAC (prove_recursive_functions_exist num_RECURSION
     `(s(0) = a:A) /\ (!n. s (SUC n) = f (s n))`) THEN
    EXISTS_TAC `s:num->A` THEN
    ASM_REWRITE_TAC [] THEN
    SUBGOAL_THEN `!n. p (s n) /\ r (s (SUC n) : A) (s n)` MP_TAC THENL
    [INDUCT_TAC THENL
     [ASM_REWRITE_TAC [] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `a:A`) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN (ACCEPT_TAC o CONJUNCT2);
      POP_ASSUM STRIP_ASSUME_TAC THEN
      FIRST_X_ASSUM
        (fun th ->
           MP_TAC (SPEC `(s : num -> A) (SUC n)` th) THEN
           MP_TAC (SPEC `(s : num -> A) n` th)) THEN
      UNDISCH_THEN `!n. s (SUC n) = (f : A -> A) (s n)`
        (fun th -> REWRITE_TAC [GSYM th]) THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      STRIP_TAC];
     ASM_REWRITE_TAC [] THEN
     REPEAT STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `n:num`) THEN
     STRIP_TAC]];
   STRIP_TAC THEN
   EXISTS_TAC `\ (y:A). ?n:num. y = f n` THEN
   REWRITE_TAC [NOT_IMP; NOT_EXISTS_THM] THEN
   REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(f : num -> A) 0` THEN
    EXISTS_TAC `0` THEN
    REFL_TAC;
    FIRST_X_ASSUM SUBST_VAR_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `(f : num -> A) (SUC n)`) THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [NOT_FORALL_THM] THEN
    EXISTS_TAC `SUC n` THEN
    REFL_TAC]]);;

export_thm WF_DCHAIN;;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *uniqueness* part of recursion.                        *)
(* ------------------------------------------------------------------------- *)

let WF_UREC = prove
 (`!r.
     WF r ==>
       !h. (!f g x. (!z. r z x ==> (f z = g z)) ==> (h f x = h g x))
            ==> !(f:A->B) g. (!x. f x = h f x) /\ (!x. g x = h g x)
                              ==> (f = g)`,
  REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
  FIRST_ASSUM MATCH_MP_TAC THEN GEN_TAC THEN
  DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN ASM_REWRITE_TAC[]);;

let WF_UREC_WF = prove
 (`!r.
     (!h. (!f g x. (!z. r z x ==> (f z = g z)) ==> (h f x = h g x))
        ==> !(f:A->bool) g. (!x. f x = h f x) /\ (!x. g x = h g x)
                          ==> (f = g))
     ==> WF r`,
  GEN_TAC THEN
  REWRITE_TAC [WF_IND] THEN
  DISCH_TAC THEN
  GEN_TAC THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `\f x. p(x:A) \/ !z:A. r z x ==> f(z)`) THEN
  REWRITE_TAC [] THEN
  W (C SUBGOAL_THEN (fun t -> REWRITE_TAC[t]) o funpow 2 lhand o snd) THENL
  [REPEAT STRIP_TAC THEN
   ASM_CASES_TAC `(p : A -> bool) x` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    AP_TERM_TAC THEN
    ABS_TAC THEN
    ASM_CASES_TAC `(r : A -> A -> bool) z x` THENL
    [ASM_REWRITE_TAC [] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC []]];
   DISCH_THEN (MP_TAC o SPECL [`p:A->bool`; `\x:A. T`]) THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   GEN_TAC THEN
   ASM_CASES_TAC `(p : A -> bool) x` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
    ASM_REWRITE_TAC []]]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of recursion with "inductive invariant" (Krstic/Matthews).  *)
(* ------------------------------------------------------------------------- *)

let WF_REC_INVARIANT = prove
 (`!r.
     WF r
     ==> !h s. (!f g x. (!z. r z x ==> (f z = g z) /\ s z (f z))
                        ==> (h f x = h g x) /\ s x (h f x))
               ==> ?(f:A->B). !x. (f x = h f x)`,
  let lemma = prove_inductive_relations_exist
    `!f:A->B x. (!z. r z x ==> t z (f z)) ==> t x (h f x)` in
  REWRITE_TAC [WF_IND] THEN
  REPEAT STRIP_TAC THEN
  X_CHOOSE_THEN `t:A->B->bool` STRIP_ASSUME_TAC lemma THEN
  SUBGOAL_THEN `!x:A. ?!y:B. t x y` MP_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM (fun th -> GEN_REWRITE_TAC BINDER_CONV [th]) THEN
   SUBGOAL_THEN `!x:A y:B. t x y ==> s x y` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`f : A -> B`; `f : A -> B`; `x' : A`]) THEN
    ASM_REWRITE_TAC [];
    STRIP_TAC THEN
    ASM_MESON_TAC []];
   ASM_MESON_TAC []]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *existence* part of recursion.                         *)
(* ------------------------------------------------------------------------- *)

let WF_REC = prove
 (`!r.
     WF r
     ==> !h. (!f g x. (!z. r z x ==> (f z = g z)) ==> (h f x = h g x))
             ==> ?f:A->B. !x. f x = h f x`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC_INVARIANT) THEN
  EXISTS_TAC `\x:A y:B. T` THEN ASM_REWRITE_TAC[]);;

let WF_REC_WF = prove
 (`!r.
     (!h. (!f g x. (!z. r z x ==> (f z = g z)) ==> (h f x = h g x))
                   ==> ?f:A->num. !x. f x = h f x)
     ==> WF r`,
  GEN_TAC THEN
  DISCH_TAC THEN REWRITE_TAC [WF_DCHAIN] THEN
  DISCH_THEN (X_CHOOSE_TAC `x:num->A`) THEN
  SUBGOAL_THEN `!n. r ((x:num->A)(@m. r (x m) (x n))) (x n)` ASSUME_TAC THENL
   [CONV_TAC(BINDER_CONV SELECT_CONV) THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC
   `\f:A->num. \y:A. if ?p:num. y = x(p)
                     then SUC(f(x(@m. r (x m) y)))
                     else 0`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    FIRST_ASSUM(X_CHOOSE_THEN `p:num` SUBST_ALL_TAC) THEN
    AP_TERM_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM MATCH_ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:A->num` MP_TAC) THEN
  DISCH_THEN(MP_TAC o GEN `n:num` o SPEC `(x:num->A) n`) THEN
  SUBGOAL_THEN `!n. ?p. (x:num->A) n = x p` (fun th -> REWRITE_TAC[th]) THENL
   [MESON_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `!n:num. ?k. f(x(k):A) < f(x(n))` ASSUME_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `@m:num. r (x(m):A) (x(n))` THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN REWRITE_TAC[LT];
    MP_TAC(SPEC `\n:num. ?i:num. n = f(x(i):A)` num_WOP) THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combine the two versions of the recursion theorem.                        *)
(* ------------------------------------------------------------------------- *)

let WF_EREC = prove
 (`!r.
     WF r ==>
       !h. (!f g x. (!z. r z x ==> (f z = g z)) ==> (h f x = h g x))
            ==> ?!f:A->B. !x. f x = h f x`,
  MESON_TAC [WF_REC; WF_UREC]);;

export_thm WF_EREC;;

(* ------------------------------------------------------------------------- *)
(* Some preservation theorems for wellfoundedness.                           *)
(* ------------------------------------------------------------------------- *)

logfile "relation-well-founded-thm";;

let wellfounded_subrelation = prove
 (`!(r : A -> A -> bool) s. subrelation r s /\ WF s ==> WF r`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [subrelation] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN REWRITE_TAC[WF] THEN
  DISCH_TAC THEN GEN_TAC THEN DISCH_THEN(ANTE_RES_THEN MP_TAC) THEN
  UNDISCH_TAC `!(x:A) (y:A). r x y ==> s x y` THEN MESON_TAC[]);;

export_thm wellfounded_subrelation;;

let WF_SUBSET = prove
 (`!r s. (!(x:A) y. r x y ==> s x y) /\ WF s ==> WF r`,
  ACCEPT_TAC (REWRITE_RULE [subrelation] wellfounded_subrelation));;

let WF_MEASURE_GEN = prove
 (`!r (m:A->B). WF r ==> WF (\x y. r (m x) (m y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WF_IND] THEN REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `\z:B. !x:A. (m(x) = z) ==> p x`) THEN
  UNDISCH_TAC `!x. (!y. r ((m:A->B) y) (m x) ==> p y) ==> p x` THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

export_thm WF_MEASURE_GEN;;

let WF_LEX_DEPENDENT = prove
 (`!(r:A->A->bool) (s:A->B->B->bool). WF r /\ (!a. WF (s a))
         ==> WF (\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s x1 y1 y2)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[WF] THEN STRIP_TAC THEN
  X_GEN_TAC `p:A#B->bool` THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  GEN_REWRITE_TAC I [FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a0:A`; `b0:B`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `\a:A. ?b:B. p(a,b)`) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`a0:A`; `b0:B`]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_TAC `b1:B`) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:A`; `\b. (p:A#B->bool) (a,b)`]) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `b1:B`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:B` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_TAC THEN EXISTS_TAC `(a:A,b:B)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN ASM_MESON_TAC[]);;

export_thm WF_LEX_DEPENDENT;;

let WF_LEX = prove
 (`!(r:A->A->bool) (s:B->B->bool). WF r /\ WF s
         ==> WF (\(x1,y1) (x2,y2). r x1 x2 \/ (x1 = x2) /\ s y1 y2)`,
  SIMP_TAC[WF_LEX_DEPENDENT; ETA_AX]);;

export_thm WF_LEX;;

let WF_POINTWISE = prove
 (`!r s.
     WF(r:A->A->bool) /\ WF(s:B->B->bool)
     ==> WF(\(x1,y1) (x2,y2). r x1 x2 /\ s y1 y2)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(GEN_ALL WF_SUBSET) THEN EXISTS_TAC
   `\(x1,y1) (x2,y2). r x1 x2 \/ (x1:A = x2) /\ s (y1:B) (y2:B)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM] THEN CONV_TAC TAUT;
    MATCH_MP_TAC WF_LEX THEN ASM_REWRITE_TAC[]]);;

export_thm WF_POINTWISE;;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness properties of natural numbers.                            *)
(* ------------------------------------------------------------------------- *)

logfile "relation-natural-thm";;

let WF_num = prove
 (`WF(<)`,
  REWRITE_TAC[WF_IND; num_WF]);;

export_thm WF_num;;

let WF_REC_num = prove
 (`!h. (!f g n. (!m. m < n ==> (f m = g m)) ==> (h f n = h g n))
        ==> ?f:num->A. !n. f n = h f n`,
  MATCH_ACCEPT_TAC(MATCH_MP WF_REC WF_num));;

(* ------------------------------------------------------------------------- *)
(* Natural number measures (useful in program verification).                 *)
(* ------------------------------------------------------------------------- *)

logfile "relation-natural-def";;

let MEASURE = new_definition
  `!m (x:A) y. MEASURE m x y = m x < m y`;;

export_thm MEASURE;;

let MEASURE_EXPAND = prove
  (`!m. MEASURE m = \(x:A) y. m x < m y`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   REWRITE_TAC [MEASURE]);;

logfile "relation-natural-thm";;

let WF_MEASURE = prove
 (`!m:A->num. WF(MEASURE m)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [MEASURE_EXPAND] THEN
  MATCH_MP_TAC WF_MEASURE_GEN THEN
  MATCH_ACCEPT_TAC WF_num);;

export_thm WF_MEASURE;;

let MEASURE_LE = prove
 (`!m a b. (!y. MEASURE m (y:A) a ==> MEASURE m y b) <=> m(a) <= m(b)`,
    REWRITE_TAC[MEASURE] THEN MESON_TAC[NOT_LE; LTE_TRANS; LT_REFL]);;

export_thm MEASURE_LE;;

(* ------------------------------------------------------------------------- *)
(* Trivially, a WF relation is irreflexive.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "relation-well-founded-thm";;

let wellfounded_irreflexive = prove
 (`!(r : A -> A -> bool). WF r ==> irreflexive r`,
  REWRITE_TAC [irreflexive_def; GSYM RIGHT_FORALL_IMP_THM] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [WF] THEN
  DISCH_THEN (MP_TAC o SPEC `\y:A. y = x`) THEN
  REWRITE_TAC [] THEN
  ANTS_TAC THENL
  [EXISTS_TAC `x:A` THEN
   REFL_TAC;
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM SUBST_VAR_TAC THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `x:A`) THEN
   ASM_REWRITE_TAC []]);;

export_thm wellfounded_irreflexive;;

let WF_REFL = prove
 (`!(r : A -> A -> bool) x. WF r ==> ~r x x`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MATCH_MP_TAC irreflexive THEN
  MATCH_MP_TAC wellfounded_irreflexive THEN
  FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Even more trivially, the everywhere-false relation is wellfounded.        *)
(* ------------------------------------------------------------------------- *)

let wellfounded_emptyr = prove
 (`WF (emptyr : A -> A -> bool)`,
  REWRITE_TAC [WF; emptyr]);;

export_thm wellfounded_emptyr;;

let WF_FALSE = prove
 (`WF(\x y:A. F)`,
  REWRITE_TAC[WF]);;

(* ------------------------------------------------------------------------- *)
(* Tail recursion.                                                           *)
(* ------------------------------------------------------------------------- *)

logfile "relation-natural-thm";;

let WF_REC_TAIL = prove
 (`!p g h. ?(f : A -> B). !x. f x = if p x then f (g x) else h x`,
  let lemma1 = prove
   (`~(p 0) ==> ((?n. p(SUC n)) <=> (?n. p(n)))`,
    MESON_TAC[num_CASES; NOT_SUC])
  and lemma2 = prove
   (`(p 0) ==> ((!m. m < n ==> p(SUC m)) <=> (!m. m < SUC n ==> p(m)))`,
    REPEAT(DISCH_TAC ORELSE EQ_TAC) THEN INDUCT_TAC THEN
    ASM_MESON_TAC[LT_SUC; LT_0]) in
  REPEAT GEN_TAC THEN
  MP_TAC(GEN `x:A` (ISPECL [`x:A`; `\y:A n:num. g(y):A`] num_RECURSION)) THEN
  REWRITE_TAC[SKOLEM_THM; FORALL_AND_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:A->num->A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:A. if ?n:num. ~p(s x n)
                    then (h:A->B)(@y. ?n. (y = s x n) /\ ~p(s x n) /\
                                          !m. m < n ==> p(s x m))
                    else something_arbitrary:B` THEN
  X_GEN_TAC `x:A` THEN
  SUBGOAL_THEN `!n x:A. s (g x) n :A = s x (SUC n)` ASSUME_TAC THENL
   [INDUCT_TAC THEN ASM_REWRITE_TAC[];
    UNDISCH_THEN `!x:A n. s x (SUC n) :A = g (s x n)` (K ALL_TAC)] THEN
  ASM_CASES_TAC `(p:A->bool) x` THEN ASM_REWRITE_TAC[] THENL
   [ASM_SIMP_TAC[lemma1] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[lemma2; lemma1];
    COND_CASES_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    AP_TERM_TAC THEN MATCH_MP_TAC SELECT_UNIQUE THEN
    REWRITE_TAC[] THEN X_GEN_TAC `y:A` THEN EQ_TAC THENL
     [SIMP_TAC[LEFT_IMP_EXISTS_THM] THEN
      INDUCT_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[LT_0];
      ASM_MESON_TAC[LT]]]);;

export_thm WF_REC_TAIL;;

(* ------------------------------------------------------------------------- *)
(* A more general mix of tail and wellfounded recursion.                     *)
(* ------------------------------------------------------------------------- *)

let WF_REC_TAIL_GENERAL = prove
 (`!r P G H.
           WF r /\
           (!f g x. (!z. r z x ==> (f z = g z))
                    ==> (P f x <=> P g x) /\ G f x = G g x /\ H f x = H g x) /\
           (!f g x. (!z. r z x ==> (f z = g z)) ==> (H f x = H g x)) /\
           (!f x y. P f x /\ r y (G f x) ==> r y x)
           ==> ?f:A->B. !x. f x = if P f x then f(G f x) else H f x`,
  REPEAT STRIP_TAC THEN
  CHOOSE_THEN MP_TAC
   (prove_inductive_relations_exist
     `(!x:A. ~(P f x) ==> terminates f x) /\
      (!x. P (f:A->B) x /\ terminates f (G f x) ==> terminates f x)`) THEN
  REWRITE_TAC[FORALL_AND_THM] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
  SUBGOAL_THEN
   `?while. !f:A->B x:A. while f x = if P f x then while f (G f x) else x`
   (STRIP_ASSUME_TAC o GSYM)
  THENL [REWRITE_TAC[GSYM SKOLEM_THM; WF_REC_TAIL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?f:A->B. !x. f x = if terminates f x then H f (while f x :A) else anything`
  MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP WF_REC) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[]
     `(a = b) /\ (a /\ b ==> (x = y) /\ ((f:A->B) x = g x))
      ==> ((if a then f x else d) = (if b then g y else d))`) THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
       `!f g x.
           (!x y. P f x /\ r y (G (f:A->B) x) ==> r y x) /\
           (!y:A. (!z:A. r z y ==> r z x)
                  ==> (P f y = P g y) /\ (G f y = G g y))
               ==> terminates f x ==> terminates g x`
       (fun th -> EQ_TAC THEN MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
      GEN_TAC THEN GEN_TAC THEN
      REWRITE_TAC[RIGHT_FORALL_IMP_THM; IMP_CONJ] THEN DISCH_TAC THEN
      ONCE_REWRITE_TAC[TAUT `a ==> b ==> c <=> b ==> a ==> c`] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      SUBGOAL_THEN
       `!x:A. terminates (f:A->B) x /\
              (!y:A. (!z:A. r z y ==> r z x)
                     ==> (P f y <=> P g y) /\ (G f y :A = G g y))
              ==> (while f x :A = while g x)`
       (fun th -> MATCH_MP_TAC th THEN ASM_MESON_TAC[]) THEN
      REWRITE_TAC[IMP_CONJ] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN
       `!f:A->B. (!x:A y:A. P f x /\ r y (G f x) ==> r y x)
         ==> !x. terminates f x ==> !y. r y (while f x) ==> r y x`
       (fun th -> ASM_MESON_TAC[th]) THEN
      GEN_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_MESON_TAC[]];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
    DISCH_THEN(fun th -> ASSUME_TAC(GSYM th) THEN MP_TAC th) THEN
    MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `x:A` THEN
    ASM_CASES_TAC `P (f:A->B) (x:A) :bool` THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to apply WF induction on a free "measured" term in the goal.       *)
(* ------------------------------------------------------------------------- *)

let WF_INDUCT_TAC =
  let qqconv =
    let pth = prove
     (`(!x. P x ==> !y. Q (x:A) (y:B)) <=> !y x. P x ==> Q x y`, MESON_TAC[]) in
    GEN_REWRITE_CONV I [pth]
  and eqconv =
    let pth = prove
     (`(!m. P (m:A) ==> (m = e) ==> Q) <=> (P e ==> Q)`, MESON_TAC[]) in
    REWR_CONV pth in
  let rec qqconvs tm =
    try (qqconv THENC BINDER_CONV qqconvs) tm
    with Failure _ -> eqconv tm in
  fun tm (asl,w as gl) ->
    let fvs = frees tm
    and gv = genvar(type_of tm) in
    let pat = list_mk_forall(gv::fvs,mk_imp(mk_eq(gv,tm),w)) in
    let th0 = UNDISCH(PART_MATCH rand num_WF pat) in
    let th1 = MP (SPECL (tm::fvs) th0) (REFL tm) in
    let th2 = CONV_RULE(LAND_CONV qqconvs) (DISCH_ALL th1) in
    (MATCH_MP_TAC th2 THEN MAP_EVERY X_GEN_TAC fvs THEN
     CONV_TAC(LAND_CONV qqconvs) THEN DISCH_THEN ASSUME_TAC) gl;;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

logfile "relation-natural-thm";;

let WF_FINITE = prove
 (`!r. (!x. ~(r x x)) /\ (!x y z. r x y /\ r y z ==> r x z) /\
          (!x:A. FINITE {y | r y x})
          ==> WF r`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [WF_DCHAIN] THEN
  DISCH_THEN (X_CHOOSE_THEN `s:num->A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!m n. m < n ==> r ((s:num->A) n) (s m)` ASSUME_TAC THENL
  [MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
   ASM_REWRITE_TAC [] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `(s : num -> A) y` THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  MP_TAC (ISPECL [`s : num -> A`; `UNIV : num set`] INFINITE_IMAGE_INJ) THEN
  ANTS_TAC THENL
  [REWRITE_TAC [num_INFINITE] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`x : num`; `y : num`] LT_CASES) THEN
   STRIP_TAC THENL
   [SUBGOAL_THEN `r ((s : num -> A) y) (s x) : bool` MP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC []];
    SUBGOAL_THEN `r ((s : num -> A) x) (s y) : bool` MP_TAC THENL
    [FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC;
     ASM_REWRITE_TAC []]];
   ALL_TAC] THEN
  REWRITE_TAC [INFINITE] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `s(0) INSERT {y:A | r y (s(0))}` THEN
  ASM_REWRITE_TAC [FINITE_INSERT] THEN
  REWRITE_TAC [SUBSET; FORALL_IN_IMAGE; IN_UNIV; IN_INSERT] THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [];
   DISJ2_TAC THEN
   REWRITE_TAC [IN_ELIM] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   MATCH_ACCEPT_TAC LT_0]);;

export_thm WF_FINITE;;

let wellfounded_successor = prove
 (`WF successor`,
  MATCH_MP_TAC wellfounded_subrelation THEN
  EXISTS_TAC `(<)` THEN
  REWRITE_TAC [subrelation_successor_lt; WF_num]);;

export_thm wellfounded_successor;;

let irreflexive_successor = prove
 (`irreflexive successor`,
  MATCH_MP_TAC wellfounded_irreflexive THEN
  ACCEPT_TAC wellfounded_successor);;

export_thm irreflexive_successor;;

logfile_end ();;

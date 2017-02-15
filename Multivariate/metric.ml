(* ========================================================================= *)
(* Formalization of general topological and metric spaces in HOL Light       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(*                (c) Copyright, Marco Maggesi 2014                          *)
(* ========================================================================= *)

needs "Multivariate/misc.ml";;
needs "Library/iter.ml";;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Instrument classical tactics to attach label to inductive hypothesis.     *)
(* ------------------------------------------------------------------------- *)

let LABEL_INDUCT_TAC =
  let IND_TAC = MATCH_MP_TAC num_INDUCTION THEN CONJ_TAC in
  fun (asl,w as gl) ->
    let s = fst (dest_var (fst (dest_forall w)))  in
    (IND_TAC THENL
     [ALL_TAC; GEN_TAC THEN DISCH_THEN (LABEL_TAC("ind_"^s))])
    gl;;

let LABEL_ABBREV_TAC tm =
  let cvs,t = dest_eq tm in
  let v,vs = strip_comb cvs in
  let s = name_of v in
  let rs = list_mk_abs(vs,t) in
  let eq = mk_eq(rs,v) in
  let th1 = itlist (fun v th -> CONV_RULE(LAND_CONV BETA_CONV) (AP_THM th v))
                   (rev vs) (ASSUME eq) in
  let th2 = SIMPLE_CHOOSE v (SIMPLE_EXISTS v (GENL vs th1)) in
  let th3 = PROVE_HYP (EXISTS(mk_exists(v,eq),rs) (REFL rs)) th2 in
  fun (asl,w as gl) ->
    let avoids = itlist (union o frees o concl o snd) asl (frees w) in
    if mem v avoids then failwith "LABEL_ABBREV_TAC: variable already used" else
    CHOOSE_THEN
     (fun th -> RULE_ASSUM_TAC(PURE_ONCE_REWRITE_RULE[th]) THEN
                PURE_ONCE_REWRITE_TAC[th] THEN
                LABEL_TAC s th)
     th3 gl;;

(* ------------------------------------------------------------------------- *)
(* Further tactics for structuring the proof flow.                           *)
(* ------------------------------------------------------------------------- *)

let CUT_TAC : term -> tactic =
  let th = MESON [] `(p ==> q) /\ p ==> q`
  and ptm = `p:bool` in
  fun tm -> MATCH_MP_TAC (INST [tm,ptm] th) THEN CONJ_TAC;;

let CLAIM_TAC s tm = SUBGOAL_THEN tm (DESTRUCT_TAC s);;

let CONJ_LIST = end_itlist CONJ;;

(* ------------------------------------------------------------------------- *)
(* General notion of a topology.                                             *)
(* ------------------------------------------------------------------------- *)

let istopology = new_definition
 `istopology L <=>
        {} IN L /\
        (!s t. s IN L /\ t IN L ==> (s INTER t) IN L) /\
        (!k. k SUBSET L ==> (UNIONS k) IN L)`;;

let topology_tybij_th = prove
 (`?t:(A->bool)->bool. istopology t`,
  EXISTS_TAC `UNIV:(A->bool)->bool` THEN REWRITE_TAC[istopology; IN_UNIV]);;

let topology_tybij =
  new_type_definition "topology" ("topology","open_in") topology_tybij_th;;

let ISTOPOLOGY_OPEN_IN = prove
 (`istopology(open_in top)`,
  MESON_TAC[topology_tybij]);;

let TOPOLOGY_EQ = prove
 (`!top1 top2. top1 = top2 <=> !s. open_in top1 s <=> open_in top2 s`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[ETA_AX] THEN MESON_TAC[topology_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Infer the "universe" from union of all sets in the topology.              *)
(* ------------------------------------------------------------------------- *)

let topspace = new_definition
 `topspace top = UNIONS {s | open_in top s}`;;

(* ------------------------------------------------------------------------- *)
(* Main properties of open sets.                                             *)
(* ------------------------------------------------------------------------- *)

let OPEN_IN_CLAUSES = prove
 (`!top:(A)topology.
        open_in top {} /\
        (!s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)) /\
        (!k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k))`,
  SIMP_TAC[IN; SUBSET; SIMP_RULE[istopology; IN; SUBSET] ISTOPOLOGY_OPEN_IN]);;

let OPEN_IN_SUBSET = prove
 (`!top s. open_in top s ==> s SUBSET (topspace top)`,
  REWRITE_TAC[topspace] THEN SET_TAC[]);;

let OPEN_IN_EMPTY = prove
 (`!top. open_in top {}`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_INTER = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s INTER t)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNIONS = prove
 (`!top k. (!s. s IN k ==> open_in top s) ==> open_in top (UNIONS k)`,
  REWRITE_TAC[OPEN_IN_CLAUSES]);;

let OPEN_IN_UNION = prove
 (`!top s t. open_in top s /\ open_in top t ==> open_in top (s UNION t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM UNIONS_2] THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]);;

let OPEN_IN_TOPSPACE = prove
 (`!top. open_in top (topspace top)`,
  SIMP_TAC[topspace; OPEN_IN_UNIONS; IN_ELIM_THM]);;

let OPEN_IN_INTERS = prove
 (`!top s:(A->bool)->bool.
        FINITE s /\ ~(s = {}) /\ (!t. t IN s ==> open_in top t)
        ==> open_in top (INTERS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; IMP_IMP; NOT_INSERT_EMPTY; FORALL_IN_INSERT] THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`; `f:(A->bool)->bool`] THEN
  ASM_CASES_TAC `f:(A->bool)->bool = {}` THEN
  ASM_SIMP_TAC[INTERS_0; INTER_UNIV] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[]);;

let OPEN_IN_SUBOPEN = prove
 (`!top s:A->bool.
        open_in top s <=>
        !x. x IN s ==> ?t. open_in top t /\ x IN t /\ t SUBSET s`,
  REPEAT GEN_TAC THEN EQ_TAC THENL [MESON_TAC[SUBSET_REFL]; ALL_TAC] THEN
  REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[TAUT `a ==> b /\ c <=> (a ==> b) /\ (a ==> c)`] THEN
  REWRITE_TAC[FORALL_AND_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[GSYM FORALL_IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_UNIONS) THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let closed_in = new_definition
 `closed_in top s <=>
        s SUBSET (topspace top) /\ open_in top (topspace top DIFF s)`;;

let CLOSED_IN_SUBSET = prove
 (`!top s. closed_in top s ==> s SUBSET (topspace top)`,
  MESON_TAC[closed_in]);;

let CLOSED_IN_EMPTY = prove
 (`!top. closed_in top {}`,
  REWRITE_TAC[closed_in; EMPTY_SUBSET; DIFF_EMPTY; OPEN_IN_TOPSPACE]);;

let CLOSED_IN_TOPSPACE = prove
 (`!top. closed_in top (topspace top)`,
  REWRITE_TAC[closed_in; SUBSET_REFL; DIFF_EQ_EMPTY; OPEN_IN_EMPTY]);;

let CLOSED_IN_UNION = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s UNION t)`,
  SIMP_TAC[closed_in; UNION_SUBSET; OPEN_IN_INTER;
           SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`]);;

let CLOSED_IN_INTERS = prove
 (`!top k:(A->bool)->bool.
        ~(k = {}) /\ (!s. s IN k ==> closed_in top s)
        ==> closed_in top (INTERS k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[closed_in] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `topspace top DIFF INTERS k :A->bool =
                UNIONS {topspace top DIFF s | s IN k}` SUBST1_TAC
  THENL [ALL_TAC; MATCH_MP_TAC OPEN_IN_UNIONS THEN ASM SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE] THEN
  REWRITE_TAC[IN_UNIONS; IN_INTERS; IN_DIFF; EXISTS_IN_IMAGE] THEN
  MESON_TAC[]);;

let CLOSED_IN_INTER = prove
 (`!top s t. closed_in top s /\ closed_in top t ==> closed_in top (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_2] THEN
  MATCH_MP_TAC CLOSED_IN_INTERS THEN ASM SET_TAC[]);;

let OPEN_IN_CLOSED_IN_EQ = prove
 (`!top s. open_in top s <=>
           s SUBSET topspace top /\ closed_in top (topspace top DIFF s)`,
  REWRITE_TAC[closed_in; SET_RULE `(u DIFF s) SUBSET u`] THEN
  REWRITE_TAC[SET_RULE `u DIFF (u DIFF s) = u INTER s`] THEN
  MESON_TAC[OPEN_IN_SUBSET; SET_RULE `s SUBSET t ==> t INTER s = s`]);;

let OPEN_IN_CLOSED_IN = prove
 (`!s. s SUBSET topspace top
       ==> (open_in top s <=> closed_in top (topspace top DIFF s))`,
  SIMP_TAC[OPEN_IN_CLOSED_IN_EQ]);;

let OPEN_IN_DIFF = prove
 (`!top s t:A->bool.
      open_in top s /\ closed_in top t ==> open_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_MESON_TAC[closed_in]]);;

let CLOSED_IN_DIFF = prove
 (`!top s t:A->bool.
        closed_in top s /\ open_in top t ==> closed_in top (s DIFF t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s DIFF t :A->bool = s INTER (topspace top DIFF t)`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET) THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_INTER THEN ASM_MESON_TAC[OPEN_IN_CLOSED_IN_EQ]]);;

let CLOSED_IN_UNIONS = prove
 (`!top s. FINITE s /\ (!t. t IN s ==> closed_in top t)
           ==> closed_in top (UNIONS s)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; CLOSED_IN_EMPTY; IN_INSERT] THEN
  MESON_TAC[CLOSED_IN_UNION]);;

let CLOSED_IN_LOCALLY_FINITE_UNIONS = prove
 (`!top f:(A->bool)->bool.
        (!s. s IN f ==> closed_in top s) /\
        (!x. x IN topspace top
             ==> ?v. open_in top v /\ x IN v /\
                     FINITE {s | s IN f /\ ~(s INTER v = {})})
        ==> closed_in top (UNIONS f)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closed_in] THEN CONJ_TAC THENL
    [RULE_ASSUM_TAC(REWRITE_RULE[closed_in]) THEN
     ASM_SIMP_TAC[UNIONS_SUBSET];
     ALL_TAC] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:A->bool` STRIP_ASSUME_TAC) THEN EXISTS_TAC
    `v DIFF UNIONS {s | s IN f /\ ~(s INTER v = {})}:A->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF; GSYM CONJ_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_IN_UNIONS THEN ASM_SIMP_TAC[IN_ELIM_THM];
    FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Subspace topology.                                                        *)
(* ------------------------------------------------------------------------- *)

let subtopology = new_definition
 `subtopology top u = topology {s INTER u | open_in top s}`;;

let ISTOPLOGY_SUBTOPOLOGY = prove
 (`!top u:A->bool. istopology {s INTER u | open_in top s}`,
  REWRITE_TAC[istopology; SET_RULE
   `{s INTER u | open_in top s} =
    IMAGE (\s. s INTER u) {s | open_in top s}`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_IN_IMAGE; RIGHT_FORALL_IMP_THM] THEN
  REWRITE_TAC[SUBSET_IMAGE; IN_IMAGE; IN_ELIM_THM; SUBSET] THEN
  REPEAT GEN_TAC THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{}:A->bool` THEN REWRITE_TAC[OPEN_IN_EMPTY; INTER_EMPTY];
    SIMP_TAC[SET_RULE `(s INTER u) INTER t INTER u = (s INTER t) INTER u`] THEN
    ASM_MESON_TAC[OPEN_IN_INTER];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:(A->bool)->bool`; `g:(A->bool)->bool`] THEN
    STRIP_TAC THEN EXISTS_TAC `UNIONS g :A->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_UNIONS; INTER_UNIONS] THEN SET_TAC[]]);;

let ISTOPOLOGY_RELATIVE_TO = prove
 (`!top u:A->bool.
        istopology top ==> istopology(top relative_to u)`,
  REWRITE_TAC[RELATIVE_TO] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC LAND_CONV [topology_tybij] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[ISTOPLOGY_SUBTOPOLOGY]);;

let OPEN_IN_SUBTOPOLOGY = prove
 (`!top u s. open_in (subtopology top u) s <=>
                ?t. open_in top t /\ s = t INTER u`,
  REWRITE_TAC[subtopology] THEN
  SIMP_TAC[REWRITE_RULE[CONJUNCT2 topology_tybij] ISTOPLOGY_SUBTOPOLOGY] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM]);;

let OPEN_IN_RELATIVE_TO = prove
 (`!top s t:A->bool.
        (open_in top relative_to s) t <=>
        open_in (subtopology top s) t`,
  REWRITE_TAC[relative_to; OPEN_IN_SUBTOPOLOGY] THEN MESON_TAC[INTER_COMM]);;

let TOPSPACE_SUBTOPOLOGY = prove
 (`!top u. topspace(subtopology top u) = topspace top INTER u`,
  REWRITE_TAC[topspace; OPEN_IN_SUBTOPOLOGY; INTER_UNIONS] THEN
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM]);;

let TOPSPACE_SUBTOPOLOGY_SUBSET = prove
 (`!top s:A->bool. topspace(subtopology top s) SUBSET s`,
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_SUBSET]);;

let CLOSED_IN_SUBTOPOLOGY = prove
 (`!top u s. closed_in (subtopology top u) s <=>
                ?t:A->bool. closed_in top t /\ s = t INTER u`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SUBSET_INTER; OPEN_IN_SUBTOPOLOGY; RIGHT_AND_EXISTS_THM] THEN
  REPEAT STRIP_TAC THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `t:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `topspace top DIFF t :A->bool` THEN
  ASM_SIMP_TAC[CLOSED_IN_TOPSPACE; OPEN_IN_DIFF; CLOSED_IN_DIFF;
               OPEN_IN_TOPSPACE] THEN
  ASM SET_TAC[]);;

let CLOSED_IN_RELATIVE_TO = prove
 (`!top s t:A->bool.
        (closed_in top relative_to s) t <=>
        closed_in (subtopology top s) t`,
  REWRITE_TAC[relative_to; CLOSED_IN_SUBTOPOLOGY] THEN MESON_TAC[INTER_COMM]);;

let SUBTOPOLOGY_SUBTOPOLOGY = prove
 (`!top s t:A->bool.
        subtopology (subtopology top s) t = subtopology top (s INTER t)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[subtopology] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[SET_RULE `{f x | ?y. P y /\ x = g y} = {f(g y) | P y}`] THEN
  REWRITE_TAC[INTER_ASSOC]);;

let OPEN_IN_TOPSPACE_EMPTY = prove
 (`!top:A topology s. topspace top = {} ==> (open_in top s <=> s = {})`,
  MESON_TAC[OPEN_IN_EMPTY; OPEN_IN_SUBSET; SUBSET_EMPTY]);;

let CLOSED_IN_TOPSPACE_EMPTY = prove
 (`!top:A topology s. topspace top = {} ==> (closed_in top s <=> s = {})`,
  MESON_TAC[CLOSED_IN_EMPTY; CLOSED_IN_SUBSET; SUBSET_EMPTY]);;

let OPEN_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. open_in (subtopology top {}) s <=> s = {}`,
  SIMP_TAC[OPEN_IN_TOPSPACE_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY]);;

let CLOSED_IN_SUBTOPOLOGY_EMPTY = prove
 (`!top s. closed_in (subtopology top {}) s <=> s = {}`,
  SIMP_TAC[CLOSED_IN_TOPSPACE_EMPTY; TOPSPACE_SUBTOPOLOGY; INTER_EMPTY]);;

let OPEN_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. open_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[OPEN_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let CLOSED_IN_SUBTOPOLOGY_REFL = prove
 (`!top u:A->bool. closed_in (subtopology top u) u <=> u SUBSET topspace top`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN EQ_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER t SUBSET u`) THEN
    ASM_SIMP_TAC[CLOSED_IN_SUBSET];
    DISCH_TAC THEN EXISTS_TAC `topspace top:A->bool` THEN
    REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_SUPERSET = prove
 (`!top s:A->bool. topspace top SUBSET s ==> subtopology top s = top`,
  REPEAT GEN_TAC THEN SIMP_TAC[TOPOLOGY_EQ; OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN X_GEN_TAC `u:A->bool` THEN EQ_TAC THENL
   [DISCH_THEN(CHOOSE_THEN(CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    DISCH_THEN(fun th -> MP_TAC th THEN
      ASSUME_TAC(MATCH_MP OPEN_IN_SUBSET th)) THEN
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN EXISTS_TAC `u:A->bool` THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[]]);;

let SUBTOPOLOGY_TOPSPACE = prove
 (`!top. subtopology top (topspace top) = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_REFL]);;

let SUBTOPOLOGY_UNIV = prove
 (`!top. subtopology top UNIV = top`,
  SIMP_TAC[SUBTOPOLOGY_SUPERSET; SUBSET_UNIV]);;

let OPEN_IN_IMP_SUBSET = prove
 (`!top s t. open_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN SET_TAC[]);;

let CLOSED_IN_IMP_SUBSET = prove
 (`!top s t. closed_in (subtopology top s) t ==> t SUBSET s`,
  REWRITE_TAC[closed_in; TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        open_in (subtopology top t) s /\ open_in (subtopology top u) s
        ==> open_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER] THEN
  ASM SET_TAC[]);;

let CLOSED_IN_SUBTOPOLOGY_UNION = prove
 (`!top s t u:A->bool.
        closed_in (subtopology top t) s /\ closed_in (subtopology top u) s
        ==> closed_in (subtopology top (t UNION u)) s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSED_IN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `s':A->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `t':A->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s' INTER t':A->bool` THEN ASM_SIMP_TAC[CLOSED_IN_INTER] THEN
  ASM SET_TAC[]);;

let OPEN_IN_SUBTOPOLOGY_INTER_SUBSET = prove
 (`!top s u v:A->bool.
        open_in (subtopology top u) (u INTER s) /\ v SUBSET u
        ==> open_in (subtopology top v) (v INTER s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Derived set (set of limit points).                                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("derived_set_of",(21,"right"));;

let derived_set_of = new_definition
  `top derived_set_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t
               ==> ?y. ~(y = x) /\ y IN s /\ y IN t)}`;;

let DERIVED_SET_OF_RESTRICT = prove
 (`!top s:A->bool.
     top derived_set_of s = top derived_set_of (topspace top INTER s)`,
  REWRITE_TAC[derived_set_of; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_SUBSET]);;

let IN_DERIVED_SET_OF = prove
 (`!top s x:A.
     x IN top derived_set_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. ~(y = x) /\ y IN s /\ y IN t)`,
  REWRITE_TAC[derived_set_of; IN_ELIM_THM]);;

let DERIVED_SET_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top derived_set_of s SUBSET topspace top`,
  REWRITE_TAC[derived_set_of] THEN SET_TAC[]);;

let DERIVED_SET_OF_SUBTOPOLOGY = prove
 (`!top u s:A->bool.
        (subtopology top u) derived_set_of s =
        u INTER top derived_set_of (u INTER s)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[derived_set_of; OPEN_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
  ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN ONCE_REWRITE_TAC[TAUT
   `p /\ q /\ r ==> s <=> r ==> p /\ q ==> s`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2; IN_INTER; IN_ELIM_THM] THEN
  ASM SET_TAC[]);;

let DERIVED_SET_OF_SUBSET_SUBTOPOLOGY = prove
 (`!top s t:A->bool. (subtopology top s) derived_set_of t SUBSET s`,
  SIMP_TAC[DERIVED_SET_OF_SUBTOPOLOGY; INTER_SUBSET]);;

let DERIVED_SET_OF_EMPTY = prove
 (`!top:A topology. top derived_set_of {} = {}`,
  REWRITE_TAC[EXTENSION; IN_DERIVED_SET_OF; NOT_IN_EMPTY] THEN
  MESON_TAC[OPEN_IN_TOPSPACE]);;

let DERIVED_SET_OF_MONO = prove
 (`!top s t:A->bool.
        s SUBSET t ==> top derived_set_of s SUBSET top derived_set_of t`,
  REWRITE_TAC[derived_set_of] THEN SET_TAC[]);;

let DERIVED_SET_OF_UNION = prove
 (`!top s t:A->bool.
       top derived_set_of (s UNION t) =
       top derived_set_of s UNION top derived_set_of t`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; UNION_SUBSET; DERIVED_SET_OF_MONO;
           SUBSET_UNION] THEN
  REWRITE_TAC[SUBSET; IN_DERIVED_SET_OF; IN_UNION] THEN
  X_GEN_TAC `x:A` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `u:A->bool`) (X_CHOOSE_TAC `v:A->bool`)) THEN
  EXISTS_TAC `u INTER v:A->bool` THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN ASM_MESON_TAC[]);;

let DERIVED_SET_OF_UNIONS = prove
 (`!top (f:(A->bool)->bool).
        FINITE f
        ==> top derived_set_of (UNIONS f) =
            UNIONS {top derived_set_of s | s IN f}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; NOT_IN_EMPTY; UNIONS_INSERT; DERIVED_SET_OF_EMPTY;
           DERIVED_SET_OF_UNION; SIMPLE_IMAGE; IMAGE_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Closure with respect to a topological space.                              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("closure_of",(21,"right"));;

let closure_of = new_definition
  `top closure_of s =
   {x:A | x IN topspace top /\
          (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)}`;;

let CLOSURE_OF_RESTRICT = prove
 (`!top s:A->bool. top closure_of s = top closure_of (topspace top INTER s)`,
  REWRITE_TAC[closure_of; EXTENSION; IN_ELIM_THM; IN_INTER] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_SUBSET]);;

let IN_CLOSURE_OF = prove
 (`!top s x:A.
     x IN top closure_of s <=>
     x IN topspace top /\
     (!t. x IN t /\ open_in top t ==> ?y. y IN s /\ y IN t)`,
  REWRITE_TAC[closure_of; IN_ELIM_THM]);;

let CLOSURE_OF = prove
 (`!top s:A->bool.
     top closure_of s =
     topspace top INTER (s UNION top derived_set_of s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION] THEN FIX_TAC "[x]" THEN
  REWRITE_TAC[IN_CLOSURE_OF; IN_DERIVED_SET_OF; IN_UNION; IN_INTER] THEN
  ASM_CASES_TAC `x:A IN topspace top` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM(LABEL_TAC "x_ok") THEN MESON_TAC[]);;

let CLOSURE_OF_ALT = prove
 (`!top s:A->bool.
        top closure_of s = topspace top INTER s UNION top derived_set_of s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSURE_OF] THEN
  MP_TAC(ISPECL [`top:A topology`; `s:A->bool`]
        DERIVED_SET_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]);;

let DERIVED_SET_OF_SUBSET_CLOSURE_OF = prove
 (`!top s:A->bool. top derived_set_of s SUBSET top closure_of s`,
  REWRITE_TAC[CLOSURE_OF; SUBSET_INTER; DERIVED_SET_OF_SUBSET_TOPSPACE] THEN
  SIMP_TAC[SUBSET_UNION]);;

let CLOSURE_OF_SUBTOPOLOGY = prove
 (`!top u s:A->bool.
      (subtopology top u) closure_of s = u INTER (top closure_of (u INTER s))`,
  SIMP_TAC[CLOSURE_OF; TOPSPACE_SUBTOPOLOGY; DERIVED_SET_OF_SUBTOPOLOGY] THEN
  SET_TAC[]);;

let CLOSURE_OF_EMPTY = prove
 (`!top. top closure_of {}:A->bool = {}`,
  REWRITE_TAC[EXTENSION; IN_CLOSURE_OF; NOT_IN_EMPTY] THEN
  MESON_TAC[OPEN_IN_TOPSPACE]);;

let CLOSURE_OF_TOPSPACE = prove
 (`!top:A topology. top closure_of topspace top = topspace top`,
  REWRITE_TAC[EXTENSION; IN_CLOSURE_OF] THEN MESON_TAC[]);;

let CLOSURE_OF_UNIV = prove
 (`!top. top closure_of (:A) = topspace top`,
  REWRITE_TAC[closure_of] THEN SET_TAC[]);;

let CLOSURE_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top closure_of s SUBSET topspace top`,
  REWRITE_TAC[closure_of] THEN SET_TAC[]);;

let CLOSURE_OF_SUBSET_SUBTOPOLOGY = prove
 (`!top s t:A->bool. (subtopology top s) closure_of t SUBSET s`,
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; closure_of] THEN SET_TAC[]);;

let CLOSURE_OF_MONO = prove
 (`!top s t:A->bool.
        s SUBSET t ==> top closure_of s SUBSET top closure_of t`,
  REWRITE_TAC[closure_of] THEN SET_TAC[]);;

let CLOSURE_OF_SUBTOPOLOGY_SUBSET = prove
 (`!top s u:A->bool.
        (subtopology top u) closure_of s SUBSET (top closure_of s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET u ==> s INTER t SUBSET u`) THEN
  MATCH_MP_TAC CLOSURE_OF_MONO THEN REWRITE_TAC[INTER_SUBSET]);;

let CLOSURE_OF_SUBTOPOLOGY_MONO = prove
 (`!top s t u:A->bool.
        t SUBSET u
        ==> (subtopology top t) closure_of s SUBSET
            (subtopology top u) closure_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'`) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN
  ASM SET_TAC[]);;

let CLOSURE_OF_UNION = prove
 (`!top s t:A->bool.
       top closure_of (s UNION t) = top closure_of s UNION top closure_of t`,
  REWRITE_TAC[CLOSURE_OF; DERIVED_SET_OF_UNION] THEN SET_TAC[]);;

let CLOSURE_OF_UNIONS = prove
 (`!top (f:(A->bool)->bool).
        FINITE f
        ==> top closure_of (UNIONS f) =  UNIONS {top closure_of s | s IN f}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[UNIONS_0; NOT_IN_EMPTY; UNIONS_INSERT; CLOSURE_OF_EMPTY;
           CLOSURE_OF_UNION; SIMPLE_IMAGE; IMAGE_CLAUSES]);;

let CLOSURE_OF_SUBSET = prove
 (`!top s:A->bool. s SUBSET topspace top ==> s SUBSET top closure_of s`,
  REWRITE_TAC[CLOSURE_OF] THEN SET_TAC[]);;

let CLOSURE_OF_SUBSET_INTER = prove
 (`!top s:A->bool. topspace top INTER s SUBSET top closure_of s`,
  REWRITE_TAC[CLOSURE_OF] THEN SET_TAC[]);;

let CLOSURE_OF_SUBSET_EQ = prove
 (`!top s:A->bool.
     s SUBSET topspace top /\ top closure_of s SUBSET s <=> closed_in top s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(s:A->bool) SUBSET topspace top` THEN
  ASM_REWRITE_TAC[closed_in; SUBSET; closure_of; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_IN_SUBOPEN] THEN
  MP_TAC(ISPEC `top:A topology` OPEN_IN_SUBSET) THEN ASM SET_TAC[]);;

let CLOSURE_OF_EQ = prove
 (`!top s:A->bool. top closure_of s = s <=> closed_in top s`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(s:A->bool) SUBSET topspace top` THENL
   [ASM_MESON_TAC[SUBSET_ANTISYM_EQ; CLOSURE_OF_SUBSET; CLOSURE_OF_SUBSET_EQ];
    ASM_MESON_TAC[CLOSED_IN_SUBSET; CLOSURE_OF_SUBSET_TOPSPACE]]);;

let CLOSED_IN_CONTAINS_DERIVED_SET = prove
 (`!top s:A->bool.
        closed_in top s <=>
        s SUBSET topspace top /\
        !x. x IN (top derived_set_of s) ==> x IN s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ; CLOSURE_OF] THEN
  MP_TAC(ISPECL [`top:A topology`; `s:A->bool`] IN_DERIVED_SET_OF) THEN
  SET_TAC[]);;

let CLOSURE_OF_CLOSED_IN = prove
 (`!top s:A->bool. closed_in top s ==> top closure_of s = s`,
  REWRITE_TAC[CLOSURE_OF_EQ]);;

let CLOSED_IN_CLOSURE_OF = prove
 (`!top s:A->bool. closed_in top (top closure_of s)`,
   REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `top closure_of (s:A->bool) =
    topspace top DIFF
    UNIONS {t | open_in top t /\ DISJOINT s t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[closure_of; UNIONS_GSPEC] THEN SET_TAC[];
    MATCH_MP_TAC CLOSED_IN_DIFF THEN REWRITE_TAC[CLOSED_IN_TOPSPACE] THEN
    SIMP_TAC[OPEN_IN_UNIONS; FORALL_IN_GSPEC]]);;

let CLOSURE_OF_CLOSURE_OF = prove
 (`!top s:A->bool. top closure_of (top closure_of s) = top closure_of s`,
  REWRITE_TAC[CLOSURE_OF_EQ; CLOSED_IN_CLOSURE_OF]);;

let CLOSURE_OF_HULL = prove
 (`!top s:A->bool.
        s SUBSET topspace top ==> top closure_of s = (closed_in top) hull s`,
  REPEAT STRIP_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HULL_UNIQUE THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET; CLOSED_IN_CLOSURE_OF] THEN
  ASM_MESON_TAC[CLOSURE_OF_EQ; CLOSURE_OF_MONO]);;

let CLOSURE_OF_MINIMAL = prove
 (`!top s t:A->bool.
        s SUBSET t /\ closed_in top t ==> (top closure_of s) SUBSET t`,
  ASM_MESON_TAC[CLOSURE_OF_EQ; CLOSURE_OF_MONO]);;

let CLOSURE_OF_MINIMAL_EQ = prove
 (`!top s t:A->bool.
        s SUBSET topspace top /\ closed_in top t
        ==> ((top closure_of s) SUBSET t <=> s SUBSET t)`,
  MESON_TAC[SUBSET_TRANS; CLOSURE_OF_SUBSET; CLOSURE_OF_MINIMAL]);;

let CLOSURE_OF_UNIQUE = prove
 (`!top s t. s SUBSET t /\ closed_in top t /\
             (!t'. s SUBSET t' /\ closed_in top t' ==> t SUBSET t')
             ==> top closure_of s = t`,
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) CLOSURE_OF_HULL o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_SUBSET; SUBSET_TRANS];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC HULL_UNIQUE THEN ASM_REWRITE_TAC[]);;

let CLOSURE_OF_EQ_EMPTY_GEN = prove
 (`!top s:A->bool.
        top closure_of s = {} <=> DISJOINT (topspace top) s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[CLOSURE_OF_RESTRICT; DISJOINT] THEN
  EQ_TAC THEN SIMP_TAC[CLOSURE_OF_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE `t SUBSET s ==> s = {} ==> t = {}`) THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN REWRITE_TAC[INTER_SUBSET]);;

let CLOSURE_OF_EQ_EMPTY = prove
 (`!top s:A->bool.
        s SUBSET topspace top ==> (top closure_of s = {} <=> s = {})`,
  REWRITE_TAC[CLOSURE_OF_EQ_EMPTY_GEN] THEN SET_TAC[]);;

let OPEN_IN_INTER_CLOSURE_OF_SUBSET = prove
 (`!top s t:A->bool.
        open_in top s
        ==> s INTER top closure_of t SUBSET top closure_of (s INTER t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[closure_of] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
  X_GEN_TAC `x:A` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s INTER u:A->bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; IN_INTER] THEN MESON_TAC[]);;

let CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF = prove
 (`!top s t:A->bool.
        open_in top s
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
    REWRITE_TAC[CLOSED_IN_CLOSURE_OF] THEN
    ASM_SIMP_TAC[OPEN_IN_INTER_CLOSURE_OF_SUBSET];
    MATCH_MP_TAC CLOSURE_OF_MONO THEN
    MP_TAC(ISPECL [`top:A topology`; `topspace top INTER t:A->bool`]
        CLOSURE_OF_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET; GSYM CLOSURE_OF_RESTRICT] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    SET_TAC[]]);;

let OPEN_IN_INTER_CLOSURE_OF_EQ = prove
 (`!top s t:A->bool.
        open_in top s
        ==> s INTER top closure_of t = s INTER top closure_of (s INTER t)`,
  SIMP_TAC[GSYM SUBSET_ANTISYM_EQ; INTER_SUBSET; SUBSET_INTER] THEN
  SIMP_TAC[OPEN_IN_INTER_CLOSURE_OF_SUBSET] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> u INTER s SUBSET t`) THEN
  MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]);;

let OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY = prove
 (`!top s t:A->bool.
        open_in top s ==> (s INTER top closure_of t = {} <=> s INTER t = {})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SPEC `t:A->bool` o
      MATCH_MP OPEN_IN_INTER_CLOSURE_OF_EQ) THEN
  EQ_TAC THEN SIMP_TAC[CLOSURE_OF_EMPTY; INTER_EMPTY] THEN
  MATCH_MP_TAC(SET_RULE
   `s INTER t SUBSET c ==> s INTER c = {} ==> s INTER t = {}`) THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[]);;

let CLOSURE_OF_OPEN_IN_INTER_SUPERSET = prove
 (`!top s t:A->bool.
        open_in top s /\ s SUBSET top closure_of t
        ==> top closure_of (s INTER t) = top closure_of s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o SPEC `t:A->bool` o
    MATCH_MP CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF) THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

let CLOSURE_OF_OPEN_IN_SUBTOPOLOGY_INTER_CLOSURE_OF = prove
 (`!top s t u:A->bool.
        open_in (subtopology top u) s /\ t SUBSET u
        ==> top closure_of (s INTER top closure_of t) =
            top closure_of (s INTER t)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_SUBTOPOLOGY]) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A->bool`
     (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:A->bool` o
      MATCH_MP CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF) THEN
    ASM_SIMP_TAC[SET_RULE
     `t SUBSET u ==> (v INTER u) INTER t = v INTER t`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[];
    MATCH_MP_TAC CLOSURE_OF_MONO THEN
    MP_TAC(ISPECL [`top:A topology`; `topspace top INTER t:A->bool`]
        CLOSURE_OF_SUBSET) THEN
    REWRITE_TAC[GSYM CLOSURE_OF_RESTRICT; INTER_SUBSET] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN SET_TAC[]]);;

let CLOSURE_OF_SUBTOPOLOGY_OPEN = prove
 (`!top u s:A->bool.
        open_in top u \/ s SUBSET u
        ==> (subtopology top u) closure_of s = u INTER top closure_of s`,
  REWRITE_TAC[SET_RULE `s SUBSET u <=> u INTER s = s`] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY] THEN
  ASM_MESON_TAC[OPEN_IN_INTER_CLOSURE_OF_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Interior with respect to a topological space.                             *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("interior_of",(21,"right"));;

let interior_of = new_definition
 `top interior_of s = {x | ?t. open_in top t /\ x IN t /\ t SUBSET s}`;;

let INTERIOR_OF_RESTRICT = prove
 (`!top s:A->bool.
        top interior_of s = top interior_of (topspace top INTER s)`,
  REWRITE_TAC[interior_of; EXTENSION; IN_ELIM_THM; SUBSET_INTER] THEN
  MESON_TAC[OPEN_IN_SUBSET]);;

let INTERIOR_OF_EQ = prove
 (`!top s:A->bool. (top interior_of s = s) <=> open_in top s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; interior_of; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC RAND_CONV [OPEN_IN_SUBOPEN] THEN MESON_TAC[SUBSET]);;

let INTERIOR_OF_OPEN_IN = prove
 (`!top s:a->bool. open_in top s ==> top interior_of s = s`,
  MESON_TAC[INTERIOR_OF_EQ]);;

let INTERIOR_OF_EMPTY = prove
 (`!top:A topology. top interior_of {} = {}`,
  REWRITE_TAC[INTERIOR_OF_EQ; OPEN_IN_EMPTY]);;

let INTERIOR_OF_TOPSPACE = prove
 (`!top:A topology. top interior_of (topspace top) = topspace top`,
  REWRITE_TAC[INTERIOR_OF_EQ; OPEN_IN_TOPSPACE]);;

let OPEN_IN_INTERIOR_OF = prove
 (`!top s:A->bool. open_in top (top interior_of s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of] THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let INTERIOR_OF_INTERIOR_OF = prove
 (`!top s:A->bool. top interior_of top interior_of s = top interior_of s`,
  REWRITE_TAC[INTERIOR_OF_EQ; OPEN_IN_INTERIOR_OF]);;

let INTERIOR_OF_SUBSET = prove
 (`!top s:A->bool. top interior_of s SUBSET s`,
  REWRITE_TAC[interior_of] THEN SET_TAC[]);;

let INTERIOR_OF_SUBSET_CLOSURE_OF = prove
 (`!top s:A->bool. top interior_of s SUBSET top closure_of s`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[INTERIOR_OF_RESTRICT; CLOSURE_OF_RESTRICT] THEN
  TRANS_TAC SUBSET_TRANS `topspace top INTER s:A->bool` THEN
  SIMP_TAC[INTERIOR_OF_SUBSET; CLOSURE_OF_SUBSET; INTER_SUBSET]);;

let SUBSET_INTERIOR_OF_EQ = prove
 (`!top s:A->bool. s SUBSET top interior_of s <=> open_in top s`,
  SIMP_TAC[GSYM INTERIOR_OF_EQ; GSYM SUBSET_ANTISYM_EQ; INTERIOR_OF_SUBSET]);;

let INTERIOR_OF_MONO = prove
 (`!top s t:A->bool.
        s SUBSET t ==> top interior_of s SUBSET top interior_of t`,
   REWRITE_TAC[interior_of] THEN SET_TAC[]);;

let INTERIOR_OF_MAXIMAL = prove
 (`!top s t:A->bool.
        t SUBSET s /\ open_in top t ==> t SUBSET top interior_of s`,
  REWRITE_TAC[interior_of] THEN SET_TAC[]);;

let INTERIOR_OF_MAXIMAL_EQ = prove
 (`!top s t:A->bool.
        open_in top t ==> (t SUBSET top interior_of s <=> t SUBSET s)`,
  MESON_TAC[INTERIOR_OF_MAXIMAL; SUBSET_TRANS; INTERIOR_OF_SUBSET]);;

let INTERIOR_OF_UNIQUE = prove
 (`!top s t:A->bool.
        t SUBSET s /\ open_in top t /\
        (!t'. t' SUBSET s /\ open_in top t' ==> t' SUBSET t)
        ==> top interior_of s = t`,
  MESON_TAC[SUBSET_ANTISYM; INTERIOR_OF_MAXIMAL; INTERIOR_OF_SUBSET;
            OPEN_IN_INTERIOR_OF]);;

let INTERIOR_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top interior_of s SUBSET topspace top`,
  REWRITE_TAC[SUBSET; interior_of; IN_ELIM_THM] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_SUBSET]);;

let INTERIOR_OF_SUBSET_SUBTOPOLOGY = prove
 (`!top s t:A->bool. (subtopology top s) interior_of t SUBSET s`,
  REPEAT STRIP_TAC THEN MP_TAC
   (ISPEC `subtopology top (s:A->bool)` INTERIOR_OF_SUBSET_TOPSPACE) THEN
  SIMP_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER]);;

let INTERIOR_OF_INTER = prove
 (`!top s t:A->bool.
      top interior_of (s INTER t) = top interior_of s INTER top interior_of t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET_INTER] THEN
  SIMP_TAC[INTERIOR_OF_MONO; INTER_SUBSET] THEN
  SIMP_TAC[INTERIOR_OF_MAXIMAL_EQ; OPEN_IN_INTERIOR_OF; OPEN_IN_INTER] THEN
  MATCH_MP_TAC(SET_RULE
      `s SUBSET s' /\ t SUBSET t' ==> s INTER t SUBSET s' INTER t'`) THEN
  REWRITE_TAC[INTERIOR_OF_SUBSET]);;

let INTERIOR_OF_INTERS_SUBSET = prove
 (`!top f:(A->bool)->bool.
        top interior_of (INTERS f) SUBSET
        INTERS {top interior_of s | s IN f}`,
  REWRITE_TAC[SUBSET; interior_of; INTERS_GSPEC] THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INTERS] THEN MESON_TAC[]);;

let UNION_INTERIOR_OF_SUBSET = prove
 (`!top s t:A->bool.
        top interior_of s UNION top interior_of t
        SUBSET top interior_of (s UNION t)`,
  SIMP_TAC[UNION_SUBSET; INTERIOR_OF_MONO; SUBSET_UNION]);;

let INTERIOR_OF_EQ_EMPTY = prove
 (`!top s:A->bool.
                top interior_of s = {} <=>
                !t. open_in top t /\ t SUBSET s ==> t = {}`,
  MESON_TAC[INTERIOR_OF_MAXIMAL_EQ; SUBSET_EMPTY;
            OPEN_IN_INTERIOR_OF; INTERIOR_OF_SUBSET]);;

let INTERIOR_OF_EQ_EMPTY_ALT = prove
 (`!top s:A->bool.
        top interior_of s = {} <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(t DIFF s = {})`,
  GEN_TAC THEN REWRITE_TAC[INTERIOR_OF_EQ_EMPTY] THEN SET_TAC[]);;

let INTERIOR_OF_UNIONS_OPEN_IN_SUBSETS = prove
 (`!top s:A->bool.
        UNIONS {t | open_in top t /\ t SUBSET s} = top interior_of s`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC INTERIOR_OF_UNIQUE THEN
  SIMP_TAC[OPEN_IN_UNIONS; IN_ELIM_THM] THEN SET_TAC[]);;

let INTERIOR_OF_COMPLEMENT = prove
 (`!top s:A->bool.
        top interior_of (topspace top DIFF s) =
        topspace top DIFF top closure_of s`,
  REWRITE_TAC[interior_of; closure_of] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_SUBSET]);;

let INTERIOR_OF_CLOSURE_OF = prove
 (`!top s:A->bool.
        top interior_of s =
        topspace top DIFF top closure_of (topspace top DIFF s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[GSYM INTERIOR_OF_COMPLEMENT] THEN
  GEN_REWRITE_TAC LAND_CONV [INTERIOR_OF_RESTRICT] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let CLOSURE_OF_INTERIOR_OF = prove
 (`!top s:A->bool.
        top closure_of s =
        topspace top DIFF top interior_of (topspace top DIFF s)`,
  REWRITE_TAC[INTERIOR_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE `s = t DIFF (t DIFF s) <=> s SUBSET t`] THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]);;

let CLOSURE_OF_COMPLEMENT = prove
 (`!top s:A->bool.
        top closure_of (topspace top DIFF s) =
        topspace top DIFF top interior_of s`,
  REWRITE_TAC[interior_of; closure_of] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM; SUBSET] THEN
  MESON_TAC[REWRITE_RULE[SUBSET] OPEN_IN_SUBSET]);;

let INTERIOR_OF_EQ_EMPTY_COMPLEMENT = prove
 (`!top s:A->bool.
        top interior_of s = {} <=>
        top closure_of (topspace top DIFF s) = topspace top`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`top:A topology`; `s:A->bool`] INTERIOR_OF_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[CLOSURE_OF_COMPLEMENT] THEN SET_TAC[]);;

let CLOSURE_OF_EQ_UNIV = prove
 (`!top s:A->bool.
     top closure_of s = topspace top <=>
     top interior_of (topspace top DIFF s) = {}`,
  REPEAT GEN_TAC THEN MP_TAC(ISPECL
   [`top:A topology`; `s:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[INTERIOR_OF_COMPLEMENT] THEN SET_TAC[]);;

let INTERIOR_OF_SUBTOPOLOGY_SUBSET = prove
 (`!top s u:A->bool.
        u INTER top interior_of s SUBSET (subtopology top u) interior_of s`,
  REWRITE_TAC[SUBSET; IN_INTER; interior_of;
              OPEN_IN_SUBTOPOLOGY; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[LEFT_AND_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  GEN_REWRITE_TAC RAND_CONV [SWAP_EXISTS_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[TAUT `(p /\ q) /\ r <=> q /\ p /\ r`] THEN
  REWRITE_TAC[UNWIND_THM2] THEN ASM SET_TAC[]);;

let INTERIOR_OF_SUBTOPOLOGY_SUBSETS = prove
 (`!top s t u:A->bool.
        t SUBSET u
        ==> t INTER (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `t SUBSET u ==> t = u INTER t`)) THEN
  REWRITE_TAC[GSYM SUBTOPOLOGY_SUBTOPOLOGY] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP (SET_RULE
   `t SUBSET u ==> u INTER t = t`)) THEN
  REWRITE_TAC[INTERIOR_OF_SUBTOPOLOGY_SUBSET]);;

let INTERIOR_OF_SUBTOPOLOGY_MONO = prove
 (`!top s t u:A->bool.
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top u) interior_of s SUBSET
            (subtopology top t) interior_of s`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(SET_RULE
    `i SUBSET s /\ t INTER i SUBSET i'
     ==> s SUBSET t ==> i SUBSET i'`) THEN
  ASM_SIMP_TAC[INTERIOR_OF_SUBSET; INTERIOR_OF_SUBTOPOLOGY_SUBSETS]);;

let INTERIOR_OF_SUBTOPOLOGY_OPEN = prove
 (`!top u s:A->bool.
        open_in top u
        ==> (subtopology top u) interior_of s = u INTER top interior_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERIOR_OF_CLOSURE_OF] THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY_OPEN] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[SET_RULE `s INTER t DIFF u = t INTER (s DIFF u)`] THEN
  ASM_SIMP_TAC[GSYM OPEN_IN_INTER_CLOSURE_OF_EQ] THEN SET_TAC[]);;

let DENSE_INTERSECTS_OPEN = prove
 (`!top s:A->bool.
        top closure_of s = topspace top <=>
        !t. open_in top t /\ ~(t = {}) ==> ~(s INTER t = {})`,
  REWRITE_TAC[CLOSURE_OF_INTERIOR_OF] THEN
  SIMP_TAC[INTERIOR_OF_SUBSET_TOPSPACE;
   SET_RULE `s SUBSET u ==> (u DIFF s = u <=> s = {})`] THEN
  REWRITE_TAC[INTERIOR_OF_EQ_EMPTY_ALT] THEN
  SIMP_TAC[OPEN_IN_SUBSET; SET_RULE
   `t SUBSET u ==> (~(t DIFF (u DIFF s) = {}) <=> ~(s INTER t = {}))`]);;

let INTERIOR_OF_CLOSED_IN_UNION_EMPTY_INTERIOR_OF = prove
 (`!top s t:A->bool.
        closed_in top s /\ top interior_of t = {}
        ==> top interior_of (s UNION t) = top interior_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INTERIOR_OF_CLOSURE_OF] THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`] THEN
  W(MP_TAC o PART_MATCH (rand o rand) CLOSURE_OF_OPEN_IN_INTER_CLOSURE_OF o
    lhand o snd) THEN
  ASM_SIMP_TAC[CLOSURE_OF_COMPLEMENT; OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[GSYM CLOSURE_OF_COMPLEMENT] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let INTERIOR_OF_UNION_EQ_EMPTY = prove
 (`!top s t:A->bool.
        closed_in top s \/ closed_in top t
        ==> (top interior_of (s UNION t) = {} <=>
             top interior_of s = {} /\ top interior_of t = {})`,
  GEN_TAC THEN MATCH_MP_TAC(MESON[]
   `(!x y. R x y ==> R y x) /\ (!x y. P x ==> R x y)
    ==> (!x y. P x \/ P y ==> R x y)`) THEN
  CONJ_TAC THENL [REWRITE_TAC[UNION_COMM] THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT
   `(p ==> r) /\ (r ==> (p <=> q)) ==> (p <=> q /\ r)`) THEN
  ASM_SIMP_TAC[INTERIOR_OF_CLOSED_IN_UNION_EMPTY_INTERIOR_OF] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> t = {} ==> s = {}`) THEN
  SIMP_TAC[INTERIOR_OF_MONO; SUBSET_UNION]);;

(* ------------------------------------------------------------------------- *)
(* Frontier with respect to topological space.                               *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("frontier_of",(21,"right"));;

let frontier_of = new_definition
 `top frontier_of s =  top closure_of s DIFF top interior_of s`;;

let FRONTIER_OF_CLOSURES = prove
 (`!top s. top frontier_of s =
           top closure_of s INTER top closure_of (topspace top DIFF s)`,
  REPEAT GEN_TAC THEN CONV_TAC SYM_CONV THEN
  REWRITE_TAC[frontier_of; CLOSURE_OF_COMPLEMENT] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET u ==> s INTER (u DIFF t) = s DIFF t`) THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE]);;

let FRONTIER_OF_RESTRICT = prove
 (`!top s:A->bool. top frontier_of s = top frontier_of (topspace top INTER s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  BINOP_TAC THEN GEN_REWRITE_TAC LAND_CONV [CLOSURE_OF_RESTRICT] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let CLOSED_IN_FRONTIER_OF = prove
 (`!top s:A->bool. closed_in top (top frontier_of s)`,
  SIMP_TAC[FRONTIER_OF_CLOSURES; CLOSED_IN_INTER; CLOSED_IN_CLOSURE_OF]);;

let FRONTIER_OF_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. top frontier_of s SUBSET topspace top`,
  SIMP_TAC[CLOSED_IN_SUBSET; CLOSED_IN_FRONTIER_OF]);;

let FRONTIER_OF_SUBSET_SUBTOPOLOGY = prove
 (`!top s t:A->bool. (subtopology top s) frontier_of t SUBSET s`,
  MESON_TAC[TOPSPACE_SUBTOPOLOGY; FRONTIER_OF_SUBSET_TOPSPACE; SUBSET_INTER]);;

let FRONTIER_OF_SUBTOPOLOGY_SUBSET = prove
 (`!top s u:A->bool.
        u INTER (subtopology top u) frontier_of s SUBSET (top frontier_of s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[frontier_of] THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET s' /\ u INTER t' SUBSET t
    ==> u INTER (s DIFF t) SUBSET s' DIFF t'`) THEN
  REWRITE_TAC[CLOSURE_OF_SUBTOPOLOGY_SUBSET; INTERIOR_OF_SUBTOPOLOGY_SUBSET]);;

let FRONTIER_OF_SUBTOPOLOGY_MONO = prove
 (`!top s t u:A->bool.
        s SUBSET t /\ t SUBSET u
        ==> (subtopology top t) frontier_of s SUBSET
            (subtopology top u) frontier_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of] THEN MATCH_MP_TAC(SET_RULE
   `s SUBSET s' /\ t' SUBSET t ==> s DIFF t SUBSET s' DIFF t'`) THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBTOPOLOGY_MONO; INTERIOR_OF_SUBTOPOLOGY_MONO]);;

let CLOPEN_IN_EQ_FRONTIER_OF = prove
 (`!top s:A->bool.
        closed_in top s /\ open_in top s <=>
        s SUBSET topspace top /\ top frontier_of s = {}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES; OPEN_IN_CLOSED_IN_EQ] THEN
  ASM_CASES_TAC `(s:A->bool) SUBSET topspace top` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [SIMP_TAC[CLOSURE_OF_CLOSED_IN] THEN SET_TAC[]; DISCH_TAC] THEN
  ASM_REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ; SUBSET_DIFF] THEN
  MATCH_MP_TAC(SET_RULE
   `c INTER c' = {} /\
    s SUBSET c /\ (u DIFF s) SUBSET c' /\ c SUBSET u /\ c' SUBSET u
        ==> c SUBSET s /\ c' SUBSET (u DIFF s)`) THEN
  ASM_SIMP_TAC[CLOSURE_OF_SUBSET; SUBSET_DIFF; CLOSURE_OF_SUBSET_TOPSPACE]);;

let FRONTIER_OF_EQ_EMPTY = prove
 (`!top s:A->bool.
        s SUBSET topspace top
        ==> (top frontier_of s = {} <=> closed_in top s /\ open_in top s)`,
  SIMP_TAC[CLOPEN_IN_EQ_FRONTIER_OF]);;

let FRONTIER_OF_OPEN_IN = prove
 (`!top s:A->bool.
        open_in top s ==> top frontier_of s = top closure_of s DIFF s`,
  SIMP_TAC[frontier_of; INTERIOR_OF_OPEN_IN]);;

let FRONTIER_OF_OPEN_IN_STRADDLE_INTER = prove
 (`!top s u:A->bool.
        open_in top  u /\ ~(u INTER top frontier_of s = {})
        ==> ~(u INTER s = {}) /\ ~(u DIFF s = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
   `~(s INTER t INTER u = {})
    ==> ~(s INTER t = {}) /\ ~(s INTER u = {})`)) THEN
  MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN
  W(MP_TAC o PART_MATCH (lhand o rand) OPEN_IN_INTER_CLOSURE_OF_EQ_EMPTY o
     rand o lhand o snd) THEN
  ASM SET_TAC[]);;

let FRONTIER_OF_SUBSET_CLOSED_IN = prove
 (`!top s:A->bool. closed_in top s ==> (top frontier_of s) SUBSET s`,
  REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ; frontier_of] THEN SET_TAC[]);;

let FRONTIER_OF_EMPTY = prove
 (`!top. top frontier_of {} = {}`,
  REWRITE_TAC[FRONTIER_OF_CLOSURES; CLOSURE_OF_EMPTY; INTER_EMPTY]);;

let FRONTIER_OF_TOPSPACE = prove
 (`!top:A topology. top frontier_of topspace top = {}`,
  SIMP_TAC[FRONTIER_OF_EQ_EMPTY; SUBSET_REFL] THEN
  REWRITE_TAC[OPEN_IN_TOPSPACE; CLOSED_IN_TOPSPACE]);;

let FRONTIER_OF_SUBSET_EQ = prove
 (`!top s:A->bool.
        s SUBSET topspace top
        ==> ((top frontier_of s) SUBSET s <=> closed_in top s)`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN SIMP_TAC[FRONTIER_OF_SUBSET_CLOSED_IN] THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  ASM_REWRITE_TAC[GSYM CLOSURE_OF_SUBSET_EQ] THEN
  ONCE_REWRITE_TAC[SET_RULE `s INTER t = s DIFF (s DIFF t)`]  THEN
  DISCH_THEN(MATCH_MP_TAC o MATCH_MP (SET_RULE
   `s DIFF t SUBSET u ==> t SUBSET u ==> s SUBSET u`)) THEN
  MATCH_MP_TAC(SET_RULE
   `!u. u DIFF s SUBSET d /\ c SUBSET u ==> c DIFF d SUBSET s`) THEN
  EXISTS_TAC `topspace top:A->bool` THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE] THEN
  MATCH_MP_TAC CLOSURE_OF_SUBSET THEN SET_TAC[]);;

let FRONTIER_OF_COMPLEMENT = prove
 (`!top s:A->bool. top frontier_of (topspace top DIFF s) = top frontier_of s`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[FRONTIER_OF_RESTRICT] THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  GEN_REWRITE_TAC RAND_CONV [INTER_COMM] THEN
  BINOP_TAC THEN AP_TERM_TAC THEN SET_TAC[]);;

let FRONTIER_OF_DISJOINT_EQ = prove
 (`!top s. s SUBSET topspace top
        ==> ((top frontier_of s) INTER s = {} <=> open_in top s)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[OPEN_IN_CLOSED_IN] THEN
  ASM_SIMP_TAC[GSYM FRONTIER_OF_SUBSET_EQ; SUBSET_DIFF] THEN
  REWRITE_TAC[FRONTIER_OF_COMPLEMENT] THEN
  MATCH_MP_TAC(SET_RULE
   `f SUBSET u ==> (f INTER s = {} <=> f SUBSET u DIFF s)`) THEN
  REWRITE_TAC[FRONTIER_OF_SUBSET_TOPSPACE]);;

let FRONTIER_OF_DISJOINT_EQ_ALT = prove
 (`!top s:A->bool.
        s SUBSET (topspace top DIFF top frontier_of s) <=>
        open_in top s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `(s:A->bool) SUBSET topspace top` THENL
   [ASM_SIMP_TAC[GSYM FRONTIER_OF_DISJOINT_EQ] THEN ASM SET_TAC[];
    EQ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[OPEN_IN_SUBSET]]]);;

let FRONTIER_OF_INTER = prove
 (`!top s t:A->bool.
        top frontier_of(s INTER t) =
        top closure_of (s INTER t) INTER
        (top frontier_of s UNION top frontier_of t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[FRONTIER_OF_CLOSURES] THEN
  SIMP_TAC[CLOSURE_OF_MONO; INTER_SUBSET; GSYM CLOSURE_OF_UNION; SET_RULE
    `u SUBSET s /\ u SUBSET t
     ==> u INTER (s INTER x UNION t INTER y) = u INTER (x UNION y)`] THEN
  REPLICATE_TAC 2 AP_TERM_TAC THEN SET_TAC[]);;

let FRONTIER_OF_INTER_SUBSET = prove
 (`!top s t. top frontier_of(s INTER t) SUBSET
             top frontier_of(s) UNION top frontier_of(t)`,
  REWRITE_TAC[FRONTIER_OF_INTER] THEN SET_TAC[]);;

let FRONTIER_OF_INTER_CLOSED_IN = prove
 (`!top s t:A->bool.
        closed_in top s /\ closed_in top t
        ==> top frontier_of(s INTER t) =
            top frontier_of s INTER t UNION s INTER top frontier_of t`,
  SIMP_TAC[FRONTIER_OF_INTER; CLOSED_IN_INTER; CLOSURE_OF_CLOSED_IN] THEN
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_SUBSET_CLOSED_IN)) THEN
  SET_TAC[]);;

let FRONTIER_OF_UNION_SUBSET = prove
 (`!top s t:A->bool.
      top frontier_of(s UNION t) SUBSET
      top frontier_of s UNION top frontier_of t`,
  ONCE_REWRITE_TAC[GSYM FRONTIER_OF_COMPLEMENT] THEN
  REWRITE_TAC[SET_RULE `u DIFF (s UNION t) = (u DIFF s) INTER (u DIFF t)`] THEN
  REWRITE_TAC[FRONTIER_OF_INTER_SUBSET]);;

let FRONTIER_OF_UNIONS_SUBSET = prove
 (`!top f:(A->bool)->bool.
        FINITE f
        ==> top frontier_of (UNIONS f) SUBSET
            UNIONS {top frontier_of t | t IN f}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  SIMP_TAC[SIMPLE_IMAGE; IMAGE_UNIONS; IMAGE_CLAUSES; UNIONS_0;
           UNIONS_INSERT; FRONTIER_OF_EMPTY; SUBSET_REFL] THEN
  REPEAT STRIP_TAC THEN
  W(MP_TAC o PART_MATCH lhand FRONTIER_OF_UNION_SUBSET o lhand o snd) THEN
  ASM SET_TAC[]);;

let FRONTIER_OF_FRONTIER_OF_SUBSET = prove
 (`!top s:A->bool.
    top frontier_of (top frontier_of s) SUBSET top frontier_of s`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
  REWRITE_TAC[CLOSED_IN_FRONTIER_OF]);;

let FRONTIER_OF_SUBTOPOLOGY_OPEN = prove
 (`!top u s:A->bool.
        open_in top u
        ==> (subtopology top u) frontier_of s = u INTER top frontier_of s`,
  SIMP_TAC[frontier_of; CLOSURE_OF_SUBTOPOLOGY_OPEN;
           INTERIOR_OF_SUBTOPOLOGY_OPEN] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Iteration of interior and closure.                                        *)
(* ------------------------------------------------------------------------- *)

let INTERIOR_OF_CLOSURE_OF_IDEMP = prove
 (`!top s:A->bool.
        top interior_of top closure_of top interior_of top closure_of s =
        top interior_of top closure_of s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERIOR_OF_UNIQUE THEN
  REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN
  SIMP_TAC[CLOSURE_OF_SUBSET; INTERIOR_OF_SUBSET_TOPSPACE] THEN
  SIMP_TAC[INTERIOR_OF_MAXIMAL_EQ] THEN
  X_GEN_TAC `t:A->bool` THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ_ALT] SUBSET_TRANS) THEN
  MATCH_MP_TAC CLOSURE_OF_MINIMAL THEN
  REWRITE_TAC[CLOSED_IN_CLOSURE_OF; INTERIOR_OF_SUBSET]);;

let CLOSURE_OF_INTERIOR_OF_IDEMP = prove
 (`!top s:A->bool.
        top closure_of top interior_of top closure_of top interior_of s =
        top closure_of top interior_of s`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `topspace top DIFF s:A->bool`]
        INTERIOR_OF_CLOSURE_OF_IDEMP) THEN
  REWRITE_TAC[CLOSURE_OF_COMPLEMENT; INTERIOR_OF_COMPLEMENT] THEN
  MATCH_MP_TAC(SET_RULE
   `s SUBSET u /\ t SUBSET u ==> u DIFF s = u DIFF t ==> s = t`) THEN
  REWRITE_TAC[CLOSURE_OF_SUBSET_TOPSPACE; INTERIOR_OF_SUBSET_TOPSPACE]);;

let INTERIOR_OF_FRONTIER_OF = prove
 (`!top s:A->bool.
        top interior_of (top frontier_of s) =
        top interior_of (top closure_of s) DIFF
        top closure_of (top interior_of s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES; INTERIOR_OF_INTER] THEN
  REWRITE_TAC[CLOSURE_OF_COMPLEMENT; INTERIOR_OF_COMPLEMENT] THEN
  MP_TAC(ISPECL [`top:A topology`; `top closure_of s:A->bool`]
        INTERIOR_OF_SUBSET_TOPSPACE) THEN
  SET_TAC[]);;

let THIN_FRONTIER_OF_SUBSET = prove
 (`!top s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top interior_of (top closure_of s) SUBSET
        top closure_of (top interior_of s)`,
  REWRITE_TAC[INTERIOR_OF_FRONTIER_OF] THEN SET_TAC[]);;

let THIN_FRONTIER_OF_CIC = prove
 (`!top s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top closure_of (top interior_of (top closure_of s)) =
        top closure_of (top interior_of s)`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC RAND_CONV [GSYM SUBSET_ANTISYM_EQ] THEN
  REWRITE_TAC[THIN_FRONTIER_OF_SUBSET] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) /\ r==> (p <=> q /\ r)`) THEN CONJ_TAC THENL
   [SIMP_TAC[CLOSURE_OF_MINIMAL_EQ; CLOSED_IN_CLOSURE_OF;
             INTERIOR_OF_SUBSET_TOPSPACE];
    GEN_REWRITE_TAC LAND_CONV [GSYM CLOSURE_OF_INTERIOR_OF_IDEMP] THEN
    SIMP_TAC[CLOSURE_OF_MONO; INTERIOR_OF_MONO; INTERIOR_OF_SUBSET]]);;

let THIN_FRONTIER_OF_ICI = prove
 (`!s:A->bool.
        top interior_of (top frontier_of s) = {} <=>
        top interior_of (top closure_of (top interior_of s)) =
        top interior_of (top closure_of  s)`,
  GEN_TAC THEN REWRITE_TAC[THIN_FRONTIER_OF_CIC] THEN
  MESON_TAC[INTERIOR_OF_CLOSURE_OF_IDEMP; CLOSURE_OF_INTERIOR_OF_IDEMP]);;

let INTERIOR_OF_FRONTIER_OF_EMPTY = prove
 (`!top s:A->bool.
        open_in top s \/ closed_in top s
        ==> top interior_of (top frontier_of s) = {}`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[THIN_FRONTIER_OF_ICI]; REWRITE_TAC[THIN_FRONTIER_OF_CIC]] THEN
  ASM_SIMP_TAC[INTERIOR_OF_OPEN_IN; CLOSURE_OF_CLOSED_IN]);;

let FRONTIER_OF_FRONTIER_OF = prove
 (`!top s:A->bool.
        open_in top s \/ closed_in top s
        ==> top frontier_of (top frontier_of s) = top frontier_of s`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o LAND_CONV) [frontier_of] THEN
  SIMP_TAC[INTERIOR_OF_FRONTIER_OF_EMPTY; CLOSURE_OF_CLOSED_IN;
          CLOSED_IN_FRONTIER_OF; DIFF_EMPTY]);;

let FRONTIER_OF_FRONTIER_OF_FRONTIER_OF = prove
 (`!top s:A->bool.
        top frontier_of top frontier_of top frontier_of s =
        top frontier_of top frontier_of s`,
  SIMP_TAC[FRONTIER_OF_FRONTIER_OF; CLOSED_IN_FRONTIER_OF]);;

(* ------------------------------------------------------------------------- *)
(* A variant of nets (slightly non-standard but good for our purposes).      *)
(* ------------------------------------------------------------------------- *)

let net_tybij = new_type_definition "net" ("mk_net","netord")
 (prove
   (`?g:A->A->bool. !x y. (!z. g z x ==> g z y) \/ (!z. g z y ==> g z x)`,
    EXISTS_TAC `\x:A y:A. F` THEN REWRITE_TAC[]));;

let NET = prove
 (`!n x y. (!z. netord n z x ==> netord n z y) \/
           (!z. netord n z y ==> netord n z x)`,
   REWRITE_TAC[net_tybij; ETA_AX]);;

let OLDNET = prove
 (`!n x y. netord n x x /\ netord n y y
           ==> ?z. netord n z z /\
                   !w. netord n w z ==> netord n w x /\ netord n w y`,
  MESON_TAC[NET]);;

let NET_DILEMMA = prove
 (`!net. (?a. (?x. netord net x a) /\ (!x. netord net x a ==> P x)) /\
         (?b. (?x. netord net x b) /\ (!x. netord net x b ==> Q x))
         ==> ?c. (?x. netord net x c) /\ (!x. netord net x c ==> P x /\ Q x)`,
  MESON_TAC[NET]);;

(* ------------------------------------------------------------------------- *)
(* Sequential net and the "within" modifier for nets.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("within",(14,"right"));;

let sequentially = new_definition
  `sequentially = mk_net(\m:num n. m >= n)`;;

let within = new_definition
  `net within s = mk_net(\x y. netord net x y /\ x IN s)`;;

let NET_PROVE_TAC[def] =
  REWRITE_TAC[GSYM FUN_EQ_THM; def] THEN
  REWRITE_TAC[ETA_AX] THEN
  ASM_SIMP_TAC[GSYM(CONJUNCT2 net_tybij)];;

let SEQUENTIALLY = prove
 (`!m n. netord sequentially m n <=> m >= n`,
  NET_PROVE_TAC[sequentially] THEN REWRITE_TAC[GE; LE_REFL] THEN
  MESON_TAC[LE_CASES; LE_REFL; LE_TRANS]);;

let WITHIN = prove
 (`!n s x y. netord(n within s) x y <=> netord n x y /\ x IN s`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[within; GSYM FUN_EQ_THM] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 net_tybij); ETA_AX] THEN
  MESON_TAC[NET]);;

let NET_WITHIN_UNIV = prove
 (`!net. net within UNIV = net`,
  REWRITE_TAC[within; IN_UNIV; ETA_AX; net_tybij]);;

let WITHIN_WITHIN = prove
 (`!net s t. (net within s) within t = net within (s INTER t)`,
  ONCE_REWRITE_TAC[within] THEN
  REWRITE_TAC[WITHIN; IN_INTER; GSYM CONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Identify trivial limits, where we can't approach arbitrarily closely.     *)
(* ------------------------------------------------------------------------- *)

let trivial_limit = new_definition
  `trivial_limit net <=>
     (!a:A b. a = b) \/
     ?a:A b. ~(a = b) /\ !x. ~(netord(net) x a) /\ ~(netord(net) x b)`;;

let TRIVIAL_LIMIT_SEQUENTIALLY = prove
 (`~(trivial_limit sequentially)`,
  REWRITE_TAC[trivial_limit; SEQUENTIALLY] THEN
  MESON_TAC[GE_REFL; NOT_SUC]);;

let NONTRIVIAL_LIMIT_WITHIN = prove
 (`!net s. trivial_limit net ==> trivial_limit(net within s)`,
  REWRITE_TAC[trivial_limit; WITHIN] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Some property holds "sufficiently close" to the limit point.              *)
(* ------------------------------------------------------------------------- *)

let eventually = new_definition
 `eventually p net <=>
        trivial_limit net \/
        ?y. (?x. netord net x y) /\ (!x. netord net x y ==> p x)`;;

let EVENTUALLY_HAPPENS = prove
 (`!net p. eventually p net ==> trivial_limit net \/ ?x. p x`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_SEQUENTIALLY = prove
 (`!p. eventually p sequentially <=> ?N. !n. N <= n ==> p n`,
  REWRITE_TAC[eventually; SEQUENTIALLY; GE; LE_REFL;
    TRIVIAL_LIMIT_SEQUENTIALLY] THEN  MESON_TAC[LE_REFL]);;

let ALWAYS_EVENTUALLY = prove
 (`(!x. p x) ==> eventually p net`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[eventually; trivial_limit] THEN
  MESON_TAC[]);;

let EVENTUALLY_AND = prove
 (`!net:(A net) p q.
        eventually (\x. p x /\ q x) net <=>
        eventually p net /\ eventually q net`,
  REPEAT GEN_TAC THEN REWRITE_TAC[eventually] THEN
  ASM_CASES_TAC `trivial_limit(net:(A net))` THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THEN SIMP_TAC[NET_DILEMMA] THEN MESON_TAC[]);;

let EVENTUALLY_MONO = prove
 (`!net:(A net) p q.
        (!x. p x ==> q x) /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_MP = prove
 (`!net:(A net) p q.
        eventually (\x. p x ==> q x) net /\ eventually p net
        ==> eventually q net`,
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_FALSE = prove
 (`!net. eventually (\x. F) net <=> trivial_limit net`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_TRUE = prove
 (`!net. eventually (\x. T) net <=> T`,
  REWRITE_TAC[eventually; trivial_limit] THEN MESON_TAC[]);;

let NOT_EVENTUALLY = prove
 (`!net p. (!x. ~(p x)) /\ ~(trivial_limit net) ==> ~(eventually p net)`,
  REWRITE_TAC[eventually] THEN MESON_TAC[]);;

let EVENTUALLY_SUBSEQUENCE = prove
 (`!P r. (!m n. m < n ==> r m < r n) /\ eventually P sequentially
         ==> eventually (P o r) sequentially`,
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY; o_THM] THEN
  MESON_TAC[MONOTONE_BIGGER; LE_TRANS]);;

let EVENTUALLY_FORALL = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> (eventually (\x. !a. a IN s ==> p a x) net <=>
             !a. a IN s ==> eventually (p a) net)`,
  GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[FORALL_IN_INSERT; EVENTUALLY_AND; ETA_AX] THEN
  MAP_EVERY X_GEN_TAC [`b:B`; `t:B->bool`] THEN
  ASM_CASES_TAC `t:B->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; EVENTUALLY_TRUE]);;

let FORALL_EVENTUALLY = prove
 (`!net:(A net) p s:B->bool.
        FINITE s /\ ~(s = {})
        ==> ((!a. a IN s ==> eventually (p a) net) <=>
             eventually (\x. !a. a IN s ==> p a x) net)`,
  SIMP_TAC[EVENTUALLY_FORALL]);;

let ARCH_EVENTUALLY_LT = prove
 (`!x. eventually (\n. x < &n) sequentially`,
  GEN_TAC THEN MP_TAC(ISPEC `x + &1` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let ARCH_EVENTUALLY_LE = prove
 (`!x. eventually (\n. x <= &n) sequentially`,
  GEN_TAC THEN MP_TAC(ISPEC `x:real` REAL_ARCH_SIMPLE) THEN
  REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN MATCH_MP_TAC MONO_EXISTS THEN
  REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN REAL_ARITH_TAC);;

let ARCH_EVENTUALLY_INV = prove
 (`!e. eventually (\n. inv(&n) < e) sequentially <=> &0 < e`,
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n + 1`)) THEN
    REWRITE_TAC[LE_ADD] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN ASM_ARITH_TAC]);;

let ARCH_EVENTUALLY_INV1 = prove
 (`!e. eventually (\n. inv(&n + &1) < e) sequentially <=> &0 < e`,
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `n:num` (MP_TAC o SPEC `n:num`)) THEN
    REWRITE_TAC[LE_REFL] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] REAL_LT_TRANS) THEN
    REWRITE_TAC[REAL_LT_INV_EQ; REAL_OF_NUM_LT] THEN ARITH_TAC;
    GEN_REWRITE_TAC LAND_CONV [REAL_ARCH_INV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `N:num` THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
    DISCH_TAC THEN TRANS_TAC REAL_LET_TRANS `inv(&N)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
    REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE; REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC]);;

let ARCH_EVENTUALLY_POW = prove
 (`!x b. &1 < x ==> eventually (\n. b < x pow n) sequentially`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN
  FIRST_ASSUM(MP_TAC o SPEC `b:real` o MATCH_MP REAL_ARCH_POW) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `N:num` THEN
  DISCH_TAC THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  TRANS_TAC REAL_LTE_TRANS `(x:real) pow N` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_POW_MONO THEN
  ASM_SIMP_TAC[REAL_LT_IMP_LE]);;

let ARCH_EVENTUALLY_POW_INV = prove
 (`!x e. &0 < e /\ abs(x) < &1
         ==> eventually (\n. abs(x pow n) < e) sequentially`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x = &0` THENL
   [REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `1` THEN
    ASM_SIMP_TAC[REAL_POW_ZERO; LE_1; REAL_ABS_NUM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`inv(abs x)`; `inv e:real`] ARCH_EVENTUALLY_POW) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC REAL_INV_1_LT THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] EVENTUALLY_MONO)] THEN
  X_GEN_TAC `n:num` THEN REWRITE_TAC[REAL_ABS_POW] THEN DISCH_TAC THEN
  GEN_REWRITE_TAC BINOP_CONV [GSYM REAL_INV_INV] THEN
  ASM_SIMP_TAC[GSYM REAL_POW_INV; REAL_LT_INV; REAL_LT_INV2]);;

let EVENTUALLY_IN_SEQUENTIALLY = prove
 (`!P. eventually P sequentially <=> FINITE {n | ~P n}`,
  GEN_TAC THEN
  REWRITE_TAC[num_FINITE; EVENTUALLY_SEQUENTIALLY; IN_ELIM_THM] THEN
  GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[NOT_LE] THEN
  MESON_TAC[LT_IMP_LE; ARITH_RULE `a + 1 <= x ==> a < x`]);;

let EVENTUALLY_NO_SUBSEQUENCE = prove
 (`!P. eventually P sequentially <=>
       ~(?r:num->num. (!m n. m < n ==> r m < r n) /\ (!n. ~P(r n)))`,
  GEN_TAC THEN REWRITE_TAC[EVENTUALLY_IN_SEQUENTIALLY] THEN
  ONCE_REWRITE_TAC[TAUT `(p <=> ~q) <=> (~p <=> q)`] THEN
  REWRITE_TAC[GSYM INFINITE; INFINITE_ENUMERATE_EQ_ALT] THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Metric spaces.                                                            *)
(* ------------------------------------------------------------------------- *)

let is_metric_space = new_definition
  `is_metric_space (s,d) <=>
   (!x y:A. x IN s /\ y IN s ==> &0 <= d(x,y)) /\
   (!x y. x IN s /\ y IN s ==> (d(x,y) = &0 <=> x = y)) /\
   (!x y. x IN s /\ y IN s ==> d(x,y) = d(y,x)) /\
   (!x y z. x IN s /\ y IN s /\ z IN s ==> d(x,z) <= d(x,y) + d(y,z))`;;

let metric_tybij =
 (new_type_definition "metric" ("metric","dest_metric") o prove)
 (`?m:(A->bool)#(A#A->real). is_metric_space m`,
  EXISTS_TAC `({}:A->bool,(\p:A#A. &0))` THEN
  REWRITE_TAC[is_metric_space; NOT_IN_EMPTY]);;

let IS_METRIC_SPACE_SUBSPACE = prove
 (`!(s:A->bool) d. is_metric_space (s,d) ==>
                   (! s'. s' SUBSET s ==> is_metric_space (s',d))`,
  SIMP_TAC[SUBSET; is_metric_space]);;

let mspace = new_definition
  `!m:A metric. mspace m = FST (dest_metric m)`;;

let mdist = new_definition
  `!m:A metric. mdist m = SND (dest_metric m)`;;

let METRIC = prove
 (`!s d. is_metric_space (s:A->bool,d)
         ==> mspace (metric (s,d)) = s /\
             mdist (metric (s,d)) = d`,
  REWRITE_TAC[mspace; mdist] THEN MESON_TAC[metric_tybij; FST; SND]);;

let MSPACE = prove
 (`!s:A->bool d. is_metric_space (s,d) ==> mspace (metric (s,d)) = s`,
  SIMP_TAC[METRIC]);;

let MDIST = prove
 (`!s:A->bool d. is_metric_space (s,d) ==> mdist (metric (s,d)) = d`,
  SIMP_TAC[METRIC]);;

(* ------------------------------------------------------------------------- *)
(* Distance properties.                                                      *)
(* ------------------------------------------------------------------------- *)

let [MDIST_POS_LE; MDIST_0; MDIST_SYM; MDIST_TRIANGLE] =
  let FORALL_METRIC_THM = prove
   (`!P. (!m. P m) <=>
         (!s:A->bool d. is_metric_space(s,d) ==> P(metric (s,d)))`,
    REWRITE_TAC[GSYM FORALL_PAIR_THM; metric_tybij] THEN
    MESON_TAC[CONJUNCT1 metric_tybij]) in
  let METRIC_AXIOMS =
   (`!m. (!x y:A. x IN mspace m /\ y IN mspace m
                  ==> &0 <= mdist m (x,y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> (mdist m (x,y) = &0 <=> x = y)) /\
         (!x y. x IN mspace m /\ y IN mspace m
                ==> mdist m (x,y) = mdist m (y,x)) /\
         (!x y z. x IN mspace m /\ y IN mspace m /\ z IN mspace m
                  ==> mdist m (x,z) <= mdist m (x,y) + mdist m (y,z))`,
    SIMP_TAC[FORALL_METRIC_THM; MSPACE; MDIST; is_metric_space]) in
  (CONJUNCTS o REWRITE_RULE [FORALL_AND_THM] o prove) METRIC_AXIOMS;;

let REAL_ABS_MDIST = prove
 (`!m x y:A. x IN mspace m /\ y IN mspace m
             ==> abs(mdist m (x,y)) = mdist m (x,y)`,
  SIMP_TAC[REAL_ABS_REFL; MDIST_POS_LE]);;

let MDIST_POS_LT = prove
 (`!m x y:A. x IN mspace m /\ y IN mspace m /\ ~(x=y)
             ==> &0 < mdist m (x,y)`,
  SIMP_TAC [REAL_LT_LE; MDIST_POS_LE] THEN MESON_TAC[MDIST_0]);;

let MDIST_REFL = prove
 (`!m x:A. x IN mspace m ==> mdist m (x,x) = &0`,
  SIMP_TAC[MDIST_0]);;

let MDIST_REVERSE_TRIANGLE = prove
 (`!m x y z:A. x IN mspace m /\ y IN mspace m /\ z IN mspace m
               ==> abs(mdist m (x,y) - mdist m (y,z)) <= mdist m (x,z)`,
  GEN_TAC THEN
  CLAIM_TAC "rmk"
    `!x y z:A. x IN mspace m /\ y IN mspace m /\ z IN mspace m
               ==> mdist m (x,y) - mdist m (y,z) <= mdist m (x,z)` THEN
  REPEAT STRIP_TAC THENL
  [REWRITE_TAC[REAL_LE_SUB_RADD] THEN ASM_MESON_TAC[MDIST_TRIANGLE; MDIST_SYM];
   REWRITE_TAC[REAL_ABS_BOUNDS;
               REAL_ARITH `!a b c. --a <= b - c <=> c - a <= b`] THEN
   ASM_MESON_TAC[MDIST_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Open ball.                                                                *)
(* ------------------------------------------------------------------------- *)

let mball = new_definition
  `mball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r}`;;

let IN_MBALL = prove
 (`!m x y:A r.
     y IN mball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) < r`,
  REWRITE_TAC[mball; IN_ELIM_THM]);;

let CENTRE_IN_MBALL = prove
 (`!m x:A r. &0 < r /\ x IN mspace m ==> x IN mball m (x,r)`,
  SIMP_TAC[IN_MBALL; MDIST_REFL; real_gt]);;

let CENTRE_IN_MBALL_EQ = prove
 (`!m x:A r. x IN mball m (x,r) <=> x IN mspace m /\ &0 < r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MBALL] THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MDIST_REFL]);;

let MBALL_SUBSET_MSPACE = prove
 (`!m (x:A) r. mball m (x,r) SUBSET mspace m`,
  SIMP_TAC[SUBSET; IN_MBALL]);;

let MBALL_EMPTY = prove
 (`!m x:A r. r <= &0 ==> mball m (x,r) = {}`,
  REWRITE_TAC[IN_MBALL; EXTENSION; NOT_IN_EMPTY] THEN
  MESON_TAC[MDIST_POS_LE; REAL_ARITH `!x. ~(r <= &0 /\ &0 <= x /\ x < r)`]);;

let MBALL_EMPTY_ALT = prove
 (`!m x:A r. ~(x IN mspace m) ==> mball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MBALL] THEN MESON_TAC[]);;

let MBALL_EQ_EMPTY = prove
 (`!m x:A r. mball m (x,r) = {} <=> ~(x IN mspace m) \/ r <= &0`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [MP_TAC CENTRE_IN_MBALL THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN SET_TAC[];
   STRIP_TAC THEN ASM_SIMP_TAC[MBALL_EMPTY; MBALL_EMPTY_ALT]]);;

let MBALL_SUBSET = prove
 (`!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mball m (x,a) SUBSET mball m (y,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [STRIP_TAC; ASM SET_TAC [MBALL_EMPTY_ALT]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MBALL] THEN FIX_TAC "[z]" THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `mdist m (y,z) <= mdist m (x:A,y) + mdist m (x,z)` THENL
  [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[MDIST_SYM; MDIST_TRIANGLE]]);;

let DISJOINT_MBALL = prove
 (`!m x:A x' r r'. r + r' <= mdist m (x,x')
             ==> DISJOINT (mball m (x,r)) (mball m (x',r'))`,
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_MBALL;
              NOT_IN_EMPTY; CONJ_ACI] THEN
  INTRO_TAC "!m x x' r r'; HPrr'; !x''; x x' x'' d1 d2" THEN
  SUBGOAL_THEN `mdist m (x:A,x') < r + r'`
    (fun th -> ASM_MESON_TAC[th; REAL_NOT_LE]) THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,x'') + mdist m (x'',x')` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE; MDIST_SYM] THEN
  HYP (MP_TAC o end_itlist CONJ) "d1 d2" [] THEN REAL_ARITH_TAC);;

let MBALL_SUBSET_CONCENTRIC = prove
 (`!m (x:A) r1 r2. r1 <= r2 ==> mball m (x,r1) SUBSET mball m (x,r2)`,
  SIMP_TAC[SUBSET; IN_MBALL] THEN MESON_TAC[REAL_LTE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Subspace of a metric space.                                               *)
(* ------------------------------------------------------------------------- *)

let submetric = new_definition
  `submetric (m:A metric) s = metric (s INTER mspace m, mdist m)`;;

let SUBMETRIC = prove
 (`(!m:A metric s. mspace (submetric m s) = s INTER mspace m) /\
   (!m:A metric s. mdist (submetric m s) = mdist m)`,
  CLAIM_TAC "metric"
    `!m:A metric s. is_metric_space (s INTER mspace m, mdist m)` THENL
  [REWRITE_TAC[is_metric_space; IN_INTER] THEN
   SIMP_TAC[MDIST_POS_LE; MDIST_0; MDIST_SYM; MDIST_TRIANGLE];
   ASM_SIMP_TAC[submetric; MSPACE; MDIST]]);;

let MBALL_SUBMETRIC = prove
 (`!m s x:A r. x IN s ==> mball (submetric m s) (x,r) = mball m (x,r) INTER s`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_MBALL; IN_INTER; SUBMETRIC] THEN MESON_TAC[]);;

let SUBMETRIC_UNIV = prove
 (`submetric m (:A) = m`,
  REWRITE_TAC[submetric; INTER_UNIV; mspace; mdist; metric_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Metric topology                                                           *)
(* ------------------------------------------------------------------------- *)

let mtopology = new_definition
  `mtopology (m:A metric) =
   topology {u | u SUBSET mspace m /\
                 !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`;;

let IS_TOPOLOGY_METRIC_TOPOLOGY = prove
 (`istopology {u | u SUBSET mspace m /\
                   !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}`,
  REWRITE_TAC[istopology; IN_ELIM_THM; NOT_IN_EMPTY; EMPTY_SUBSET] THEN
  CONJ_TAC THENL
  [INTRO_TAC "!s t; (s shp) (t thp)" THEN CONJ_TAC THENL
   [HYP SET_TAC "s t" []; ALL_TAC] THEN
   REWRITE_TAC[IN_INTER] THEN INTRO_TAC "!x; sx tx" THEN
   REMOVE_THEN "shp"
     (DESTRUCT_TAC "@r1. r1 rs" o C MATCH_MP (ASSUME `x:A IN s`)) THEN
   REMOVE_THEN "thp"
     (DESTRUCT_TAC "@r2. r2 rt" o C MATCH_MP (ASSUME `x:A IN t`)) THEN
   EXISTS_TAC `min r1 r2` THEN
   ASM_REWRITE_TAC[REAL_LT_MIN; SUBSET_INTER] THEN
   ASM_MESON_TAC[REAL_MIN_MIN; MBALL_SUBSET_CONCENTRIC; SUBSET_TRANS];
   REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN MESON_TAC[]]);;

let OPEN_IN_MTOPOLOGY = prove
 (`!m:A metric u.
     open_in (mtopology m) u <=>
     u SUBSET mspace m /\
     (!x. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mtopology] THEN
  (SUBST1_TAC o REWRITE_RULE[IS_TOPOLOGY_METRIC_TOPOLOGY] o
  SPEC `{u | u SUBSET mspace m /\
             !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}` o
  CONJUNCT2)
  topology_tybij THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM IN] THEN REWRITE_TAC[IN_ELIM_THM]);;

let TOPSPACE_MTOPOLOGY = prove
 (`!m:A metric. topspace (mtopology m) = mspace m`,
  GEN_TAC THEN REWRITE_TAC[mtopology; topspace] THEN
  (SUBST1_TAC o REWRITE_RULE[IS_TOPOLOGY_METRIC_TOPOLOGY] o
  SPEC `{u | u SUBSET mspace m /\
             !x:A. x IN u ==> ?r. &0 < r /\ mball m (x,r) SUBSET u}` o
  CONJUNCT2)
  topology_tybij THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
  [SET_TAC[]; ALL_TAC] THEN
  INTRO_TAC "x" THEN EXISTS_TAC `mspace (m:A metric)` THEN
  ASM_REWRITE_TAC[MBALL_SUBSET_MSPACE; SUBSET_REFL] THEN
  MESON_TAC[REAL_LT_01]);;

let OPEN_IN_MBALL = prove
 (`!m (x:A) r. open_in (mtopology m) (mball m (x,r))`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `&0 < (r:real)` THENL
  [ALL_TAC; ASM_SIMP_TAC[MBALL_EMPTY; GSYM REAL_NOT_LT; OPEN_IN_EMPTY]] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY; MBALL_SUBSET_MSPACE; IN_MBALL; SUBSET] THEN
  INTRO_TAC "![y]; x y xy" THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r - mdist m (x:A,y)` THEN CONJ_TAC THENL
  [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  INTRO_TAC "![z]; z lt" THEN ASM_REWRITE_TAC[] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC);;

let MTOPOLOGY_SUBMETRIC = prove
 (`!m:A metric s. mtopology (submetric m s) = subtopology (mtopology m) s`,
  REWRITE_TAC[TOPOLOGY_EQ] THEN INTRO_TAC "!m s [u]" THEN
  EQ_TAC THEN INTRO_TAC "hp" THENL
  [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN
   EXISTS_TAC
     `UNIONS {mball m (c:A,r) | c,r | mball m (c,r) INTER s SUBSET u}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
    INTRO_TAC "![t]; @c r. sub t" THEN REMOVE_THEN "t" SUBST_VAR_TAC THEN
    MATCH_ACCEPT_TAC OPEN_IN_MBALL;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    HYP_TAC "hp: (us um) hp"
      (REWRITE_RULE[OPEN_IN_MTOPOLOGY; SUBMETRIC; SUBSET_INTER]) THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN REWRITE_TAC[SUBSET] THEN
    INTRO_TAC "!x; x" THEN
    USE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `mball m (x:A,r)` THEN
    CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`x:A`; `r:real`] THEN
     IMP_REWRITE_TAC [GSYM MBALL_SUBMETRIC] THEN ASM SET_TAC[];
     MATCH_MP_TAC CENTRE_IN_MBALL THEN ASM SET_TAC[]]];
   ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_MTOPOLOGY; SUBMETRIC; SUBSET_INTER] THEN
  HYP_TAC "hp: @t. t u" (REWRITE_RULE[OPEN_IN_SUBTOPOLOGY]) THEN
  REMOVE_THEN "u" SUBST_VAR_TAC THEN
  HYP_TAC "t: tm r" (REWRITE_RULE[OPEN_IN_MTOPOLOGY]) THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN INTRO_TAC "!x; xt xs" THEN
  USE_THEN "xt" (HYP_TAC "r: @r. rpos sub" o C MATCH_MP) THEN
  EXISTS_TAC `r:real` THEN IMP_REWRITE_TAC[MBALL_SUBMETRIC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Closed sets.                                                              *)
(* ------------------------------------------------------------------------- *)

let CLOSED_IN_METRIC = prove
 (`!m c:A->bool.
     closed_in (mtopology m) c <=>
     c SUBSET mspace m /\
     (!x. x IN mspace m DIFF c ==> ?r. &0 < r /\ DISJOINT c (mball m (x,r)))`,
  REWRITE_TAC[closed_in; OPEN_IN_MTOPOLOGY; DISJOINT; TOPSPACE_MTOPOLOGY] THEN
  MP_TAC MBALL_SUBSET_MSPACE THEN ASM SET_TAC[]);;

let mcball = new_definition
  `mcball m (x:A,r) =
   {y | x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r}`;;

let IN_MCBALL = prove
 (`!m (x:A) r y.
     y IN mcball m (x,r) <=>
     x IN mspace m /\ y IN mspace m /\ mdist m (x,y) <= r`,
  REWRITE_TAC[mcball; IN_ELIM_THM]);;

let CENTRE_IN_MCBALL = prove
 (`!m x:A r. &0 <= r /\ x IN mspace m ==> x IN mcball m (x,r)`,
  SIMP_TAC[IN_MCBALL; MDIST_REFL]);;

let CENTRE_IN_MCBALL_EQ = prove
 (`!m x:A r. x IN mcball m (x,r) <=> x IN mspace m /\ &0 <= r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_MCBALL] THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_SIMP_TAC[MDIST_REFL]);;

let MCBALL_EMPTY = prove
 (`!m (x:A) r. r < &0 ==> mcball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MCBALL] THEN
  MESON_TAC[REAL_LET_TRANS; MDIST_POS_LE; REAL_NOT_LT]);;

let MCBALL_EMPTY_ALT = prove
 (`!m (x:A) r. ~(x IN mspace m) ==> mcball m (x,r) = {}`,
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_MCBALL; DE_MORGAN_THM] THEN
  MESON_TAC[]);;

let MCBALL_SUBSET_MSPACE = prove
 (`!m (x:A) r. mcball m (x,r) SUBSET (mspace m)`,
  REWRITE_TAC[mcball; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let MBALL_SUBSET_MCBALL = prove
 (`!m x:A r. mball m (x,r) SUBSET mcball m (x,r)`,
  SIMP_TAC[SUBSET; IN_MBALL; IN_MCBALL; REAL_LT_IMP_LE]);;

let MCBALL_SUBSET = prove
 (`!m x y:A a b. y IN mspace m /\ mdist m (x,y) + a <= b
                 ==> mcball m (x,a) SUBSET mcball m (y,b)`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [STRIP_TAC; ASM SET_TAC [MCBALL_EMPTY_ALT]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MCBALL] THEN FIX_TAC "[z]" THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `mdist m (y,z) <= mdist m (x:A,y) + mdist m (x,z)` THENL
  [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[MDIST_SYM; MDIST_TRIANGLE]]);;

let MCBALL_SUBSET_CONCENTRIC = prove
 (`!m (x:A) a b. a <= b ==> mcball m (x,a) SUBSET mcball m (x,b)`,
  SIMP_TAC[SUBSET; IN_MCBALL] THEN MESON_TAC[REAL_LE_TRANS]);;

let MCBALL_SUBSET_MBALL = prove
 (`!m x y:A a b.
     y IN mspace m /\ mdist m (x,y) + a < b
     ==> mcball m (x,a) SUBSET mball m (y,b)`,
  INTRO_TAC "!m x y a b; y lt" THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [POP_ASSUM (LABEL_TAC "x");
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; EMPTY_SUBSET]] THEN
  ASM_REWRITE_TAC[SUBSET; IN_MCBALL; IN_MBALL] THEN
  INTRO_TAC "![z]; z le" THEN HYP REWRITE_TAC "z" [] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (y:A,x) + mdist m (x,z)` THEN
  ASM_SIMP_TAC[MDIST_TRIANGLE] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + a` THEN
  HYP REWRITE_TAC "lt" [] THEN HYP SIMP_TAC "x y" [MDIST_SYM] THEN
  ASM_REAL_ARITH_TAC);;

let MCBALL_SUBSET_MBALL_CONCENTRIC = prove
 (`!m x:A a b. a < b ==> mcball m (x,a) SUBSET mball m (x,b)`,
  INTRO_TAC "!m x a b; lt" THEN ASM_CASES_TAC `x:A IN mspace m` THENL
  [POP_ASSUM (LABEL_TAC "x");
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; EMPTY_SUBSET]] THEN
  MATCH_MP_TAC MCBALL_SUBSET_MBALL THEN ASM_SIMP_TAC[MDIST_REFL] THEN
  ASM_REAL_ARITH_TAC);;

let CLOSED_IN_MCBALL = prove
 (`!m:A metric x r. closed_in (mtopology m) (mcball m (x,r))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CLOSED_IN_METRIC; MCBALL_SUBSET_MSPACE; DIFF; IN_ELIM_THM;
              IN_MCBALL; DE_MORGAN_THM; REAL_NOT_LE] THEN
  FIX_TAC "[y]" THEN
  MAP_EVERY ASM_CASES_TAC [`x:A IN mspace m`; `y:A IN mspace m`] THEN
  ASM_REWRITE_TAC[] THENL
  [ALL_TAC;
   ASM_SIMP_TAC[MCBALL_EMPTY_ALT; DISJOINT_EMPTY] THEN
   MESON_TAC[REAL_LT_01]] THEN
  INTRO_TAC "lt" THEN EXISTS_TAC `mdist m (x:A,y) - r` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[EXTENSION; DISJOINT; IN_INTER; NOT_IN_EMPTY;
              IN_MBALL; IN_MCBALL] THEN
  FIX_TAC "[z]" THEN ASM_CASES_TAC `z:A IN mspace m` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `mdist m (x,y) <= mdist m (x:A,z) + mdist m (z,y)` MP_TAC THENL
  [ASM_SIMP_TAC[MDIST_TRIANGLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[MDIST_SYM] THEN ASM_REAL_ARITH_TAC);;

let MCBALL_SUBMETRIC = prove
 (`!m s x:A r.
     x IN s ==> mcball (submetric m s) (x,r) = mcball m (x,r) INTER s`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[EXTENSION; IN_MCBALL; IN_INTER; SUBMETRIC] THEN
  MESON_TAC[]);;

let OPEN_IN_MTOPOLOGY_MCBALL = prove
 (`!m u. open_in (mtopology m) (u:A->bool) <=>
         u SUBSET mspace m /\
         (!x. x IN u ==> (?r. &0 < r /\ mcball m (x,r) SUBSET u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN
  ASM_CASES_TAC `u:A->bool SUBSET mspace m` THEN
  ASM_REWRITE_TAC[] THEN EQ_TAC THENL
  [INTRO_TAC "hp; !x; x" THEN
   REMOVE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
   EXISTS_TAC `r / &2` THEN
   HYP REWRITE_TAC "rpos" [REAL_HALF] THEN
   TRANS_TAC SUBSET_TRANS `mball m (x:A,r)` THEN HYP REWRITE_TAC "sub" [] THEN
   MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN
   ASM_REAL_ARITH_TAC;
   INTRO_TAC "hp; !x; x" THEN
   REMOVE_THEN "x" (HYP_TAC "hp: @r. rpos sub" o C MATCH_MP) THEN
   EXISTS_TAC `r:real` THEN HYP REWRITE_TAC "rpos" [] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (x:A,r)` THEN
   HYP REWRITE_TAC "sub" [MBALL_SUBSET_MCBALL]]);;

let METRIC_DERIVED_SET_OF = prove
  (`!m s.
      mtopology m derived_set_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. ~(y = x) /\ y IN s /\ y IN mball m (x,r)))}`,
  REWRITE_TAC[derived_set_of; TOPSPACE_MTOPOLOGY; OPEN_IN_MTOPOLOGY; EXTENSION;
              IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (LABEL_TAC "x") THEN EQ_TAC THENL
  [INTRO_TAC "hp; !r; r" THEN HYP_TAC "hp: +" (SPEC `mball m (x:A,r)`) THEN
   ASM_REWRITE_TAC[CENTRE_IN_MBALL_EQ; MBALL_SUBSET_MSPACE] THEN
   DISCH_THEN MATCH_MP_TAC THEN HYP REWRITE_TAC "x" [IN_MBALL] THEN
   INTRO_TAC "![y]; y xy" THEN EXISTS_TAC `r - mdist m (x:A,y)` THEN
   CONJ_TAC THENL
   [REMOVE_THEN "xy" MP_TAC THEN REAL_ARITH_TAC;
    HYP REWRITE_TAC "x y" [SUBSET; IN_MBALL] THEN INTRO_TAC "![z]; z lt" THEN
    HYP REWRITE_TAC "z" [] THEN
    TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
    ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
   INTRO_TAC "hp; !t; t inc r" THEN
   HYP_TAC "r: @r. r ball" (C MATCH_MP (ASSUME `x:A IN t`)) THEN
   HYP_TAC "hp: @y. neq y dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
   EXISTS_TAC `y:A` THEN HYP REWRITE_TAC "neq y" [] THEN
   ASM SET_TAC[]]);;

let METRIC_CLOSURE_OF = prove
  (`!m s.
      mtopology m closure_of s =
      {x:A | x IN mspace m /\
            (!r. &0 < r ==> (?y. y IN s /\ y IN mball m (x,r)))}`,
  REWRITE_TAC[closure_of; TOPSPACE_MTOPOLOGY; OPEN_IN_MTOPOLOGY; EXTENSION;
              IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `x:A IN mspace m` THEN ASM_REWRITE_TAC[] THEN
  POP_ASSUM (LABEL_TAC "x") THEN EQ_TAC THENL
  [INTRO_TAC "hp; !r; r" THEN HYP_TAC "hp: +" (SPEC `mball m (x:A,r)`) THEN
   ASM_REWRITE_TAC[CENTRE_IN_MBALL_EQ; MBALL_SUBSET_MSPACE] THEN
   DISCH_THEN MATCH_MP_TAC THEN HYP REWRITE_TAC "x" [IN_MBALL] THEN
   INTRO_TAC "![y]; y xy" THEN EXISTS_TAC `r - mdist m (x:A,y)` THEN
   CONJ_TAC THENL
   [REMOVE_THEN "xy" MP_TAC THEN REAL_ARITH_TAC;
    HYP REWRITE_TAC "x y" [SUBSET; IN_MBALL] THEN INTRO_TAC "![z]; z lt" THEN
    HYP REWRITE_TAC "z" [] THEN
    TRANS_TAC REAL_LET_TRANS `mdist m (x:A,y) + mdist m (y,z)` THEN
    ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
   INTRO_TAC "hp; !t; t inc r" THEN
   HYP_TAC "r: @r. r ball" (C MATCH_MP (ASSUME `x:A IN t`)) THEN
   HYP_TAC "hp: @y. y dist" (C MATCH_MP (ASSUME `&0 < r`)) THEN
   EXISTS_TAC `y:A` THEN HYP REWRITE_TAC "y" [] THEN
   ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Spheres in metric spaces.                                                 *)
(* ------------------------------------------------------------------------- *)

let msphere = new_definition
  `msphere m (x:A,e) = {y | mdist m (x,y) = e}`;;

(* ------------------------------------------------------------------------- *)
(* Bounded sets.                                                             *)
(* ------------------------------------------------------------------------- *)

let mbounded = new_definition
  `mbounded m s <=> (?c:A b. s SUBSET mcball m (c,b))`;;

let MBOUNDED_SUBSET = prove
 (`!m s t:A->bool. mbounded m t /\ s SUBSET t ==> mbounded m s`,
  REWRITE_TAC[mbounded] THEN SET_TAC[]);;

let MBOUNDED_SUBSET_MSPACE = prove
 (`!m s:A->bool. mbounded m s ==> s SUBSET mspace m`,
  REWRITE_TAC[mbounded] THEN REPEAT STRIP_TAC THEN
  TRANS_TAC SUBSET_TRANS `mcball m (c:A,b)` THEN
  ASM_REWRITE_TAC[MCBALL_SUBSET_MSPACE]);;

let MBOUNDED = prove
 (`!m s. mbounded m s <=>
         s = {} \/
         (!x:A. x IN s ==> x IN mspace m) /\
         (?c b. c IN mspace m /\ (!x. x IN s ==> mdist m (c,x) <= b))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded; SUBSET; IN_MCBALL] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
  ASM SET_TAC[]);;

let MBOUNDED_EMPTY = prove
 (`!m:A metric. mbounded m {}`,
  REWRITE_TAC[mbounded; EMPTY_SUBSET]);;

let MBOUNDED_MCBALL = prove
 (`!m:A metric c b. mbounded m (mcball m (c,b))`,
  REWRITE_TAC[mbounded] THEN MESON_TAC[SUBSET_REFL]);;

let MBOUNDED_MBALL = prove
 (`!m:A metric c b. mbounded m (mball m (c,b))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC MBOUNDED_SUBSET THEN
  EXISTS_TAC `mcball m (c:A,b)` THEN
  REWRITE_TAC[MBALL_SUBSET_MCBALL; MBOUNDED_MCBALL]);;

let MBOUNDED_INSERT = prove
 (`!m a:A s. mbounded m (a INSERT s) <=> a IN mspace m /\ mbounded m s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MBOUNDED; NOT_INSERT_EMPTY; IN_INSERT] THEN
  ASM_CASES_TAC `a:A IN mspace m` THEN ASM_REWRITE_TAC[] THENL
  [ALL_TAC; ASM_MESON_TAC[]] THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY] THENL [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THENL
  [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`c:A`; `max b (mdist m (c:A,a))`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MAX_MAX] THEN
  TRANS_TAC REAL_LE_TRANS `b:real` THEN ASM_SIMP_TAC[REAL_MAX_MAX]);;

let MBOUNDED_INTER = prove
 (`!m:A metric s t. mbounded m s /\ mbounded m t ==> mbounded m (s INTER t)`,
  REWRITE_TAC[mbounded] THEN SET_TAC[]);;

let MBOUNDED_UNION = prove
 (`!m:A metric s t. mbounded m (s UNION t) <=> mbounded m s /\ mbounded m t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded] THEN EQ_TAC THENL
  [SET_TAC[]; INTRO_TAC "(@c1 b1. s) (@c2 b2. t)"] THEN
  ASM_CASES_TAC
    `&0 <= b1 /\ &0 <= b2 /\ c1:A IN mspace m /\ c2 IN mspace m` THENL
  [POP_ASSUM STRIP_ASSUME_TAC;
   POP_ASSUM MP_TAC THEN REWRITE_TAC[DE_MORGAN_THM; REAL_NOT_LE] THEN
   ASM SET_TAC [MCBALL_EMPTY; MCBALL_EMPTY_ALT]] THEN
  MAP_EVERY EXISTS_TAC [`c1:A`; `b1 + b2 + mdist m (c1:A,c2)`] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
  [TRANS_TAC SUBSET_TRANS `mcball m (c1:A,b1)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MCBALL_SUBSET_CONCENTRIC THEN
   CUT_TAC `&0 <= mdist m (c1:A,c2)` THENL
   [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[MDIST_POS_LE]];
   TRANS_TAC SUBSET_TRANS `mcball m (c2:A,b2)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC MCBALL_SUBSET THEN ASM_SIMP_TAC[MDIST_SYM] THEN
   ASM_REAL_ARITH_TAC]);;

let MBOUNDED_IFF_FINITE_DIAMETER = prove
 (`!m:A metric s. mbounded m s <=>
                  s SUBSET mspace m /\
                  (?b. !x y. x IN s /\ y IN s ==> mdist m (x,y) <= b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[mbounded; SUBSET; IN_MCBALL] THEN
  EQ_TAC THENL
  [INTRO_TAC "@c b. hp" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
   EXISTS_TAC `b + b:real` THEN INTRO_TAC "!x y; x y" THEN
   TRANS_TAC REAL_LE_TRANS `mdist m (x:A,c) + mdist m (c,y)` THEN
   CONJ_TAC THENL
   [ASM_MESON_TAC[MDIST_TRIANGLE];
    MATCH_MP_TAC REAL_LE_ADD2 THEN ASM_MESON_TAC[MDIST_SYM]];
   ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN
   POP_ASSUM (DESTRUCT_TAC "@a. a" o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
   INTRO_TAC "inc (@b. bound)" THEN
   MAP_EVERY EXISTS_TAC [`a:A`; `b:real`] THEN ASM_SIMP_TAC[]]);;

let MBOUNDED_SUBMETRIC = prove
 (`!m:A metric s.
     mbounded (submetric m s) t <=> mbounded m (s INTER t) /\ t SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBMETRIC] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A decision procedure for metric spaces.                                   *)
(* ------------------------------------------------------------------------- *)

let METRIC_ARITH : term -> thm =
  let SUP_CONV =
    let conv0 = REWR_CONV SUP_INSERT_INSERT
    and conv1 = REWR_CONV SUP_SING in
    conv1 ORELSEC (conv0 THENC REPEATC conv0 THENC TRY_CONV conv1) in
  let MAXDIST_THM = prove
   (`!m s x y:A.
       mbounded m s /\ x IN s /\ y IN s
       ==> mdist m (x,y) =
           sup (IMAGE (\a. abs(mdist m (x,a) - mdist m (a,y))) s)`,
    REPEAT GEN_TAC THEN INTRO_TAC "bnd x y" THEN
    MATCH_MP_TAC (GSYM SUP_UNIQUE) THEN
    CLAIM_TAC "inc" `!p:A. p IN s ==> p IN mspace m` THENL
    [HYP SET_TAC "bnd" [MBOUNDED_SUBSET_MSPACE]; ALL_TAC] THEN
    GEN_TAC THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN EQ_TAC THENL
    [INTRO_TAC "le; ![z]; z" THEN
     TRANS_TAC REAL_LE_TRANS `mdist m (x:A,y)` THEN
     ASM_SIMP_TAC[MDIST_REVERSE_TRIANGLE];
     DISCH_THEN (MP_TAC o C MATCH_MP (ASSUME `y:A IN s`)) THEN
     ASM_SIMP_TAC[MDIST_REFL; REAL_SUB_RZERO; REAL_ABS_MDIST]])
  and METRIC_EQ_THM = prove
   (`!m s x y:A.
       s SUBSET mspace m /\ x IN s /\ y IN s
       ==> (x = y <=> (!a. a IN s ==> mdist m (x,a) = mdist m (y,a)))`,
    INTRO_TAC "!m s x y; sub sx sy" THEN EQ_TAC THEN SIMP_TAC[] THEN
    DISCH_THEN (MP_TAC o SPEC `y:A`) THEN
    CLAIM_TAC "x y" `x:A IN mspace m /\ y IN mspace m` THENL
    [ASM SET_TAC []; ASM_SIMP_TAC[MDIST_REFL; MDIST_0]]) in
  let CONJ1_CONV : conv -> conv =
    let TRUE_CONJ_CONV = REWR_CONV (MESON [] `T /\ p <=> p`) in
    fun conv -> LAND_CONV conv THENC TRUE_CONJ_CONV in
  let IN_CONV : conv =
    let DISJ_TRUE_CONV = REWR_CONV (MESON [] `p \/ T <=> T`)
    and TRUE_DISJ_CONV = REWR_CONV (MESON [] `T \/ p <=> T`) in
    let REFL_CONV = REWR_CONV (MESON [] `x:A = x <=> T`) in
    let conv0 = REWR_CONV (EQF_INTRO (SPEC_ALL NOT_IN_EMPTY)) in
    let conv1 = REWR_CONV IN_INSERT in
    let conv2 = LAND_CONV REFL_CONV THENC TRUE_DISJ_CONV in
    let rec IN_CONV tm =
      (conv0 ORELSEC
       (conv1 THENC
        (conv2 ORELSEC
         (RAND_CONV IN_CONV THENC DISJ_TRUE_CONV)))) tm in
    IN_CONV
  and IMAGE_CONV : conv =
    let pth0,pth1 = CONJ_PAIR IMAGE_CLAUSES in
    let conv0 = REWR_CONV pth0
    and conv1 = REWR_CONV pth1 THENC TRY_CONV (LAND_CONV BETA_CONV) in
    let rec IMAGE_CONV tm =
      (conv0 ORELSEC (conv1 THENC RAND_CONV IMAGE_CONV)) tm in
    IMAGE_CONV in
  let SUBSET_CONV : conv -> conv =
    let conv0 = REWR_CONV (EQT_INTRO (SPEC_ALL EMPTY_SUBSET)) in
    let conv1 = REWR_CONV INSERT_SUBSET in
    fun conv ->
      let conv2 = conv1 THENC CONJ1_CONV conv in
      REPEATC conv2 THENC conv0 in
  let rec prove_hyps th =
    match hyp th with
    | [] -> th
    | htm :: _ ->
        let emth = SPEC htm EXCLUDED_MIDDLE in
        let nhp = EQF_INTRO (ASSUME (mk_neg htm)) in
        let nth1 = (SUBS_CONV [nhp] THENC PRESIMP_CONV) (concl th) in
        let nth2 = MESON [nhp] (rand (concl nth1)) in
        let nth = EQ_MP (SYM nth1) nth2 in
        prove_hyps(DISJ_CASES emth th nth) in
  let rec guess_metric tm =
    match tm with
    | Comb(Const("mdist",_),m) -> m
    | Comb(Const("mspace",_),m) -> m
    | Comb(s,t) -> (try guess_metric s with Failure _ -> guess_metric t)
    | Abs(_, bd) -> guess_metric bd
    | _ -> failwith "metric not found" in
  let find_mdist mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_eq mty =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("=",ty),_),_) when fst(dest_fun_ty ty) = mty -> [tm]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find
  and find_points mtm =
    let rec find tm =
      match tm with
      | Comb(Comb(Const("mdist",_),pmtm),p) when pmtm = mtm ->
          let x,y = dest_pair p in
          if x = y then [x] else [x;y]
      | Comb(Comb(Const("IN",_),x),Comb(Const("mspace",_),pmtm))
          when pmtm = mtm -> [x]
      | Comb(s,t) -> union (find s) (find t)
      | Abs(v, bd) -> filter (fun x -> not(free_in v x)) (find bd)
      | _ -> [] in
    find in
  let prenex_conv =
    TOP_DEPTH_CONV BETA_CONV THENC
    PURE_REWRITE_CONV[FORALL_SIMP; EXISTS_SIMP] THENC
    NNFC_CONV THENC DEPTH_BINOP_CONV `(/\)` CONDS_CELIM_CONV THENC
    PRESIMP_CONV THENC
    GEN_REWRITE_CONV REDEPTH_CONV
      [AND_FORALL_THM; LEFT_AND_FORALL_THM; RIGHT_AND_FORALL_THM;
       LEFT_OR_FORALL_THM; RIGHT_OR_FORALL_THM] THENC
    PRENEX_CONV
  and real_poly_conv =
    let eths = REAL_ARITH
      `(x = y <=> x - y = &0) /\
       (x < y <=> y - x > &0) /\
       (x > y <=> x - y > &0) /\
       (x <= y <=> y - x >= &0) /\
       (x >= y <=> x - y >= &0)` in
    GEN_REWRITE_CONV I [eths] THENC LAND_CONV REAL_POLY_CONV
  and augment_mdist_pos_thm =
    MESON [] `p ==> (q <=> r) ==> (q <=> (p ==> r))` in
  fun tm ->
    let mtm = guess_metric tm in
    let mty = hd(snd(dest_type(type_of mtm))) in
    let mspace_tm = mk_icomb(mk_const("mspace",[]),mtm) in
    let metric_eq_thm = ISPEC mtm METRIC_EQ_THM
    and mk_in_mspace_th =
      let in_tm = mk_const("IN",[mty,aty]) in
      fun pt -> ASSUME (mk_comb(mk_comb(in_tm,pt),mspace_tm)) in
    let th0 = prenex_conv tm in
    let tm0 = rand (concl th0) in
    let avs,bod = strip_forall tm0 in
    let points = find_points mtm bod in
    let in_mspace_conv = GEN_REWRITE_CONV I (map mk_in_mspace_th points) in
    let in_mspace2_conv = CONJ1_CONV in_mspace_conv THENC in_mspace_conv in
    let MDIST_REFL_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_REFL) in
      fun tm -> MP_CONV in_mspace_conv (pconv tm)
    and MDIST_SYM_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm MDIST_SYM) in
      fun tm -> let x,y = dest_pair (rand tm) in
                if x <= y then failwith "MDIST_SYM_CONV" else
                MP_CONV in_mspace2_conv (pconv tm)
    and MBOUNDED_CONV =
      let conv0 = REWR_CONV (EQT_INTRO (ISPEC mtm MBOUNDED_EMPTY)) in
      let conv1 = REWR_CONV (ISPEC mtm MBOUNDED_INSERT) in
      let rec mbounded_conv tm =
        try conv0 tm with Failure _ ->
        (conv1 THENC CONJ1_CONV in_mspace_conv THENC mbounded_conv) tm in
      mbounded_conv in
    let REFL_SYM_CONV = MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV in
    let ABS_MDIST_CONV =
      let pconv = IMP_REWR_CONV (ISPEC mtm REAL_ABS_MDIST) in
      fun tm -> MP_CONV in_mspace2_conv (pconv tm) in
    let metric_eq_prerule =
      (CONV_RULE o BINDER_CONV o BINDER_CONV)
      (LAND_CONV (CONJ1_CONV (SUBSET_CONV in_mspace_conv)) THENC
       RAND_CONV (REWRITE_CONV[FORALL_IN_INSERT; NOT_IN_EMPTY])) in
    let MAXDIST_CONV =
      let maxdist_thm = ISPEC mtm MAXDIST_THM
      and ante_conv =
        CONJ1_CONV MBOUNDED_CONV THENC CONJ1_CONV IN_CONV THENC IN_CONV
      and image_conv =
        IMAGE_CONV THENC ONCE_DEPTH_CONV REFL_SYM_CONV THENC
        PURE_REWRITE_CONV
          [REAL_SUB_LZERO; REAL_SUB_RZERO; REAL_SUB_REFL;
           REAL_ABS_0; REAL_ABS_NEG; REAL_ABS_SUB; INSERT_AC] THENC
        ONCE_DEPTH_CONV ABS_MDIST_CONV THENC
        PURE_REWRITE_CONV[INSERT_AC] in
      let sup_conv = RAND_CONV image_conv THENC SUP_CONV in
      fun fset_tm ->
        let maxdist_th = SPEC fset_tm maxdist_thm in
        fun tm ->
          let th0 = MP_CONV ante_conv (IMP_REWR_CONV maxdist_th tm) in
          let tm0 = rand (concl th0) in
          let th1 = sup_conv tm0 in
          TRANS th0 th1 in
    let AUGMENT_MDISTS_POS_RULE =
      let mdist_pos_le = ISPEC mtm MDIST_POS_LE in
      let augment_rule : term -> thm -> thm =
        let mk_mdist_pos_thm tm =
          let xtm,ytm = dest_pair (rand tm) in
          let pth = SPECL[xtm;ytm] mdist_pos_le in
          MP_CONV (CONJ1_CONV in_mspace_conv THENC in_mspace_conv) pth in
        fun mdist_tm ->
          let ith =
            MATCH_MP augment_mdist_pos_thm (mk_mdist_pos_thm mdist_tm) in
          fun th -> MATCH_MP ith th in
      fun th ->
        let mdist_thl = find_mdist mtm (concl th) in
        itlist augment_rule mdist_thl th in
    let BASIC_METRIC_ARITH (tm : term) : thm =
      let mdist_tms = find_mdist mtm tm in
      let th0 =
        let eqs =
          mapfilter (MDIST_REFL_CONV ORELSEC MDIST_SYM_CONV) mdist_tms in
        (ONCE_DEPTH_CONV in_mspace_conv THENC PRESIMP_CONV THENC
         SUBS_CONV eqs THENC REAL_RAT_REDUCE_CONV THENC
         ONCE_DEPTH_CONV real_poly_conv) tm in
      let tm0 = rand (concl th0) in
      let points = find_points mtm tm0 in
      let fset_tm = mk_setenum(points,mty) in
      let METRIC_EQ_CONV =
        let th = metric_eq_prerule (SPEC fset_tm metric_eq_thm) in
        fun tm ->
          let xtm,ytm = dest_eq tm in
          let th0 = SPECL[xtm;ytm] th in
          let th1 = MP_CONV (CONJ1_CONV IN_CONV THENC IN_CONV) th0 in
          let tm1 = rand (concl th1) in
          let th2 = ONCE_DEPTH_CONV REFL_SYM_CONV tm1 in
          TRANS th1 th2 in
      let eq1 = map (MAXDIST_CONV fset_tm) (find_mdist mtm tm0)
      and eq2 = map METRIC_EQ_CONV (find_eq mty tm0) in
      let th1 = AUGMENT_MDISTS_POS_RULE (SUBS_CONV (eq1 @ eq2) tm0) in
      let tm1 = rand (concl th1) in
      prove_hyps (EQ_MP (SYM th0) (EQ_MP (SYM th1) (REAL_ARITH tm1))) in
    let SIMPLE_METRIC_ARITH tm =
      let th0 = (WEAK_CNF_CONV THENC CONJ_CANON_CONV) tm in
      let tml =
        try conjuncts (rand (concl th0))
        with Failure s -> failwith("conjuncts "^s) in
      let th1 =
        try end_itlist CONJ (map BASIC_METRIC_ARITH tml)
        with Failure s -> failwith("end_itlist "^s) in
      EQ_MP (SYM th0) th1 in
    let elim_exists tm =
      let points = find_points mtm tm in
      let rec try_points v tm ptl =
        if ptl = [] then fail () else
        let xtm = hd ptl in
        try EXISTS (mk_exists(v,tm),xtm) (elim_exists (vsubst [xtm,v] tm))
        with Failure _ -> try_points v tm (tl ptl)
      and elim_exists tm =
        try let v,bd = dest_exists tm in
            try_points v bd points
        with Failure _ -> SIMPLE_METRIC_ARITH tm in
      elim_exists tm in
    EQ_MP (SYM th0) (GENL avs (elim_exists bod));;

let METRIC_ARITH_TAC = CONV_TAC METRIC_ARITH;;

let ASM_METRIC_ARITH_TAC =
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (not o is_forall o concl))) THEN
  METRIC_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Compact sets.                                                             *)
(* ------------------------------------------------------------------------- *)

let compact_in = new_definition
  `!top s:A->bool.
     compact_in top s <=>
     s SUBSET topspace top /\
     (!U. (!u. u IN U ==> open_in top u) /\ s SUBSET UNIONS U
          ==> (?V. FINITE V /\ V SUBSET U /\ s SUBSET UNIONS V))`;;

let compact_space = new_definition
 `compact_space(top:A topology) <=> compact_in top (topspace top)`;;

let COMPACT_SPACE_ALT = prove
 (`!top:A topology.
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            topspace top SUBSET UNIONS U
            ==> ?V. FINITE V /\ V SUBSET U /\ topspace top SUBSET UNIONS V`,
  REWRITE_TAC[compact_space; compact_in; SUBSET_REFL]);;

let COMPACT_SPACE = prove
 (`!top:A topology.
        compact_space top <=>
        !U. (!u. u IN U ==> open_in top u) /\
            UNIONS U = topspace top
            ==> ?V. FINITE V /\ V SUBSET U /\ UNIONS V = topspace top`,
  GEN_TAC THEN REWRITE_TAC[COMPACT_SPACE_ALT] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; UNIONS_SUBSET] THEN
  AP_TERM_TAC THEN ABS_TAC THEN
  MESON_TAC[SUBSET; OPEN_IN_SUBSET]);;

let COMPACT_IN_ABSOLUTE = prove
 (`!top s:A->bool.
        compact_in (subtopology top s) s <=> compact_in top s`,
  REWRITE_TAC[compact_in] THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; SUBSET_INTER; SUBSET_REFL] THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY; SET_RULE
   `(!x. x IN s ==> ?y. P y /\ x = f y) <=> s SUBSET IMAGE f {y | P y}`] THEN
  REWRITE_TAC[IMP_CONJ; FORALL_SUBSET_IMAGE] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
  REWRITE_TAC[SUBSET_INTER; SUBSET_REFL] THEN SET_TAC[]);;

let COMPACT_IN_SUBSPACE = prove
 (`!top s:A->bool.
        compact_in top s <=>
        s SUBSET topspace top /\ compact_space (subtopology top s)`,
  REWRITE_TAC[compact_space; COMPACT_IN_ABSOLUTE; TOPSPACE_SUBTOPOLOGY] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  SIMP_TAC[SET_RULE `s SUBSET t ==> t INTER s = s`] THEN
  REWRITE_TAC[COMPACT_IN_ABSOLUTE] THEN
  REWRITE_TAC[TAUT `(p <=> ~(q ==> ~p)) <=> (p ==> q)`] THEN
  SIMP_TAC[compact_in]);;

let COMPACT_IN_SUBSET_TOPSPACE = prove
 (`!top s:A->bool. compact_in top s ==> s SUBSET topspace top`,
  SIMP_TAC[compact_in]);;

let FINITE_IMP_COMPACT_IN = prove
 (`!top s:A->bool. s SUBSET topspace top /\ FINITE s ==> compact_in top s`,
  SIMP_TAC[compact_in] THEN INTRO_TAC "!top s; sub fin; !U; U s" THEN
  EXISTS_TAC `IMAGE (\x:A. @u. u IN U /\ x IN u) s` THEN
  HYP SIMP_TAC "fin" [FINITE_IMAGE] THEN ASM SET_TAC []);;

let COMPACT_IN_EMPTY = prove
 (`!top:A topology. compact_in top {}`,
  GEN_TAC THEN MATCH_MP_TAC FINITE_IMP_COMPACT_IN THEN
  REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET]);;

let CLOSED_COMPACT_IN = prove
 (`!top k c:A->bool. compact_in top k /\ c SUBSET k /\ closed_in top c
                     ==> compact_in top c`,
  INTRO_TAC "! *; cpt sub cl" THEN REWRITE_TAC[compact_in] THEN CONJ_TAC THENL
  [HYP SET_TAC "sub cpt" [compact_in]; INTRO_TAC "!U; U c"] THEN
  HYP_TAC "cpt: ksub cpt" (REWRITE_RULE[compact_in]) THEN
  REMOVE_THEN "cpt" (MP_TAC o
    SPEC `(topspace top DIFF c:A->bool) INSERT U`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [CUT_TAC `open_in top (topspace top DIFF c:A->bool)` THENL
    [HYP SET_TAC "U" [IN_DIFF];
     HYP SIMP_TAC "cl" [OPEN_IN_DIFF; OPEN_IN_TOPSPACE]];
    HYP_TAC "cl: c' cl" (REWRITE_RULE[closed_in]) THEN
    REWRITE_TAC[SUBSET; IN_INSERT; IN_DIFF; IN_UNIONS] THEN
    INTRO_TAC "!x; x" THEN ASM_CASES_TAC `x:A IN c` THEN
    POP_ASSUM (LABEL_TAC "x'") THENL
    [HYP SET_TAC "c x'" [];
     EXISTS_TAC `topspace top DIFF c:A->bool` THEN
     ASM_REWRITE_TAC[] THEN ASM SET_TAC []]];
   INTRO_TAC "@V. fin v k" THEN
   EXISTS_TAC `V DELETE (topspace top DIFF c:A->bool)` THEN
   ASM_REWRITE_TAC[FINITE_DELETE] THEN
   CONJ_TAC THENL [ASM SET_TAC []; ALL_TAC] THEN
   REWRITE_TAC[SUBSET; IN_UNIONS; IN_DELETE] THEN ASM SET_TAC []]);;

let CLOSED_IN_COMPACT_SPACE = prove
 (`!top s:A->bool.
        compact_space top /\ closed_in top s ==> compact_in top s`,
  REWRITE_TAC[compact_space] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC CLOSED_COMPACT_IN THEN EXISTS_TAC `topspace top:A->bool` THEN
  ASM_MESON_TAC[CLOSED_IN_SUBSET]);;

let COMPACT_IN_IMP_MBOUNDED = prove
 (`!m s:A->bool. compact_in (mtopology m) s ==> mbounded m s`,
  REWRITE_TAC[compact_in; TOPSPACE_MTOPOLOGY; mbounded] THEN
  INTRO_TAC "!m s; s cpt" THEN ASM_CASES_TAC `s:A->bool = {}` THENL
  [ASM_REWRITE_TAC[EMPTY_SUBSET];
   POP_ASSUM (DESTRUCT_TAC "@a. a" o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY])] THEN
  CLAIM_TAC "a'" `a:A IN mspace m` THENL [ASM SET_TAC[]; EXISTS_TAC `a:A`] THEN
  REMOVE_THEN "cpt" (MP_TAC o SPEC `{mball m (a:A,&n) | n IN (:num)}`) THEN
  ANTS_TAC THENL
  [CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN; OPEN_IN_MBALL];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_UNIV] THEN
    INTRO_TAC "!x; x" THEN CLAIM_TAC "@n. n" `?n. mdist m (a:A,x) <= &n` THENL
    [MATCH_ACCEPT_TAC REAL_ARCH_SIMPLE;
     EXISTS_TAC `mball m (a:A,&n + &1)`] THEN
    CONJ_TAC THENL
    [REWRITE_TAC[REAL_OF_NUM_ADD; IN_UNIV] THEN MESON_TAC[];
     ASM_SIMP_TAC[IN_MBALL; REAL_ARITH `!x. x <= &n ==> x < &n + &1`] THEN
     ASM SET_TAC []]];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin V cov" THEN
  CLAIM_TAC "@k. k" `?k. !v. v IN V ==> v = mball m (a:A,&(k v))` THENL
  [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN ASM SET_TAC [];
   ALL_TAC] THEN
  CLAIM_TAC "kfin" `FINITE (IMAGE (k:(A->bool)->num) V)` THENL
  [HYP SIMP_TAC "fin" [FINITE_IMAGE];
   HYP_TAC "kfin: @n. n" (REWRITE_RULE[num_FINITE])] THEN EXISTS_TAC `&n` THEN
  TRANS_TAC SUBSET_TRANS `UNIONS (V:(A->bool)->bool)` THEN
  HYP SIMP_TAC "cov" [UNIONS_SUBSET] THEN INTRO_TAC "![v]; v" THEN
  USE_THEN "v" (HYP_TAC "k" o C MATCH_MP) THEN REMOVE_THEN "k" SUBST1_TAC THEN
  TRANS_TAC SUBSET_TRANS `mball m (a:A,&n)` THEN
  REWRITE_TAC[MBALL_SUBSET_MCBALL] THEN MATCH_MP_TAC MBALL_SUBSET THEN
  ASM_SIMP_TAC[MDIST_REFL; REAL_ADD_LID; REAL_OF_NUM_LE] THEN
  HYP SET_TAC "n v" []);;

let COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT = prove
 (`!top k s:A->bool.
     compact_in (subtopology top s) k ==> compact_in top k`,
  REWRITE_TAC[compact_in; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER] THEN
  INTRO_TAC "!top k s; (k sub) cpt" THEN ASM_REWRITE_TAC[] THEN
  INTRO_TAC "!U; open cover" THEN
  HYP_TAC "cpt: +" (SPEC `{u INTER s | u | u:A->bool IN U}`) THEN
  ANTS_TAC THENL
  [ASM_REWRITE_TAC[GSYM INTER_UNIONS; SUBSET_INTER] THEN
   REWRITE_TAC[IN_ELIM_THM; OPEN_IN_SUBTOPOLOGY] THEN
   INTRO_TAC "!u; @v. v ueq" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN EXISTS_TAC `v:A->bool` THEN
   REMOVE_THEN "v" (HYP_TAC "open" o C MATCH_MP) THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin V k" THEN EXISTS_TAC `IMAGE (\v:A->bool.
    if v IN V then @u. u IN U /\ v = u INTER s else {}) V` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  CONJ_TAC THENL
  [REWRITE_TAC[SUBSET; IN_IMAGE] THEN INTRO_TAC "![u]; @v. ueq v" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN ASM_REWRITE_TAC[] THEN
   HYP_TAC "V" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "V: @u. u veq" o C MATCH_MP) THEN
   REMOVE_THEN "veq" SUBST_VAR_TAC THEN HYP MESON_TAC "u" [];
   ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE] THEN INTRO_TAC "!x; x" THEN
  HYP_TAC "k" (REWRITE_RULE[SUBSET; IN_UNIONS]) THEN
  USE_THEN "x" (HYP_TAC "k: @v. v xINv" o C MATCH_MP) THEN
  LABEL_ABBREV_TAC `u:A->bool = @u. u IN U /\ v = u INTER s` THEN
  CLAIM_TAC "u' veq" `u:A->bool IN U /\ v = u INTER s` THENL
  [REMOVE_THEN "u" SUBST_VAR_TAC THEN
   CUT_TAC `?u:A->bool. u IN U /\ v = u INTER s` THENL
   [MESON_TAC[]; ALL_TAC] THEN
   HYP_TAC "V" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   USE_THEN "v" (HYP_TAC "V" o C MATCH_MP) THEN
   REMOVE_THEN "V" MATCH_ACCEPT_TAC;
   EXISTS_TAC `u:A->bool` THEN CONJ_TAC THENL
   [EXISTS_TAC `v:A->bool` THEN ASM_REWRITE_TAC[];
    HYP SET_TAC "veq xINv" []]]);;

let COMPACT_IMP_COMPACT_IN_SUBTOPOLOGY = prove
 (`!top k s:A->bool.
     compact_in top k /\ k SUBSET s ==> compact_in (subtopology top s) k`,
   INTRO_TAC "!top k s; cpt sub" THEN
   ASM_SIMP_TAC[compact_in; TOPSPACE_SUBTOPOLOGY; SUBSET_INTER;
     COMPACT_IN_SUBSET_TOPSPACE] THEN
   INTRO_TAC "!U; open cover" THEN
   HYP_TAC "cpt: sub' cpt" (REWRITE_RULE[compact_in]) THEN
   (HYP_TAC "cpt: +" o SPEC)
     `{v:A->bool | v | open_in top v /\ ?u. u IN U /\ u = v INTER s}` THEN
   ANTS_TAC THENL
   [SIMP_TAC[IN_ELIM_THM] THEN TRANS_TAC SUBSET_TRANS `UNIONS U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC UNIONS_MONO THEN
    INTRO_TAC "![u]; u" THEN USE_THEN "u" (HYP_TAC "open" o C MATCH_MP) THEN
    HYP_TAC "open: @v. v ueq" (REWRITE_RULE[OPEN_IN_SUBTOPOLOGY]) THEN
    EXISTS_TAC `v:A->bool` THEN REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
    [EXISTS_TAC `v INTER s:A->bool` THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
   INTRO_TAC "@V. fin open cover" THEN
   EXISTS_TAC `{v INTER s | v | v:A->bool IN V}` THEN CONJ_TAC THENL
   [(SUBST1_TAC o SET_RULE)
      `{v INTER s | v | v:A->bool IN V} = IMAGE (\v. v INTER s) V` THEN
    ASM_SIMP_TAC[FINITE_IMAGE];
    ALL_TAC] THEN
   ASM_REWRITE_TAC[GSYM INTER_UNIONS; SUBSET_INTER] THEN
   REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN INTRO_TAC "![u]; @v. v ueq" THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
   HYP_TAC "open" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "open: v @u. u ueq" o C MATCH_MP) THEN
   REMOVE_THEN "ueq" SUBST_VAR_TAC THEN ASM_REWRITE_TAC[]);;

let COMPACT_IN_SUBTOPOLOGY_EQ = prove
 (`!top k s:A->bool.
     compact_in (subtopology top s) k <=> compact_in top k /\ k SUBSET s`,
  REPEAT GEN_TAC THEN
  CUT_TAC `compact_in (subtopology top s) (k:A->bool) ==> k SUBSET s` THENL
  [MESON_TAC[COMPACT_IMP_COMPACT_IN_SUBTOPOLOGY;
     COMPACT_IN_SUBTOPOLOGY_IMP_COMPACT];
   ALL_TAC] THEN
  DISCH_TAC THEN TRANS_TAC SUBSET_TRANS `topspace top INTER s:A->bool` THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  ASM_SIMP_TAC[GSYM TOPSPACE_SUBTOPOLOGY; COMPACT_IN_SUBSET_TOPSPACE]);;

(* ------------------------------------------------------------------------- *)
(* Connected topological spaces.                                             *)
(* ------------------------------------------------------------------------- *)

let connected_space = new_definition
  `connected_space(top:A topology) <=>
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  topspace top SUBSET e1 UNION e2 /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`;;

let CONNECTED_SPACE_EQ = prove
 (`!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  e1 UNION e2 = topspace top /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`,
  REWRITE_TAC[SET_RULE
   `s UNION t = u <=> u SUBSET s UNION t /\ s SUBSET u /\ t SUBSET u`] THEN
  REWRITE_TAC[connected_space] THEN MESON_TAC[OPEN_IN_SUBSET]);;

let CONNECTED_SPACE_CLOSED_IN = prove
 (`!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  topspace top SUBSET e1 UNION e2 /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`,
  GEN_TAC THEN REWRITE_TAC[connected_space] THEN AP_TERM_TAC THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->bool`; `v:A->bool`] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`topspace top DIFF v:A->bool`; `topspace top DIFF u:A->bool`] THEN
  ASM_SIMP_TAC[CLOSED_IN_DIFF; CLOSED_IN_TOPSPACE;
               OPEN_IN_DIFF; OPEN_IN_TOPSPACE] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET)) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET)) THEN
  ASM SET_TAC[]);;

let CONNECTED_SPACE_CLOSED_IN_EQ = prove
 (`!top:A topology.
        connected_space(top:A topology) <=>
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  e1 UNION e2 = topspace top /\ e1 INTER e2 = {} /\
                  ~(e1 = {}) /\ ~(e2 = {}))`,
  REWRITE_TAC[SET_RULE
   `s UNION t = u <=> u SUBSET s UNION t /\ s SUBSET u /\ t SUBSET u`] THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOSED_IN] THEN MESON_TAC[CLOSED_IN_SUBSET]);;

let CONNECTED_SPACE_CLOPEN_IN = prove
 (`!top:A topology.
        connected_space top <=>
        !t. open_in top t /\ closed_in top t ==> t = {} \/ t = topspace top`,
  GEN_TAC THEN REWRITE_TAC[CONNECTED_SPACE_EQ] THEN SIMP_TAC[OPEN_IN_SUBSET;
     SET_RULE `(open_in top e1 ==> e1 SUBSET topspace top) /\
               (open_in top e2 ==> e2 SUBSET topspace top)
               ==> (open_in top e1 /\ open_in top e2 /\
                    e1 UNION e2 = topspace top /\ e1 INTER e2 = {} /\ P <=>
                    e2 = topspace top DIFF e1 /\
                    open_in top e1 /\ open_in top e2 /\ P)`] THEN
  REWRITE_TAC[UNWIND_THM2; closed_in] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN AP_TERM_TAC THEN ABS_TAC THEN
  ONCE_REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ] THEN SET_TAC[]);;

let CONNECTED_SPACE_SUBTOPOLOGY = prove
 (`!top s:A->bool.
        connected_space(subtopology top s) <=>
        ~(?e1 e2. open_in top e1 /\ open_in top e2 /\
                  topspace top INTER s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected_space; OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[MESON[]
   `(?e1 e2. (?t1. P1 t1 /\ e1 = f1 t1) /\ (?t2. P2 t2 /\ e2 = f2 t2) /\
             R e1 e2) <=> (?t1 t2. P1 t1 /\ P2 t2 /\ R(f1 t1) (f2 t2))`] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET)) THEN
  ASM SET_TAC[]);;

let CONNECTED_SPACE_SUBTOPOLOGY_CLOSED_IN = prove
 (`!top s:A->bool.
        connected_space(subtopology top s) <=>
        ~(?e1 e2. closed_in top e1 /\ closed_in top e2 /\
                  topspace top INTER s SUBSET (e1 UNION e2) /\
                  (e1 INTER e2 INTER s = {}) /\
                  ~(e1 INTER s = {}) /\ ~(e2 INTER s = {}))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONNECTED_SPACE_CLOSED_IN; CLOSED_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[MESON[]
   `(?e1 e2. (?t1. P1 t1 /\ e1 = f1 t1) /\ (?t2. P2 t2 /\ e2 = f2 t2) /\
             R e1 e2) <=> (?t1 t2. P1 t1 /\ P2 t2 /\ R(f1 t1) (f2 t2))`] THEN
  AP_TERM_TAC THEN REPEAT(AP_TERM_TAC THEN ABS_TAC) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o MATCH_MP CLOSED_IN_SUBSET)) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hausdorff spaces.                                                         *)
(* ------------------------------------------------------------------------- *)

let hausdorff_space = new_definition
 `hausdorff_space (top:A topology) <=>
        !x y. x IN topspace top /\ y IN topspace top /\ ~(x = y)
              ==> ?u v. open_in top u /\ open_in top v /\ x IN u /\ y IN v /\
                        DISJOINT u v`;;

let HAUSDORFF_SPACE_MTOPOLOGY = prove
 (`!m:A metric. hausdorff_space(mtopology m)`,
  REWRITE_TAC[hausdorff_space; TOPSPACE_MTOPOLOGY] THEN
  MAP_EVERY X_GEN_TAC [`m:A metric`; `x:A`; `y:A`] THEN STRIP_TAC THEN
  EXISTS_TAC `mball m (x:A,mdist m (x,y) / &2)` THEN
  EXISTS_TAC `mball m (y:A,mdist m (x,y) / &2)` THEN
  REWRITE_TAC[SET_RULE `DISJOINT s t <=> !x. x IN s /\ x IN t ==> F`] THEN
  REWRITE_TAC[OPEN_IN_MBALL; IN_MBALL] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN CONV_TAC METRIC_ARITH);;

let COMPACT_IN_IMP_CLOSED_IN = prove
 (`!top s:A->bool.
        hausdorff_space top /\ compact_in top s ==> closed_in top s`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `s:A->bool = {}` THEN
  ASM_REWRITE_TAC[CLOSED_IN_EMPTY] THEN
  REWRITE_TAC[hausdorff_space; compact_in; closed_in] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:A` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN `x:A` o SPECL [`x:A`; `y:A`]) THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [RIGHT_IMP_EXISTS_THM] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:A->A->bool`; `v:A->A->bool`] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `IMAGE (u:A->A->bool) s`) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_FINITE_SUBSET_IMAGE] THEN
  ANTS_TAC THENL [SIMP_TAC[UNIONS_IMAGE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_IMAGE; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `k:A->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `INTERS(IMAGE (v:A->A->bool) k)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTERS THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    ASM SET_TAC[];
    REWRITE_TAC[INTERS_IMAGE; IN_ELIM_THM; SUBSET; IN_DIFF] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[OPEN_IN_CLOSED_IN_EQ]) THEN ASM SET_TAC[]]);;

let CLOSED_IN_HAUSDORFF_SING = prove
 (`!top x:A. hausdorff_space top /\ x IN topspace top ==> closed_in top {x}`,
  MESON_TAC[COMPACT_IN_IMP_CLOSED_IN; FINITE_IMP_COMPACT_IN; FINITE_SING;
            SING_SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Topology bases and sub-bases including Alexander sub-base theorem.        *)
(* ------------------------------------------------------------------------- *)

let ISTOPOLOGY_BASE_ALT = prove
 (`!P:(A->bool)->bool.
        istopology (ARBITRARY UNION_OF P) <=>
        (!s t. (ARBITRARY UNION_OF P) s /\ (ARBITRARY UNION_OF P) t
               ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  GEN_TAC THEN REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[ARBITRARY_UNION_OF_EMPTY] THEN
  MATCH_MP_TAC(TAUT `q ==> (p /\ q <=> p)`) THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ARBITRARY_UNION_OF_UNIONS THEN
  ASM SET_TAC[]);;

let ISTOPOLOGY_BASE_EQ = prove
 (`!P:(A->bool)->bool.
        istopology (ARBITRARY UNION_OF P) <=>
        (!s t. P s /\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))`,
  REWRITE_TAC[ISTOPOLOGY_BASE_ALT; ARBITRARY_UNION_OF_INTER_EQ]);;

let ISTOPOLOGY_BASE = prove
 (`!P:(A->bool)->bool.
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> istopology (ARBITRARY UNION_OF P)`,
  REWRITE_TAC[ISTOPOLOGY_BASE_EQ] THEN
  MESON_TAC[ARBITRARY_UNION_OF_INC]);;

let MINIMAL_TOPOLOGY_BASE = prove
 (`!top:A topology P.
        (!s. P s ==> open_in top s) /\
        (!s t. P s /\ P t ==> P(s INTER t))
        ==> !s. open_in(topology(ARBITRARY UNION_OF P)) s ==> open_in top s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ISTOPOLOGY_BASE) THEN
  SIMP_TAC[topology_tybij] THEN DISCH_THEN(K ALL_TAC) THEN
  ASM_SIMP_TAC[FORALL_UNION_OF; OPEN_IN_UNIONS]);;

let OPEN_IN_TOPOLOGY_BASE_UNIQUE = prove
 (`!top:A topology P.
        (!s. P s ==> open_in top s) /\
        (!s t. P s /\ P t ==> P(s INTER t)) /\
        (!u x. open_in top u /\ x IN u ==> ?b. P b /\ x IN b /\ b SUBSET u)
        ==> open_in top = ARBITRARY UNION_OF P`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  REWRITE_TAC[FORALL_AND_THM; TAUT `(p <=> q) <=> (p ==> q) /\ (q ==> p)`] THEN
  ASM_SIMP_TAC[FORALL_UNION_OF; OPEN_IN_UNIONS] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[UNION_OF; ARBITRARY] THEN
  EXISTS_TAC `{b:A->bool | P b /\ b SUBSET u}` THEN
  SIMP_TAC[FORALL_IN_GSPEC; GSYM SUBSET_ANTISYM_EQ] THEN
  SIMP_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM SET_TAC[]);;

let TOPOLOGY_BASE_UNIQUE = prove
 (`!top:A topology P.
        (!s. P s ==> open_in top s) /\
        (!s t. P s /\ P t ==> P(s INTER t)) /\
        (!u x. open_in top u /\ x IN u ==> ?b. P b /\ x IN b /\ b SUBSET u)
        ==> topology(ARBITRARY UNION_OF P) = top`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(MESON[topology_tybij]
   `open_in top = P ==> topology P = top`) THEN
  MATCH_MP_TAC OPEN_IN_TOPOLOGY_BASE_UNIQUE THEN ASM_REWRITE_TAC[]);;

let ISTOPOLOGY_SUBBASE = prove
 (`!P s:A->bool.
     istopology (ARBITRARY UNION_OF (FINITE INTERSECTION_OF P relative_to s))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISTOPOLOGY_BASE THEN
  MATCH_MP_TAC RELATIVE_TO_INTER THEN
  REWRITE_TAC[FINITE_INTERSECTION_OF_INTER]);;

let OPEN_IN_SUBBASE = prove
 (`!B u s:A->bool.
        open_in (topology
           (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u))) s <=>
        (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u)) s`,
  GEN_TAC THEN GEN_TAC THEN
  REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij); GSYM FUN_EQ_THM; ETA_AX] THEN
  REWRITE_TAC[ISTOPOLOGY_SUBBASE]);;

let TOPSPACE_SUBBASE = prove
 (`!B u:A->bool.
        topspace(topology
           (ARBITRARY UNION_OF (FINITE INTERSECTION_OF B relative_to u))) = u`,
  REWRITE_TAC[OPEN_IN_SUBBASE; topspace; GSYM SUBSET_ANTISYM_EQ] THEN
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM; FORALL_UNION_OF] THEN
    GEN_TAC THEN REWRITE_TAC[ARBITRARY] THEN MATCH_MP_TAC(MESON[]
     `(!x. Q x ==> R x) ==> (!x. P x ==> Q x) ==> (!x. P x ==> R x)`) THEN
    REWRITE_TAC[FORALL_RELATIVE_TO; INTER_SUBSET];
    MATCH_MP_TAC(SET_RULE `x IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[UNION_OF; ARBITRARY; IN_ELIM_THM] THEN
    EXISTS_TAC `{u:A->bool}` THEN REWRITE_TAC[UNIONS_1] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; relative_to] THEN
    EXISTS_TAC `(:A)` THEN REWRITE_TAC[INTER_UNIV] THEN
    REWRITE_TAC[INTERSECTION_OF] THEN EXISTS_TAC `{}:(A->bool)->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; INTERS_0]]);;

let MINIMAL_TOPOLOGY_SUBBASE = prove
 (`!top:A topology u P.
        (!s. P s ==> open_in top s) /\ open_in top u
        ==> !s. open_in(topology(ARBITRARY UNION_OF
                       (FINITE INTERSECTION_OF P relative_to u))) s
                ==> open_in top s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[REWRITE_RULE[topology_tybij] ISTOPOLOGY_SUBBASE] THEN
  REWRITE_TAC[FORALL_UNION_OF; ARBITRARY] THEN
  X_GEN_TAC `v:(A->bool)->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_IN_UNIONS THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
   (SET_RULE `(!x. P x ==> Q x)
              ==> (!x. Q x ==> R x) ==> (!x. P x ==> R x)`)) THEN
  REWRITE_TAC[FORALL_RELATIVE_TO; FORALL_INTERSECTION_OF] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INTERS_INSERT] THEN
  MATCH_MP_TAC OPEN_IN_INTERS THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; FINITE_INSERT; NOT_INSERT_EMPTY] THEN
  ASM_MESON_TAC[]);;

let ISTOPOLOGY_SUBBASE_UNIV = prove
 (`!P:(A->bool)->bool.
       istopology (ARBITRARY UNION_OF (FINITE INTERSECTION_OF P))`,
  GEN_TAC THEN MATCH_MP_TAC ISTOPOLOGY_BASE THEN
  REWRITE_TAC[FINITE_INTERSECTION_OF_INTER]);;

let ALEXANDER_SUBBASE_THEOREM = prove
 (`!top:A topology B.
        topology
          (ARBITRARY UNION_OF
               (FINITE INTERSECTION_OF B relative_to UNIONS B)) = top /\
        (!C. C SUBSET B /\ UNIONS C = topspace top
             ==> ?C'. FINITE C' /\ C' SUBSET C /\ UNIONS C' = topspace top)
        ==> compact_space top`,
  REPEAT GEN_TAC THEN INTRO_TAC "top fin" THEN
  SUBGOAL_THEN `UNIONS B:A->bool = topspace top` ASSUME_TAC THENL
   [EXPAND_TAC "top" THEN REWRITE_TAC[TOPSPACE_SUBBASE]; ALL_TAC] THEN
  REWRITE_TAC[compact_space; compact_in; SUBSET_REFL] THEN
  MP_TAC(ISPEC
   `\C. (!u:A->bool. u IN C ==> open_in top u) /\
        topspace top SUBSET UNIONS C /\
        !C'. FINITE C' /\ C' SUBSET C ==> ~(topspace top SUBSET UNIONS C')`
    ZL_SUBSETS_UNIONS_NONEMPTY) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p' ==> p) /\ q /\ ~r ==> (p /\ q ==> r) ==> p'`) THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `c:((A->bool)->bool)->bool` THEN
    REWRITE_TAC[MEMBER_NOT_EMPTY] THEN STRIP_TAC THEN
    REPEAT(CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    X_GEN_TAC `c':(A->bool)->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:((A->bool)->bool)->bool`; `c':(A->bool)->bool`]
     FINITE_SUBSET_UNIONS_CHAIN) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(A->bool)->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "*")) THEN
  SUBGOAL_THEN
   `?x:A. x IN topspace top /\ ~(x IN UNIONS(B INTER C))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `s SUBSET t /\ ~(s = t) ==> ?x. x IN t /\ ~(x IN s)`) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_INTER] THEN ASM_MESON_TAC[OPEN_IN_SUBSET];
      DISCH_TAC] THEN
    REMOVE_THEN "fin" (MP_TAC o SPEC `B INTER C:(A->bool)->bool`) THEN
    ASM_REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c B'. c IN C /\ open_in top c /\ ~(c = topspace top) /\
           FINITE B' /\ B' SUBSET B /\ ~(B' = {}) /\ (x:A) IN INTERS B' /\
           INTERS B' SUBSET c`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?u:A->bool. open_in top u /\ u IN C /\ x IN u`
    MP_TAC THENL [ASM SET_TAC[]; MATCH_MP_TAC MONO_EXISTS] THEN
    X_GEN_TAC `c:A->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN
    MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SING_SUBSET; FINITE_SING; UNIONS_1; SUBSET_REFL];
      UNDISCH_TAC `(x:A) IN c`] THEN
    UNDISCH_TAC `open_in top (c:A->bool)` THEN EXPAND_TAC "top" THEN
    REWRITE_TAC[REWRITE_RULE[topology_tybij] ISTOPOLOGY_SUBBASE] THEN
    SPEC_TAC(`c:A->bool`,`d:A->bool`) THEN
    ASM_REWRITE_TAC[FORALL_UNION_OF; ARBITRARY] THEN
    X_GEN_TAC `v:(A->bool)->bool` THEN
    DISCH_THEN(LABEL_TAC "+") THEN
    ONCE_REWRITE_TAC[TAUT `p ==> q ==> r <=> q ==> p ==> r`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
     `~(UNIONS v = u) ==> UNIONS v SUBSET u ==> ~(u IN v)`)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET] THEN FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP
       (SET_RULE `(!x. P x ==> Q x)
                  ==> (!x. Q x ==> R x) ==> (!x. P x ==> R x)`)) THEN
      REWRITE_TAC[FORALL_RELATIVE_TO; INTER_SUBSET];
      DISCH_TAC] THEN
    REWRITE_TAC[IN_UNIONS; LEFT_IMP_EXISTS_THM] THEN
    X_GEN_TAC `w:A->bool` THEN STRIP_TAC THEN
    REMOVE_THEN "+" (MP_TAC o SPEC `w:A->bool`) THEN
    ASM_REWRITE_TAC[relative_to; LEFT_IMP_EXISTS_THM] THEN
    REWRITE_TAC[IMP_CONJ; FORALL_INTERSECTION_OF] THEN
    REWRITE_TAC[IMP_IMP; LEFT_FORALL_IMP_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `B':(A->bool)->bool` THEN
    ASM_CASES_TAC `B':(A->bool)->bool = {}` THENL [ALL_TAC; ASM SET_TAC[]] THEN
    ASM_REWRITE_TAC[INTERS_0; INTER_UNIV; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!b. (b:A->bool) IN B'
        ==> ?C'. FINITE C' /\ C' SUBSET C /\
                 topspace top SUBSET UNIONS(b INSERT C')`
  MP_TAC THENL
   [X_GEN_TAC `b:A->bool` THEN DISCH_TAC THEN
    REMOVE_THEN "*" (MP_TAC o SPEC `(b:A->bool) INSERT C`) THEN
    ASM_REWRITE_TAC[FORALL_IN_INSERT; SET_RULE `s SUBSET a INSERT s`] THEN
    MATCH_MP_TAC(TAUT
     `q /\ ~s /\ p /\ (~r ==> t) ==> (p /\ q /\ r ==> s) ==> t`) THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    CONJ_TAC THENL
     [EXPAND_TAC "top" THEN REWRITE_TAC[OPEN_IN_SUBBASE] THEN
      MATCH_MP_TAC UNION_OF_INC THEN REWRITE_TAC[ARBITRARY] THEN
      REWRITE_TAC[INTERSECTION_OF; relative_to] THEN
      EXISTS_TAC `b:A->bool` THEN
      CONJ_TAC THENL [EXISTS_TAC `{b:A->bool}`; ASM SET_TAC[]] THEN
      REWRITE_TAC[FINITE_SING; FORALL_IN_INSERT; INTERS_1; NOT_IN_EMPTY] THEN
      ASM SET_TAC[];
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
      DISCH_THEN(X_CHOOSE_THEN `C':(A->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `C' DELETE (b:A->bool)` THEN
      ASM_REWRITE_TAC[FINITE_DELETE] THEN ASM SET_TAC[]];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]] THEN
  DISCH_THEN(X_CHOOSE_TAC `cc:(A->bool)->(A->bool)->bool`) THEN
  SUBGOAL_THEN
   `topspace top SUBSET
    UNIONS(c INSERT UNIONS(IMAGE (cc:(A->bool)->(A->bool)->bool) B'))`
  MP_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FINITE_UNIONS] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN ASM SET_TAC[]);;

let ALEXANDER_SUBBASE_THEOREM_ALT = prove
 (`!top:A topology B u.
        u SUBSET UNIONS B /\
        topology
          (ARBITRARY UNION_OF
               (FINITE INTERSECTION_OF B relative_to u)) = top /\
        (!C. C SUBSET B /\ u SUBSET UNIONS C
             ==> ?C'. FINITE C' /\ C' SUBSET C /\ u SUBSET UNIONS C')
        ==> compact_space top`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `topspace top:A->bool = u` ASSUME_TAC THENL
   [ASM_MESON_TAC[TOPSPACE_SUBBASE]; ALL_TAC] THEN
  MATCH_MP_TAC ALEXANDER_SUBBASE_THEOREM THEN
  EXISTS_TAC `B relative_to (topspace top:A->bool)` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV)
     [FINITE_INTERSECTION_OF_RELATIVE_TO] THEN
    ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN REWRITE_TAC[RELATIVE_TO] THEN
    ONCE_REWRITE_TAC[SET_RULE `{f x | s x} = {f x | x IN s}`] THEN
    REWRITE_TAC[GSYM INTER_UNIONS] THEN ASM SET_TAC[];
    REWRITE_TAC[RELATIVE_TO; IMP_CONJ] THEN
    ONCE_REWRITE_TAC[SET_RULE `{f x | s x} = IMAGE f s`] THEN
    REWRITE_TAC[FORALL_SUBSET_IMAGE; EXISTS_FINITE_SUBSET_IMAGE] THEN
    REWRITE_TAC[GSYM SIMPLE_IMAGE; GSYM INTER_UNIONS] THEN
    REWRITE_TAC[SET_RULE `s INTER t = s <=> s SUBSET t`] THEN
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The most basic facts about usual topology and metric on R.                *)
(* ------------------------------------------------------------------------- *)

let real_open = new_definition
  `real_open s <=>
      !x. x IN s ==> ?e. &0 < e /\ !x'. abs(x' - x) < e ==> x' IN s`;;

let real_closed = new_definition
 `real_closed s <=> real_open((:real) DIFF s)`;;

let euclideanreal = new_definition
 `euclideanreal = topology real_open`;;

let REAL_OPEN_EMPTY = prove
 (`real_open {}`,
  REWRITE_TAC[real_open; NOT_IN_EMPTY]);;

let REAL_OPEN_UNIV = prove
 (`real_open(:real)`,
  REWRITE_TAC[real_open; IN_UNIV] THEN MESON_TAC[REAL_LT_01]);;

let REAL_OPEN_INTER = prove
 (`!s t. real_open s /\ real_open t ==> real_open (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[real_open; AND_FORALL_THM; IN_INTER] THEN
  MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_TAC THEN MP_TAC th) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `d1:real`) (X_CHOOSE_TAC `d2:real`)) THEN
  MP_TAC(SPECL [`d1:real`; `d2:real`] REAL_DOWN2) THEN
  ASM_MESON_TAC[REAL_LT_TRANS]);;

let REAL_OPEN_UNIONS = prove
 (`(!s. s IN f ==> real_open s) ==> real_open(UNIONS f)`,
  REWRITE_TAC[real_open; IN_UNIONS] THEN MESON_TAC[]);;

let REAL_OPEN_IN = prove
 (`!s. real_open s <=> open_in euclideanreal s`,
  GEN_TAC THEN REWRITE_TAC[euclideanreal] THEN CONV_TAC SYM_CONV THEN
  AP_THM_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 topology_tybij)] THEN
  REWRITE_TAC[REWRITE_RULE[IN] istopology] THEN
  REWRITE_TAC[REAL_OPEN_EMPTY; REAL_OPEN_INTER; SUBSET] THEN
  MESON_TAC[IN; REAL_OPEN_UNIONS]);;

let TOPSPACE_EUCLIDEANREAL = prove
 (`topspace euclideanreal = (:real)`,
  REWRITE_TAC[topspace; EXTENSION; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[REAL_OPEN_UNIV; IN_UNIV; REAL_OPEN_IN]);;

let TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY = prove
 (`!s. topspace (subtopology euclideanreal s) = s`,
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; TOPSPACE_SUBTOPOLOGY; INTER_UNIV]);;

let REAL_CLOSED_IN = prove
 (`!s. real_closed s <=> closed_in euclideanreal s`,
  REWRITE_TAC[real_closed; closed_in; TOPSPACE_EUCLIDEANREAL;
              REAL_OPEN_IN; SUBSET_UNIV]);;

let REAL_OPEN_UNION = prove
 (`!s t. real_open s /\ real_open t ==> real_open(s UNION t)`,
  REWRITE_TAC[REAL_OPEN_IN; OPEN_IN_UNION]);;

let REAL_OPEN_SUBREAL_OPEN = prove
 (`!s. real_open s <=> !x. x IN s ==> ?t. real_open t /\ x IN t /\ t SUBSET s`,
  REWRITE_TAC[REAL_OPEN_IN; GSYM OPEN_IN_SUBOPEN]);;

let REAL_CLOSED_EMPTY = prove
 (`real_closed {}`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_EMPTY]);;

let REAL_CLOSED_UNIV = prove
 (`real_closed(:real)`,
  REWRITE_TAC[REAL_CLOSED_IN; GSYM TOPSPACE_EUCLIDEANREAL;
              CLOSED_IN_TOPSPACE]);;

let REAL_CLOSED_UNION = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s UNION t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_UNION]);;

let REAL_CLOSED_INTER = prove
 (`!s t. real_closed s /\ real_closed t ==> real_closed(s INTER t)`,
  REWRITE_TAC[REAL_CLOSED_IN; CLOSED_IN_INTER]);;

let REAL_CLOSED_INTERS = prove
 (`!f. (!s. s IN f ==> real_closed s) ==> real_closed(INTERS f)`,
  REWRITE_TAC[REAL_CLOSED_IN] THEN REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real->bool)->bool = {}` THEN
  ASM_SIMP_TAC[CLOSED_IN_INTERS; INTERS_0] THEN
  REWRITE_TAC[GSYM TOPSPACE_EUCLIDEANREAL; CLOSED_IN_TOPSPACE]);;

let REAL_OPEN_REAL_CLOSED = prove
 (`!s. real_open s <=> real_closed(UNIV DIFF s)`,
  SIMP_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; TOPSPACE_EUCLIDEANREAL; SUBSET_UNIV;
           OPEN_IN_CLOSED_IN_EQ]);;

let REAL_OPEN_DIFF = prove
 (`!s t. real_open s /\ real_closed t ==> real_open(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; OPEN_IN_DIFF]);;

let REAL_CLOSED_DIFF = prove
 (`!s t. real_closed s /\ real_open t ==> real_closed(s DIFF t)`,
  REWRITE_TAC[REAL_OPEN_IN; REAL_CLOSED_IN; CLOSED_IN_DIFF]);;

let REAL_OPEN_INTERS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_open t) ==> real_open(INTERS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[INTERS_INSERT; INTERS_0; REAL_OPEN_UNIV; IN_INSERT] THEN
  MESON_TAC[REAL_OPEN_INTER]);;

let REAL_CLOSED_UNIONS = prove
 (`!s. FINITE s /\ (!t. t IN s ==> real_closed t) ==> real_closed(UNIONS s)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; REAL_CLOSED_EMPTY; IN_INSERT] THEN
  MESON_TAC[REAL_CLOSED_UNION]);;

let REAL_OPEN_HALFSPACE_GT = prove
 (`!a. real_open {x | x > a}`,
  GEN_TAC THEN REWRITE_TAC[real_open; IN_ELIM_THM] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(a - b):real` THEN ASM_REAL_ARITH_TAC);;

let REAL_OPEN_HALFSPACE_LT = prove
 (`!a. real_open {x | x < a}`,
  GEN_TAC THEN REWRITE_TAC[real_open; IN_ELIM_THM] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(a - b):real` THEN ASM_REAL_ARITH_TAC);;

let REAL_CLOSED_HALFSPACE_LE = prove
 (`!a. real_closed {x | x <= a}`,
  GEN_TAC THEN
  REWRITE_TAC[real_closed; real_open; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(a - b):real` THEN ASM_REAL_ARITH_TAC);;

let REAL_CLOSED_HALFSPACE_GE = prove
 (`!a. real_closed {x | x >= a}`,
  GEN_TAC THEN
  REWRITE_TAC[real_closed; real_open; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN
  X_GEN_TAC `b:real` THEN DISCH_TAC THEN
  EXISTS_TAC `abs(a - b):real` THEN ASM_REAL_ARITH_TAC);;

let real_euclidean_metric = new_definition
  `real_euclidean_metric = metric ((:real),\(x,y). abs(y-x))`;;

let REAL_EUCLIDEAN_METRIC = prove
 (`mspace real_euclidean_metric = (:real) /\
   (!x y. mdist real_euclidean_metric (x,y) = abs(y-x))`,
  SUBGOAL_THEN `is_metric_space((:real),\ (x,y). abs(y-x))` MP_TAC THENL
  [REWRITE_TAC[is_metric_space; IN_UNIV] THEN REAL_ARITH_TAC;
   SIMP_TAC[real_euclidean_metric; metric_tybij; mspace; mdist]]);;

let MTOPOLOGY_REAL_EUCLIDEAN_METRIC = prove
 (`mtopology real_euclidean_metric = euclideanreal`,
  REWRITE_TAC[TOPOLOGY_EQ; OPEN_IN_MTOPOLOGY; REAL_EUCLIDEAN_METRIC;
    GSYM REAL_OPEN_IN; real_open; IN_MBALL; REAL_EUCLIDEAN_METRIC;
    SUBSET; IN_UNIV]);;

let HAUSDORFF_SPACE_EUCLIDEANREAL = prove
 (`hausdorff_space euclideanreal`,
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
              HAUSDORFF_SPACE_MTOPOLOGY]);;

(* ------------------------------------------------------------------------- *)
(* Connectedness and compactness characterizations for R.                    *)
(* ------------------------------------------------------------------------- *)

let CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEANREAL = prove
 (`!s. connected_space(subtopology euclideanreal s) <=> is_realinterval s`,
  let tac = ASM_MESON_TAC[REAL_LT_IMP_LE; REAL_LE_TOTAL; REAL_LE_ANTISYM] in
  GEN_TAC THEN REWRITE_TAC[CONNECTED_SPACE_SUBTOPOLOGY] THEN
  REWRITE_TAC[GSYM REAL_OPEN_IN; is_realinterval; NOT_EXISTS_THM] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
  EQ_TAC THEN DISCH_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real`; `b:real`; `c:real`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(c:real) IN s` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`{x:real | x < c}`; `{x:real | x > c}`]) THEN
    REWRITE_TAC[REAL_OPEN_HALFSPACE_LT; REAL_OPEN_HALFSPACE_GT] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; IN_UNION; IN_ELIM_THM] THEN
    REWRITE_TAC[NOT_IN_EMPTY; REAL_ARITH `x < a \/ x > a <=> ~(x = a)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `a:real`);
      DISCH_THEN(MP_TAC o SPEC `b:real`)] THEN
    ASM_REWRITE_TAC[REAL_LT_LE; real_gt] THEN ASM SET_TAC[];
    REWRITE_TAC[TAUT `~(p /\ q /\ r /\ s /\ t /\ u) <=>
                      t /\ u ==> ~(p /\ q /\ r /\ s)`] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; LEFT_AND_EXISTS_THM] THEN
    REWRITE_TAC[IN_INTER; RIGHT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[MESON[]
     `(!s t x y. P x y s t) <=> (!x y s t. P x y s t)`] THEN
    MATCH_MP_TAC REAL_WLOG_LT THEN
    CONJ_TAC THENL [SET_TAC[]; REWRITE_TAC[GSYM INTER_ASSOC]] THEN
    CONJ_TAC THENL [MESON_TAC[INTER_COMM; UNION_COMM]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`e1:real->bool`; `e2:real->bool`] THEN STRIP_TAC THEN
    REWRITE_TAC[real_open] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(?x:real. a <= x /\ x <= b /\ x IN e1 /\ x IN e2)`
    ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `?x:real. a <= x /\ x <= b /\ ~(x IN e1) /\ ~(x IN e2)`
    MP_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MP_TAC(SPEC `\c:real. !x. a <= x /\ x <= c ==> x IN e1` REAL_COMPLETE) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL [tac; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real` THEN STRIP_TAC THEN
    SUBGOAL_THEN `a <= x /\ x <= b` STRIP_ASSUME_TAC THENL [tac; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!z. a <= z /\ z < x ==> (z:real) IN e1` ASSUME_TAC THENL
     [ASM_MESON_TAC[REAL_NOT_LT; REAL_LT_IMP_LE]; ALL_TAC] THEN
    REPEAT STRIP_TAC THENL
     [SUBGOAL_THEN
       `?d. &0 < d /\ !y. abs(y - x) < d ==> (y:real) IN e1`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[REAL_DOWN; REAL_ARITH `&0 < e ==> ~(x + e <= x)`;
       REAL_ARITH `z <= x + e /\ e < d ==> z < x \/ abs(z - x) < d`];
      SUBGOAL_THEN `?d. &0 < d /\ !y:real. abs(y - x) < d ==> y IN e2`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(SPECL [`x - a:real`; `d:real`] REAL_DOWN2) THEN ANTS_TAC THENL
       [ASM_MESON_TAC[REAL_LT_LE; REAL_SUB_LT]; ALL_TAC] THEN
      ASM_MESON_TAC[REAL_ARITH `e < x - a ==> a <= x - e`;
        REAL_ARITH `&0 < e /\ e < d ==> x - e < x /\ abs((x - e) - x) < d`;
        REAL_ARITH `&0 < e /\ x <= b ==> x - e <= b`]]]);;

let COMPACT_IN_EUCLIDEANREAL_INTERVAL = prove
 (`!a b. compact_in euclideanreal (real_interval[a,b])`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `real_interval[a,b] = {}` THEN
  ASM_REWRITE_TAC[COMPACT_IN_EMPTY] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[REAL_INTERVAL_NE_EMPTY]) THEN
  REWRITE_TAC[COMPACT_IN_SUBSPACE; TOPSPACE_EUCLIDEANREAL; SUBSET_UNIV] THEN
  MATCH_MP_TAC ALEXANDER_SUBBASE_THEOREM_ALT THEN
  EXISTS_TAC
   `{{x | x > a} | a IN (:real)} UNION {{x | x < a} | a IN (:real)}` THEN
  EXISTS_TAC `real_interval[a,b]` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_UNION] THEN
    MATCH_MP_TAC(SET_RULE `(!x. x IN s) ==> t SUBSET s UNION v`) THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNIV] THEN
    MESON_TAC[REAL_ARITH `a > a - &1:real`];
    REWRITE_TAC[subtopology; GSYM ARBITRARY_UNION_OF_RELATIVE_TO] THEN
    AP_TERM_TAC THEN REWRITE_TAC[RELATIVE_TO] THEN
    GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [INTER_COMM] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real->bool` THEN AP_THM_TAC THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC OPEN_IN_TOPOLOGY_BASE_UNIQUE THEN
    REWRITE_TAC[FINITE_INTERSECTION_OF_INTER] THEN CONJ_TAC THENL
     [REWRITE_TAC[FORALL_INTERSECTION_OF] THEN
      X_GEN_TAC `t:(real->bool)->bool` THEN
      ASM_CASES_TAC `t:(real->bool)->bool = {}` THENL
       [ASM_MESON_TAC[TOPSPACE_EUCLIDEANREAL; INTERS_0; OPEN_IN_TOPSPACE];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> MATCH_MP_TAC OPEN_IN_INTERS THEN
        CONJUNCTS_THEN2 ASSUME_TAC MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_FORALL THEN
      X_GEN_TAC `d:real->bool` THEN
      MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
      SPEC_TAC(`d:real->bool`,`d:real->bool`) THEN
      GEN_REWRITE_TAC (BINDER_CONV o LAND_CONV) [GSYM IN] THEN
      REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC; IN_UNIV] THEN
      REWRITE_TAC[GSYM REAL_OPEN_IN; REAL_OPEN_HALFSPACE_LT] THEN
      REWRITE_TAC[REAL_OPEN_HALFSPACE_GT];
      MAP_EVERY X_GEN_TAC [`u:real->bool`; `x:real`] THEN
      REWRITE_TAC[real_open; GSYM REAL_OPEN_IN] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:real`) ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      EXISTS_TAC `{y:real | y > x - d} INTER {y | y < x + d}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_INTERSECTION_OF_INTER THEN CONJ_TAC THEN
        MATCH_MP_TAC FINITE_INTERSECTION_OF_INC THEN
        GEN_REWRITE_TAC I [GSYM IN] THEN
        REWRITE_TAC[IN_UNION; IN_ELIM_THM] THENL
         [DISJ1_TAC THEN EXISTS_TAC `x - d:real`;
          DISJ2_TAC THEN EXISTS_TAC `x + d:real`] THEN
        REWRITE_TAC[IN_UNIV];
        REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[IMP_CONJ; FORALL_SUBSET_UNION; RIGHT_FORALL_IMP_THM] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_SUBSET_IMAGE; SUBSET_UNIV] THEN
    MAP_EVERY X_GEN_TAC [`l:real->bool`; `r:real->bool`] THEN
    REWRITE_TAC[UNIONS_UNION] THEN DISCH_TAC THEN MP_TAC
     (CONJUNCT2(ISPECL [`a:real`; `b:real`] IS_REALINTERVAL_INTERVAL)) THEN
    REWRITE_TAC[GSYM CONNECTED_SPACE_SUBTOPOLOGY_EUCLIDEANREAL] THEN
    REWRITE_TAC[CONNECTED_SPACE_SUBTOPOLOGY; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL
     [`UNIONS (IMAGE (\a:real. {x | x > a}) l)`;
      `UNIONS (IMAGE (\a:real. {x | x < a}) r)`]) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEANREAL; INTER_UNIV] THEN
    MATCH_MP_TAC(TAUT
     `(p /\ q) /\ ((s ==> u) /\ (t ==> u)) /\ (~r ==> u)
      ==> ~(p /\ q /\ r /\ ~s /\ ~t) ==> u`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_UNIONS THEN
      REWRITE_TAC[FORALL_IN_IMAGE; GSYM REAL_OPEN_IN] THEN
      REWRITE_TAC[REAL_OPEN_HALFSPACE_GT; REAL_OPEN_HALFSPACE_LT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET u UNION v
          ==> ((!x. x IN s ==> x IN v) ==> P) ==> u INTER s = {} ==> P`)) THEN
        DISCH_THEN(MP_TAC o SPEC `b:real`);
        FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
         `s SUBSET u UNION v
          ==> ((!x. x IN s ==> x IN u) ==> P) ==> v INTER s = {} ==> P`)) THEN
        DISCH_THEN(MP_TAC o SPEC `a:real`)] THEN
      ASM_REWRITE_TAC[IN_REAL_INTERVAL; REAL_LE_REFL] THEN
      REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `c:real` THEN STRIP_TAC THENL
       [EXISTS_TAC `{{x:real | x < c}}`; EXISTS_TAC `{{x:real | x > c}}`] THEN
      REWRITE_TAC[FINITE_SING; SING_SUBSET; UNIONS_1] THEN
      REWRITE_TAC[IN_UNION; IN_IMAGE; OR_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
      EXISTS_TAC `c:real` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_REAL_INTERVAL; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; UNIONS_IMAGE; NOT_IN_EMPTY; IN_INTER] THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_FORALL_THM; LEFT_IMP_EXISTS_THM] THEN
      X_GEN_TAC `c:real` THEN REWRITE_TAC[CONJ_ASSOC] THEN
      REWRITE_TAC[IN_REAL_INTERVAL] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
      DISCH_THEN(CONJUNCTS_THEN2
       (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)
       (X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `{{x:real | x > u},{x | x < v}}` THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; UNIONS_2] THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_REAL_INTERVAL] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
      REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; IN_IMAGE] THEN CONJ_TAC THENL
       [DISJ1_TAC THEN EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `v:real` THEN ASM_REWRITE_TAC[]]]]);;

let COMPACT_IN_EUCLIDEANREAL = prove
 (`!s. compact_in euclideanreal s <=>
       mbounded real_euclidean_metric s /\ closed_in euclideanreal s`,
  GEN_TAC THEN EQ_TAC THENL
   [MESON_TAC[COMPACT_IN_IMP_CLOSED_IN; HAUSDORFF_SPACE_EUCLIDEANREAL;
              COMPACT_IN_IMP_MBOUNDED; MTOPOLOGY_REAL_EUCLIDEAN_METRIC];
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [mbounded]) THEN
    REWRITE_TAC[mcball; REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
    REWRITE_TAC[SUBSET; LEFT_IMP_EXISTS_THM; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real`; `d:real`] THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_COMPACT_IN THEN
    EXISTS_TAC `real_interval[a - d,a + d]` THEN
    ASM_REWRITE_TAC[COMPACT_IN_EUCLIDEANREAL_INTERVAL] THEN
    REWRITE_TAC[SUBSET; IN_REAL_INTERVAL] THEN X_GEN_TAC `x:real` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Limits in a topological space.                                            *)
(* ------------------------------------------------------------------------- *)

let limit = new_definition
  `limit top (f:A->B) l net <=>
   l IN topspace top /\
   (!u. open_in top u /\ l IN u ==> eventually (\x. f x IN u) net)`;;

let LIMIT_IN_TOPSPACE = prove
 (`!net top f:A->B l. limit top f l net ==> l IN topspace top`,
  SIMP_TAC[limit]);;

let LIMIT_HAUSDORFF_UNIQUE = prove
 (`!net top f:A->B l1 l2.
     ~trivial_limit net /\
     hausdorff_space top /\
     limit top f l1 net /\
     limit top f l2 net
     ==> l1 = l2`,
  REWRITE_TAC[limit; hausdorff_space] THEN
  INTRO_TAC "! *; nontriv hp (l1 hp1) (l2 hp2)" THEN
  REFUTE_THEN (LABEL_TAC "contra") THEN
  REMOVE_THEN "hp" (MP_TAC o SPECL [`l1:B`; `l2:B`]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN REPEAT GEN_TAC THEN
  CUT_TAC `open_in top u /\ open_in top v /\ l1:B IN u /\ l2:B IN v
           ==> ?x:A. f x IN u /\ f x IN v` THENL
  [SET_TAC[]; STRIP_TAC] THEN
  CLAIM_TAC "rmk" `eventually (\x:A. f x:B IN u /\ f x IN v) net` THENL
  [ASM_SIMP_TAC[EVENTUALLY_AND];
   HYP_TAC "rmk" (MATCH_MP EVENTUALLY_HAPPENS) THEN ASM_MESON_TAC[]]);;

let LIMIT_SEQUENTIALLY = prove
 (`!top s l:A.
     limit top s l sequentially <=>
     l IN topspace top /\
     (!u. open_in top u /\ l IN u ==> (?N. !n. N <= n ==> s n IN u))`,
  REWRITE_TAC[limit; EVENTUALLY_SEQUENTIALLY]);;

let LIMIT_SEQUENTIALLY_OFFSET = prove
 (`!top f l:A k. limit top f l sequentially
                 ==> limit top (\i. f (i + k)) l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  USE_THEN "N" MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let LIMIT_SEQUENTIALLY_OFFSET_REV = prove
 (`!top f l:A k. limit top (\i. f (i + k)) l sequentially
                 ==> limit top f l sequentially`,
  SIMP_TAC[LIMIT_SEQUENTIALLY] THEN INTRO_TAC "! *; l lim; !u; hp" THEN
  USE_THEN "hp" (HYP_TAC "lim: @N. N" o C MATCH_MP) THEN
  EXISTS_TAC `N+k:num` THEN INTRO_TAC "!n; n" THEN
  REMOVE_THEN "N" (MP_TAC o SPEC `n-k:num`) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `n - k + k = n:num` (fun th -> REWRITE_TAC[th]) THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Topological limit in metric spaces.                                       *)
(* ------------------------------------------------------------------------- *)

let LIMIT_IN_MSPACE = prove
 (`!net m f:A->B l. limit (mtopology m) f l net ==> l IN mspace m`,
  MESON_TAC[LIMIT_IN_TOPSPACE; TOPSPACE_MTOPOLOGY]);;

let LIMIT_METRIC_UNIQUE = prove
 (`!m f:A->B l1 l2 net.
     ~trivial_limit net /\
     limit (mtopology m) f l1 net /\
     limit (mtopology m) f l2 net
     ==> l1 = l2`,
  MESON_TAC[LIMIT_HAUSDORFF_UNIQUE; HAUSDORFF_SPACE_MTOPOLOGY]);;

let LIMIT_METRIC = prove
 (`!m f:A->B l net.
     limit (mtopology m) f l net <=>
     l IN mspace m /\
     (!e. &0 < e
          ==> eventually (\x. f x IN mspace m /\ mdist m (f x, l) < e) net)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[limit; OPEN_IN_MTOPOLOGY; TOPSPACE_MTOPOLOGY] THEN EQ_TAC THENL
  [INTRO_TAC "l hp" THEN ASM_REWRITE_TAC[] THEN INTRO_TAC "!e; e" THEN
   REMOVE_THEN "hp" (MP_TAC o SPEC `mball m (l:B,e)`) THEN
   ASM_REWRITE_TAC[MBALL_SUBSET_MSPACE] THEN ASM_SIMP_TAC[CENTRE_IN_MBALL] THEN
   REWRITE_TAC[IN_MBALL] THEN ANTS_TAC THENL
   [INTRO_TAC "!x; x lt" THEN
    EXISTS_TAC `e - mdist m (l:B,x)` THEN
    CONJ_TAC THENL
    [ASM_REAL_ARITH_TAC;
     ASM_REWRITE_TAC[SUBSET; IN_MBALL] THEN INTRO_TAC "![y]; y lt'" THEN
     ASM_REWRITE_TAC[] THEN
     TRANS_TAC REAL_LET_TRANS `mdist m (l:B,x) + mdist m (x,y)` THEN
     ASM_SIMP_TAC[MDIST_TRIANGLE] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
    GEN_TAC THEN REWRITE_TAC[] THEN ASM_CASES_TAC `f (x:A):B IN mspace m` THEN
    ASM_SIMP_TAC[MDIST_SYM]];
   INTRO_TAC "l hp" THEN ASM_REWRITE_TAC[] THEN INTRO_TAC "!u; (u hp) l" THEN
   REMOVE_THEN "hp"
     (DESTRUCT_TAC "@r. r sub" o C MATCH_MP (ASSUME `l:B IN u`)) THEN
   REMOVE_THEN "hp" (MP_TAC o C MATCH_MP (ASSUME `&0 < r`)) THEN
   MATCH_MP_TAC (REWRITE_RULE [IMP_CONJ] EVENTUALLY_MONO) THEN
   GEN_TAC THEN REWRITE_TAC[] THEN INTRO_TAC "f lt" THEN
   CLAIM_TAC "rmk" `f (x:A):B IN mball m (l,r)` THENL
   [ASM_SIMP_TAC[IN_MBALL; MDIST_SYM]; HYP SET_TAC "rmk sub" []]]);;

let LIMIT_METRIC_SEQUENTIALLY = prove
 (`!m f:num->A l.
     limit (mtopology m) f l sequentially <=>
     l IN mspace m /\
     (!e. &0 < e ==> (?N. !n. N <= n
                              ==> f n IN mspace m /\ mdist m (f n,l) < e))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LIMIT_METRIC; EVENTUALLY_SEQUENTIALLY] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let LIMIT_IN_CLOSED_IN = prove
 (`!net top s f:A->B l.
      ~trivial_limit net /\ limit top f l net /\
      closed_in top s /\ eventually (\x. f x IN s) net
      ==> l IN s`,
  INTRO_TAC "! *; ntriv lim cl ev" THEN REFUTE_THEN (LABEL_TAC "contra") THEN
  HYP_TAC "lim: l lim" (REWRITE_RULE[limit]) THEN
  REMOVE_THEN "lim" (MP_TAC o SPEC `topspace top DIFF s:B->bool`) THEN
  ASM_SIMP_TAC[OPEN_IN_DIFF; OPEN_IN_TOPSPACE; IN_DIFF; EVENTUALLY_AND] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN DISJ2_TAC THEN INTRO_TAC "nev" THEN
  HYP (MP_TAC o CONJ_LIST) "ev nev" [] THEN
  REWRITE_TAC[GSYM EVENTUALLY_AND] THEN MATCH_MP_TAC NOT_EVENTUALLY THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let LIMIT_SUBMETRIC_IFF = prove
 (`!net m s f:A->B l.
     limit (mtopology (submetric m s)) f l net <=>
     l IN s /\ eventually (\x. f x IN s) net /\ limit (mtopology m) f l net`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[LIMIT_METRIC; SUBMETRIC; IN_INTER; EVENTUALLY_AND] THEN
  EQ_TAC THEN SIMP_TAC[] THENL [INTRO_TAC "l hp"; MESON_TAC[]] THEN
  HYP_TAC "hp" (C MATCH_MP REAL_LT_01) THEN ASM_REWRITE_TAC[]);;

let METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED = prove
 (`!m s:A->bool.
     closed_in (mtopology m) s <=>
     s SUBSET mspace m /\
     (!a l. (!n. a n IN s) /\ limit (mtopology m) a l sequentially
            ==> l IN s)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [INTRO_TAC "cl" THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_METRIC]; INTRO_TAC "!a l; a lim"] THEN
   MATCH_MP_TAC
     (ISPECL[`sequentially`; `mtopology (m:A metric)`] LIMIT_IN_CLOSED_IN) THEN
   EXISTS_TAC `a:num->A` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE];
   ALL_TAC] THEN
  SIMP_TAC[CLOSED_IN_METRIC; IN_DIFF] THEN
  INTRO_TAC "sub seq; !x; x diff" THEN
  REFUTE_THEN (LABEL_TAC "contra" o
    REWRITE_RULE[NOT_EXISTS_THM; MESON[] `~(a /\ b) <=> a ==> ~b`]) THEN
  CLAIM_TAC "@a. a lt"
    `?a. (!n. a n:A IN s) /\ (!n. mdist m (x, a n) < inv(&n + &1))` THENL
  [REWRITE_TAC[GSYM FORALL_AND_THM; GSYM SKOLEM_THM] THEN GEN_TAC THEN
   REMOVE_THEN "contra" (MP_TAC o SPEC `inv (&n + &1)`) THEN
   ANTS_TAC THENL [MATCH_MP_TAC REAL_LT_INV THEN REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[SET_RULE `~DISJOINT s t <=> ?x:A. x IN s /\ x IN t`] THEN
   ASM_REWRITE_TAC[IN_MBALL] THEN MESON_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "a'" `!n:num. a n:A IN mspace m` THENL
  [HYP SET_TAC "sub a" []; ALL_TAC] THEN
  REMOVE_THEN "seq" (MP_TAC o SPECL[`a:num->A`;`x:A`]) THEN
  ASM_REWRITE_TAC[LIMIT_METRIC_SEQUENTIALLY] THEN INTRO_TAC "!e; e" THEN
  HYP_TAC "e -> @N. NZ Ngt Nlt" (ONCE_REWRITE_RULE[REAL_ARCH_INV]) THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  TRANS_TAC REAL_LT_TRANS `inv (&n + &1)` THEN CONJ_TAC THENL
  [HYP MESON_TAC "lt a' x" [MDIST_SYM]; ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS `inv (&N)` THEN HYP REWRITE_TAC "Nlt" [] THEN
  MATCH_MP_TAC REAL_LE_INV2 THEN
  REWRITE_TAC[REAL_OF_NUM_LT; REAL_OF_NUM_LE; REAL_OF_NUM_ADD] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cauchy sequences and complete metric spaces.                              *)
(* ------------------------------------------------------------------------- *)

let cauchy_in = new_definition
  `!m:A metric s:num->A.
     cauchy_in m s <=>
     (!n. s n IN mspace m) /\
     (!e. &0 < e
          ==> (?N. !n n'. N <= n /\ N <= n'
                          ==> mdist m (s n,s n') < e))`;;

let mcomplete = new_definition
  `!m:A metric.
     mcomplete m <=>
     (!s. cauchy_in m s ==> ?x. limit (mtopology m) s x sequentially)`;;

let CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = prove
 (`!m s:A->bool. closed_in (mtopology m) s /\ mcomplete m
                 ==> mcomplete (submetric m s)`,
  INTRO_TAC "!m s; cl cp" THEN REWRITE_TAC[mcomplete] THEN
  INTRO_TAC "![a]; a" THEN CLAIM_TAC "cy'" `cauchy_in m (a:num->A)` THENL
  [REMOVE_THEN "a" MP_TAC THEN SIMP_TAC[cauchy_in; SUBMETRIC; IN_INTER];
   HYP_TAC "cp" (GSYM o REWRITE_RULE[mcomplete]) THEN
   HYP REWRITE_TAC "cp" [LIMIT_SUBMETRIC_IFF] THEN
   REMOVE_THEN "cp" (HYP_TAC "cy': @l.l" o MATCH_MP) THEN EXISTS_TAC `l:A` THEN
   HYP_TAC "a: A cy" (REWRITE_RULE[cauchy_in; SUBMETRIC; IN_INTER]) THEN
   ASM_REWRITE_TAC[EVENTUALLY_TRUE] THEN MATCH_MP_TAC
     (ISPECL [`sequentially`; `mtopology(m:A metric)`] LIMIT_IN_CLOSED_IN) THEN
   EXISTS_TAC `a:num->A` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY; EVENTUALLY_TRUE]]);;

let SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE = prove
 (`!m s:A->bool.
     mcomplete m /\
     (!x l. (!n. x n IN s) /\ limit (mtopology m) x l sequentially ==> l IN s)
            ==> mcomplete (submetric m s)`,
  INTRO_TAC "!m s; cpl seq" THEN SUBGOAL_THEN
    `submetric m (s:A->bool) = submetric m (mspace m INTER s)` SUBST1_TAC THENL
  [REWRITE_TAC[submetric; INTER_ACI]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
  ASM_REWRITE_TAC[METRIC_CLOSED_IN_IFF_SEQUENTIALLY_CLOSED; INTER_SUBSET] THEN
  INTRO_TAC "!a l; a lim" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
  [MATCH_MP_TAC (ISPEC `sequentially` LIMIT_IN_MSPACE) THEN
   HYP MESON_TAC "lim" [];
   REMOVE_THEN "seq" MATCH_MP_TAC THEN HYP SET_TAC "a lim" []]);;

(* ------------------------------------------------------------------------- *)
(* Topological definition of continuous functions.                           *)
(* ------------------------------------------------------------------------- *)

let continuous_map = new_definition
  `!top top' f:A->B.
     continuous_map (top,top')  f <=>
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!u. open_in top' u
          ==> open_in top {x | x IN topspace top /\ f x IN u})`;;

let CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE = prove
 (`!top top' f:A->B. continuous_map (top,top')  f
                     ==> IMAGE f (topspace top) SUBSET topspace top'`,
  REWRITE_TAC[continuous_map] THEN SET_TAC[]);;

let CONTINUOUS_MAP_LIMIT = prove
 (`!net top top' f:A->B g:B->C l.
     continuous_map (top,top')  g /\ limit top f l net
     ==> limit top' (g o f) (g l) net`,
  REWRITE_TAC[limit; o_THM] THEN INTRO_TAC "! *; cont l lim" THEN
  USE_THEN "cont" MP_TAC THEN REWRITE_TAC[continuous_map] THEN
  INTRO_TAC "g cont" THEN ASM_SIMP_TAC[] THEN INTRO_TAC "!u; u gl" THEN
  ASM_CASES_TAC `trivial_limit (net:A net)` THENL
  [ASM_REWRITE_TAC[eventually]; POP_ASSUM (LABEL_TAC "nontriv")] THEN
  REMOVE_THEN "lim"
    (MP_TAC o SPEC `{x:B | x IN topspace top /\ g x:C IN u}`) THEN
  ASM_SIMP_TAC[IN_ELIM_THM; eventually] THEN MESON_TAC[]);;

let CONTINUOUS_MAP_IN_SUBTOPOLOGY = prove
 (`!top top' s f:A->B.
     continuous_map (top,subtopology top' s) f <=>
     continuous_map (top,top')  f /\ IMAGE f (topspace top) SUBSET s`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[continuous_map; TOPSPACE_SUBTOPOLOGY; IN_INTER;
    OPEN_IN_SUBTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC[] THENL
  [INTRO_TAC "img cont" THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
   INTRO_TAC "!u; u" THEN
   SUBGOAL_THEN
     `{x:A | x IN topspace top /\ f x:B IN u} =
      {x | x IN topspace top /\ f x IN u INTER s}`
     (fun th -> REWRITE_TAC[th]) THENL [HYP SET_TAC "img" []; ALL_TAC] THEN
   REMOVE_THEN "cont" MATCH_MP_TAC THEN EXISTS_TAC `u:B->bool` THEN
   ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
   INTRO_TAC "(img cont) img'" THEN
   CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
   INTRO_TAC "!u; @t. t ueq" THEN REMOVE_THEN "ueq" SUBST_VAR_TAC THEN
   SUBGOAL_THEN
     `{x:A | x IN topspace top /\ f x:B IN t INTER s} =
      {x | x IN topspace top /\ f x IN t}`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
   ASM SET_TAC[]]);;

let IMAGE_COMPACT_IN = prove
 (`!top top' (f:A->B) s.
     compact_in top s /\ continuous_map (top,top')  f
     ==> compact_in top' (IMAGE f s)`,
  INTRO_TAC "!top top' f s; cpt cont" THEN REWRITE_TAC[compact_in] THEN
  CONJ_TAC THENL
  [TRANS_TAC SUBSET_TRANS `IMAGE (f:A->B) (topspace top)` THEN
   ASM_SIMP_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; IMAGE_SUBSET;
     COMPACT_IN_SUBSET_TOPSPACE];
   INTRO_TAC "!U; U img"] THEN
  HYP_TAC "cpt : sub cpt" (REWRITE_RULE[compact_in]) THEN
  REMOVE_THEN "cpt" (MP_TAC o
    SPEC `{{x | x | x IN topspace top /\ (f:A->B) x IN u} | u | u IN U}`) THEN
  ANTS_TAC THENL
  [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN
   INTRO_TAC "{![w]; @v. v eq & !x; x}" THENL
   [REMOVE_THEN "eq" SUBST1_TAC THEN
    HYP_TAC "cont : wd cont" (REWRITE_RULE[continuous_map]) THEN ASM SET_TAC[];
    REMOVE_THEN "img" (MP_TAC o SPEC `f (x:A):B` o REWRITE_RULE[SUBSET]) THEN
    ANTS_TAC THENL [HYP SET_TAC "x" []; REWRITE_TAC[IN_UNIONS]] THEN
    INTRO_TAC "@t. t fx" THEN
    EXISTS_TAC `{x:A | x IN topspace top /\ f x:B IN t}` THEN ASM SET_TAC[]];
   ALL_TAC] THEN
  INTRO_TAC "@V. fin sub s" THEN
  CLAIM_TAC "@u. u"
    `?u. !v. v IN V ==> u v IN U /\
                        v = {x:A | x IN topspace top /\ f x:B IN u v}` THENL
  [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
   INTRO_TAC "!v; v" THEN
   HYP_TAC "sub" (REWRITE_RULE[SUBSET; IN_ELIM_THM]) THEN
   REMOVE_THEN "v" (HYP_TAC "sub: @u. u eq" o C MATCH_MP) THEN
   EXISTS_TAC `u:B->bool` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  EXISTS_TAC `IMAGE (u:(A->bool)->(B->bool)) V` THEN CONJ_TAC THENL
  [HYP SIMP_TAC "fin" [FINITE_IMAGE]; ASM SET_TAC []]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise continuity in topological spaces.                               *)
(* ------------------------------------------------------------------------- *)

let topcontinuous_at = new_definition
  `!top top' f:A->B x.
     topcontinuous_at top top' f x <=>
     x IN topspace top /\
     (!x. x IN topspace top ==> f x IN topspace top') /\
     (!v. open_in top' v /\ f x IN v
          ==> (?u. open_in top u /\ x IN u /\ (!y. y IN u ==> f y IN v)))`;;

let CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT = prove
 (`!top top' f:A->B.
     continuous_map (top,top')  f <=>
     (!x. x IN topspace top ==> topcontinuous_at top top' f x)`,
  REPEAT GEN_TAC THEN EQ_TAC THENL
  [SIMP_TAC[continuous_map; topcontinuous_at] THEN
   INTRO_TAC "f v; !x; x; !v; v1 v2" THEN
   REMOVE_THEN "v" (MP_TAC o C MATCH_MP
     (ASSUME `open_in top' (v:B->bool)`)) THEN
   INTRO_TAC "pre" THEN
   EXISTS_TAC `{x:A | x IN topspace top /\ f x:B IN v}` THEN
   ASM_SIMP_TAC[IN_ELIM_THM];
   ALL_TAC] THEN
  SIMP_TAC[continuous_map; topcontinuous_at; SUBSET] THEN
  INTRO_TAC "hp1" THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  INTRO_TAC "![v]; v" THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN INTRO_TAC "!x; x1 x2" THEN
  REMOVE_THEN "hp1" (MP_TAC o SPEC `x:A`) THEN ASM_SIMP_TAC[] THEN
  INTRO_TAC "x3 v1" THEN REMOVE_THEN "v1" (MP_TAC o SPEC `v:B->bool`) THEN
  USE_THEN "x1" (LABEL_TAC "x4" o REWRITE_RULE[IN_ELIM_THM]) THEN
  ASM_SIMP_TAC[] THEN INTRO_TAC "@u. u1 u2 u3" THEN
  EXISTS_TAC `u:A->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SUBSET; IN_ELIM_THM] THEN
  ASM_MESON_TAC[OPEN_IN_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Continuous functions on metric spaces.                                    *)
(* ------------------------------------------------------------------------- *)

let METRIC_CONTINUOUS_MAP = prove
 (`!m m' f:A->B.
     continuous_map (mtopology m,mtopology m') f <=>
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!a e. &0 < e /\ a IN mspace m
            ==> (?d. &0 < d /\
                     (!x. x IN mspace m /\ mdist m (a,x) < d
                          ==> mdist m' (f a, f x) < e)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[continuous_map; TOPSPACE_MTOPOLOGY] THEN
  EQ_TAC THEN SIMP_TAC[] THENL
  [INTRO_TAC "f cont; !a e; e a" THEN
   REMOVE_THEN "cont" (MP_TAC o SPEC `mball m' (f (a:A):B,e)`) THEN
   REWRITE_TAC[OPEN_IN_MBALL] THEN
   ASM_SIMP_TAC[OPEN_IN_MTOPOLOGY; SUBSET; IN_MBALL; IN_ELIM_THM] THEN
   DISCH_THEN (MP_TAC o SPEC `a:A`) THEN ASM_SIMP_TAC[MDIST_REFL];
   SIMP_TAC[OPEN_IN_MTOPOLOGY; SUBSET; IN_MBALL; IN_ELIM_THM] THEN
   ASM_MESON_TAC[]]);;

let CONTINUOUS_MAP_TO_METRIC = prove
 (`!t m f:A->B.
     continuous_map (t,mtopology m) f <=>
     (!x. x IN topspace t
          ==> (!r. &0 < r
                   ==> (?u. open_in t u /\
                            x IN u /\
                            (!y. y IN u ==> f y IN mball m (f x,r)))))`,
  INTRO_TAC "!t m f" THEN
  REWRITE_TAC[CONTINUOUS_MAP_EQ_TOPCONTINUOUS_AT; topcontinuous_at;
              TOPSPACE_MTOPOLOGY] THEN
  EQ_TAC THENL
  [INTRO_TAC "A; !x; x" THEN REMOVE_THEN "A" (MP_TAC o SPEC `x:A`) THEN
   ASM_SIMP_TAC[OPEN_IN_MBALL; CENTRE_IN_MBALL];
   INTRO_TAC "A; !x; x" THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[REAL_LT_01; IN_MBALL];
    ASM_MESON_TAC[OPEN_IN_MTOPOLOGY; SUBSET]]]);;

let CONTINUOUS_ON_MDIST = prove
 (`!m a. a:A IN mspace m
         ==> continuous_map (mtopology m,euclideanreal) (\x. mdist m (a,x))`,
  INTRO_TAC "!m a; a" THEN
  REWRITE_TAC[GSYM MTOPOLOGY_REAL_EUCLIDEAN_METRIC;
              METRIC_CONTINUOUS_MAP;
              REAL_EUCLIDEAN_METRIC; IN_UNIV] THEN
  INTRO_TAC "![b] e; epos b" THEN EXISTS_TAC `e:real` THEN
  ASM_REWRITE_TAC[] THEN INTRO_TAC "!x; x dist" THEN
  REWRITE_TAC[continuous_map; TOPSPACE_EUCLIDEANREAL; IN_UNIV;
              TOPSPACE_MTOPOLOGY; GSYM REAL_OPEN_IN; OPEN_IN_MTOPOLOGY] THEN
  TRANS_TAC REAL_LET_TRANS `mdist m (b:A,x)` THEN
  HYP REWRITE_TAC "dist" [] THEN
  ASM_MESON_TAC[MDIST_REVERSE_TRIANGLE; MDIST_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Lipschitz functions.                                                      *)
(* ------------------------------------------------------------------------- *)

let LIPSCHITZ_COEFFICIENT_POS = prove
 (`!m m' f:A->B k.
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m' (f x,f y) <= k * mdist m (x,y)) /\
     (?x y. x IN mspace m /\ y IN mspace m /\ ~(f x = f y))
     ==> &0 < k`,
  REPEAT GEN_TAC THEN INTRO_TAC "f k (@x y. x y fneq)" THEN
  CLAIM_TAC "neq" `~(x:A = y)` THENL [HYP MESON_TAC "fneq" []; ALL_TAC] THEN
  TRANS_TAC REAL_LTE_TRANS `mdist m' (f x:B,f y) / mdist m (x:A,y)` THEN
  ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LE_LDIV_EQ]);;

let LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP = prove
 (`!m m' (f:A->B) k.
     (!x. x IN mspace m ==> f x IN mspace m') /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m' (f x,f y) <= k * mdist m (x,y))
     ==> continuous_map (mtopology m,mtopology m') f`,
  SIMP_TAC[METRIC_CONTINUOUS_MAP] THEN INTRO_TAC "! *; f lip; !a e; e a" THEN
  ASM_CASES_TAC `?y:A. y IN mspace m /\ ~(f a:B = f y)` THENL
  [EXISTS_TAC `e / k` THEN POP_ASSUM (DESTRUCT_TAC "@y. y neq") THEN
   CLAIM_TAC "kpos" `&0 < k` THENL
   [(MATCH_MP_TAC o ISPECL[`m:A metric`; `m':B metric`; `f:A->B`])
      LIPSCHITZ_COEFFICIENT_POS THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[REAL_LT_DIV] THEN INTRO_TAC "!x; x lt" THEN
    TRANS_TAC REAL_LET_TRANS `k * mdist m (a:A,x)` THEN ASM_SIMP_TAC[] THEN
    REMOVE_THEN "lt" MP_TAC THEN ASM_SIMP_TAC[REAL_LT_RDIV_EQ] THEN
    REWRITE_TAC[REAL_MUL_SYM]];
   POP_ASSUM
     (LABEL_TAC "eq" o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
   EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN
   INTRO_TAC "![y]; y d" THEN REMOVE_THEN "eq" (MP_TAC o SPEC `y:A`) THEN
   ASM_SIMP_TAC[MDIST_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Contractions.                                                             *)
(* ------------------------------------------------------------------------- *)

let CONTRACTION_IMP_UNIQUE_FIXPOINT = prove
 (`!m (f:A->A) k x y.
     k < &1 /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y)) /\
     x IN mspace m /\ y IN mspace m /\ f x = x /\ f y = y
     ==> x = y`,
  INTRO_TAC "!m f k x y; k f le x y xeq yeq" THEN
  ASM_CASES_TAC `x:A = y` THENL [POP_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  REMOVE_THEN "le" (MP_TAC o SPECL[`x:A`;`y:A`]) THEN ASM_REWRITE_TAC[] THEN
  CUT_TAC `&0 < (&1 - k) * mdist m (x:A,y:A)` THENL
  [REAL_ARITH_TAC;
   MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[MDIST_POS_LT] THEN
   ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Banach Fixed-Point Theorem (aka, Contraction Mapping Principle).          *)
(* ------------------------------------------------------------------------- *)

let BANACH_FIXPOINT_THM = prove
 (`!m f:A->A k.
     ~(mspace m = {}) /\
     mcomplete m /\
     (!x. x IN mspace m ==> f x IN mspace m) /\
     k < &1 /\
     (!x y. x IN mspace m /\ y IN mspace m
            ==> mdist m (f x, f y) <= k * mdist m (x,y))
     ==> (?!x. x IN mspace m /\ f x = x)`,
  INTRO_TAC "!m f k; ne compl 4 k1 contr" THEN REMOVE_THEN "ne" MP_TAC THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@a. aINm" THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
  [ALL_TAC;
   REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTRACTION_IMP_UNIQUE_FIXPOINT THEN
   ASM_MESON_TAC[]] THEN
  ASM_CASES_TAC `!x:A. x IN mspace m ==> f x:A = f a` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "nonsing")] THEN
  CLAIM_TAC "kpos" `&0 < k` THENL
  [MATCH_MP_TAC (ISPECL [`m:A metric`; `m:A metric`; `f:A->A`]
     LIPSCHITZ_COEFFICIENT_POS) THEN
   ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "fINm" `!n:num. (ITER n f (a:A)) IN mspace m` THENL
  [LABEL_INDUCT_TAC THEN ASM_SIMP_TAC[ITER]; ALL_TAC] THEN
  ASM_CASES_TAC `f a = a:A` THENL
  [ASM_MESON_TAC[]; POP_ASSUM (LABEL_TAC "aneq")] THEN
  CUT_TAC `cauchy_in (m:A metric) (\n. ITER n f (a:A))` THENL
  [DISCH_THEN (fun cauchy -> HYP_TAC "compl : @l. lim"
    (C MATCH_MP cauchy o REWRITE_RULE[mcomplete])) THEN
   EXISTS_TAC `l:A` THEN CONJ_TAC THENL
   [ASM_MESON_TAC [LIMIT_IN_MSPACE]; ALL_TAC] THEN
   MATCH_MP_TAC
     (ISPECL [`m:A metric`; `(\n. ITER n f a:A)`] LIMIT_METRIC_UNIQUE) THEN
   EXISTS_TAC `sequentially` THEN
   ASM_REWRITE_TAC[TRIVIAL_LIMIT_SEQUENTIALLY] THEN
   MATCH_MP_TAC LIMIT_SEQUENTIALLY_OFFSET_REV THEN
   EXISTS_TAC `1` THEN REWRITE_TAC[GSYM ADD1] THEN
   SUBGOAL_THEN `(\i. ITER (SUC i) f (a:A)) = f o (\i. ITER i f a)`
     SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; ITER]; ALL_TAC] THEN
   MATCH_MP_TAC CONTINUOUS_MAP_LIMIT THEN
   EXISTS_TAC `mtopology (m:A metric)` THEN ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC LIPSCHITZ_CONTINUOUS_IMP_CONTINUOUS_MAP THEN
   EXISTS_TAC `k:real` THEN ASM_REWRITE_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "k1'" `&0 < &1 - k` THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[cauchy_in] THEN INTRO_TAC "!e; e" THEN
  CLAIM_TAC "@N. N" `?N. k pow N < ((&1 - k) * e) / mdist m (a:A,f a)` THENL
  [MATCH_MP_TAC REAL_ARCH_POW_INV THEN
   ASM_SIMP_TAC[REAL_LT_DIV; MDIST_POS_LT; REAL_LT_MUL];
   EXISTS_TAC `N:num`] THEN
  MATCH_MP_TAC WLOG_LT THEN ASM_SIMP_TAC[MDIST_REFL] THEN CONJ_TAC THENL
  [HYP MESON_TAC "fINm" [MDIST_SYM]; ALL_TAC] THEN
  INTRO_TAC "!n n'; lt; le le'" THEN
  TRANS_TAC REAL_LET_TRANS
    `sum (n..n'-1) (\i. mdist m (ITER i f a:A, ITER (SUC i) f a))` THEN
  CONJ_TAC THENL
  [REMOVE_THEN "lt" MP_TAC THEN SPEC_TAC (`n':num`,`n':num`) THEN
   LABEL_INDUCT_TAC THENL [REWRITE_TAC[LT]; REWRITE_TAC[LT_SUC_LE]] THEN
   INTRO_TAC "nle" THEN HYP_TAC "nle : nlt | neq" (REWRITE_RULE[LE_LT]) THENL
   [ALL_TAC;
    POP_ASSUM SUBST_ALL_TAC THEN
    REWRITE_TAC[ITER;
      ARITH_RULE `SUC n'' - 1 = n''`; SUM_SING_NUMSEG; REAL_LE_REFL]] THEN
   USE_THEN "nlt" (HYP_TAC "ind_n'" o C MATCH_MP) THEN REWRITE_TAC[ITER] THEN
   TRANS_TAC REAL_LE_TRANS
     `mdist m (ITER n f a:A,ITER n'' f a) +
      mdist m (ITER n'' f a,f (ITER n'' f a))` THEN
   ASM_SIMP_TAC[MDIST_TRIANGLE] THEN
   SUBGOAL_THEN `SUC n'' - 1 = SUC (n'' - 1)` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[SUM_CLAUSES_NUMSEG]] THEN
   SUBGOAL_THEN `SUC (n'' - 1) = n''` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_SIMP_TAC[LT_IMP_LE; REAL_LE_RADD]] THEN
   REMOVE_THEN "ind_n'" (ACCEPT_TAC o REWRITE_RULE[ITER]);
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
     `sum (n..n'-1) (\i. mdist m (a:A, f a) * k pow i)` THEN CONJ_TAC THENL
  [MATCH_MP_TAC SUM_LE_NUMSEG THEN
   CUT_TAC `!i. mdist m (ITER i f a,ITER (SUC i) f a) <=
                mdist m (a:A,f a) * k pow i` THENL
   [SIMP_TAC[ITER]; ALL_TAC] THEN
   LABEL_INDUCT_TAC THENL
   [REWRITE_TAC[ITER; real_pow; REAL_MUL_RID; REAL_LE_REFL];
    HYP_TAC "ind_i" (REWRITE_RULE[ITER]) THEN
    TRANS_TAC REAL_LE_TRANS `k * mdist m (ITER i f a:A, f (ITER i f a))` THEN
    ASM_SIMP_TAC[real_pow; REAL_LE_LMUL_EQ; ITER;
      REAL_ARITH `!x. x * k * k pow i = k * x * k pow i`]];
   ALL_TAC] THEN
  REWRITE_TAC[SUM_LMUL; SUM_GP] THEN
  HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> ~(n' - 1 < n)`] THEN
  HYP SIMP_TAC "k1" [REAL_ARITH `k < &1 ==> ~(k = &1)`] THEN
  USE_THEN "lt" (SUBST1_TAC o
    MATCH_MP (ARITH_RULE `n < n' ==> SUC (n' - 1) = n'`)) THEN
  SUBGOAL_THEN `k pow n - k pow n' = k pow n * (&1 - k pow (n' - n))`
    SUBST1_TAC THENL
  [REWRITE_TAC[REAL_SUB_LDISTRIB; REAL_MUL_RID; GSYM REAL_POW_ADD] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> n + n' - n = n':num`];
   (SUBST1_TAC o REAL_ARITH)
     `mdist m (a:A,f a) * (k pow n * (&1 - k pow (n' - n))) / (&1 - k) =
      ((k pow n * (&1 - k pow (n' - n))) / (&1 - k)) * mdist m (a,f a)`] THEN
  ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ; MDIST_POS_LT; REAL_LT_LDIV_EQ] THEN
  TRANS_TAC REAL_LET_TRANS `k pow n` THEN CONJ_TAC THENL
  [ONCE_REWRITE_TAC[GSYM REAL_SUB_LE] THEN
   REWRITE_TAC[GSYM REAL_POW_ADD;
     REAL_ARITH `k pow n - k pow n * (&1 - k pow (n' - n)) =
                 k pow n * k pow (n' - n)`] THEN
   HYP SIMP_TAC "lt" [ARITH_RULE `n < n' ==> n + n' - n = n':num`] THEN
   HYP SIMP_TAC "kpos" [REAL_POW_LE; REAL_LT_IMP_LE];
   TRANS_TAC REAL_LET_TRANS `k pow N` THEN
   ASM_SIMP_TAC[REAL_POW_MONO_INV; REAL_LT_IMP_LE;
     REAL_ARITH `e / mdist m (a:A,f a) * (&1 - k) =
                 ((&1 - k) * e) / mdist m (a,f a)`]]);;

(* ------------------------------------------------------------------------- *)
(* Metric space of bounded functions.                                        *)
(* ------------------------------------------------------------------------- *)

let funspace = new_definition
  `funspace s m =
   metric ({f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                     f IN EXTENSIONAL s /\
                     mbounded m (IMAGE f s)},
           (\(f,g). if s = {} then &0 else
                    sup {mdist m (f x,g x) | x | x IN s}))`;;

let FUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] o prove)
 (`!s m.
     mspace (funspace s m) =
       {f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                 f IN EXTENSIONAL s /\
                 mbounded m (IMAGE f s)} /\
     (!f g. mdist (funspace s m) (f,g) =
              if s = {} then &0 else
              sup {mdist m (f x,g x) | x | x IN s})`,
  REPEAT GEN_TAC THEN MAP_EVERY LABEL_ABBREV_TAC
    [`fspace = {f:A->B | (!x. x IN s ==> f x IN mspace m) /\
                         f IN EXTENSIONAL s /\
                         mbounded m (IMAGE f s)}`;
     `fdist =
        \(f,g). if s = {} then &0 else
                sup {mdist m (f x:B,g x) | x | x:A IN s}`] THEN
  CUT_TAC `mspace (funspace s m) = fspace:(A->B)->bool /\
           mdist (funspace s m:(A->B)metric) = fdist` THENL
  [EXPAND_TAC "fdist" THEN DISCH_THEN (fun th -> REWRITE_TAC[th]);
   ASM_REWRITE_TAC[funspace] THEN MATCH_MP_TAC METRIC] THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN MAP_EVERY EXPAND_TAC ["fspace"; "fdist"] THEN
   SIMP_TAC[is_metric_space; NOT_IN_EMPTY; IN_EXTENSIONAL; IMAGE_CLAUSES;
     MBOUNDED_EMPTY; IN_ELIM_THM; REAL_LE_REFL; REAL_ADD_LID; FUN_EQ_THM];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REMOVE_THEN "nempty" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN LABEL_TAC "nempty" th) THEN
  CLAIM_TAC "wd ext bound"
    `(!f x:A. f IN fspace /\ x IN s ==> f x:B IN mspace m) /\
     (!f. f IN fspace ==> f IN EXTENSIONAL s) /\
     (!f. f IN fspace
          ==> (?c b. c IN mspace m /\
                     (!x. x IN s ==> mdist m (c,f x) <= b)))` THENL
  [EXPAND_TAC "fspace" THEN
   ASM_SIMP_TAC[IN_ELIM_THM; MBOUNDED; IMAGE_EQ_EMPTY] THEN SET_TAC[];
   ALL_TAC] THEN
  CLAIM_TAC "bound2"
    `!f g:A->B. f IN fspace /\ g IN fspace
                ==> (?b. !x. x IN s ==> mdist m (f x,g x) <= b)` THENL
  [REMOVE_THEN "fspace" (SUBST_ALL_TAC o GSYM) THEN
   REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
   CUT_TAC `mbounded m (IMAGE (f:A->B) s UNION IMAGE g s)` THENL
   [REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBSET; IN_UNION] THEN
    STRIP_TAC THEN EXISTS_TAC `b:real` THEN ASM SET_TAC [];
    ASM_REWRITE_TAC[MBOUNDED_UNION]];
   ALL_TAC] THEN
  HYP_TAC "nempty -> @a. a" (REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[is_metric_space] THEN CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_SUP THEN
   CLAIM_TAC "@b. b" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f(a:A):B,g a)`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN HYP SIMP_TAC "wd f g a" [MDIST_POS_LE] THEN
    HYP MESON_TAC "a b" [];
    ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f  g" THEN EXPAND_TAC "fdist" THEN
   REWRITE_TAC[] THEN EQ_TAC THENL
   [INTRO_TAC "sup0" THEN MATCH_MP_TAC (SPEC `s:A->bool` EXTENSIONAL_EQ) THEN
    HYP SIMP_TAC "f g ext" [] THEN INTRO_TAC "!x; x" THEN
    REFUTE_THEN (LABEL_TAC "neq") THEN
    CUT_TAC
      `&0 < mdist m (f (x:A):B, g x) /\
       mdist m (f x, g x) <= sup {mdist m (f x,g x) | x IN s}` THENL
    [HYP REWRITE_TAC "sup0" [] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    HYP SIMP_TAC "wd f g x neq" [MDIST_POS_LT] THEN
    MATCH_MP_TAC REAL_LE_SUP THEN
    CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
    [HYP SIMP_TAC "bound2 f g" []; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (f (x:A):B,g x)`] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
    HYP MESON_TAC "B x" [];
    DISCH_THEN (SUBST1_TAC o GSYM) THEN
    SUBGOAL_THEN `{mdist m (f x:B,f x) | x:A IN s} = {&0}`
      (fun th -> REWRITE_TAC[th; SUP_SING]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV; IN_INSERT] THEN
    HYP MESON_TAC "wd f a" [MDIST_REFL]];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [INTRO_TAC "![f] [g]; f g" THEN EXPAND_TAC "fdist" THEN REWRITE_TAC[] THEN
   AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   HYP MESON_TAC "wd f g" [MDIST_SYM];
   ALL_TAC] THEN
  INTRO_TAC "![f] [g] [h]; f g h" THEN EXPAND_TAC "fdist" THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC REAL_SUP_LE THEN CONJ_TAC THENL
  [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY; IN_UNIV] THEN
   HYP MESON_TAC "a" [];
   ALL_TAC] THEN
  FIX_TAC "[d]" THEN REWRITE_TAC [IN_ELIM_THM; IN_UNIV] THEN
  INTRO_TAC "@x. x d" THEN POP_ASSUM SUBST1_TAC THEN
  CUT_TAC
    `mdist m (f (x:A):B,h x) <= mdist m (f x,g x) + mdist m (g x, h x) /\
     mdist m (f x, g x) <= fdist (f,g) /\
     mdist m (g x, h x) <= fdist (g,h)` THEN
  EXPAND_TAC "fdist" THEN REWRITE_TAC[] THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  HYP SIMP_TAC "wd f g h x" [MDIST_TRIANGLE] THEN
  CONJ_TAC THEN MATCH_MP_TAC REAL_LE_SUP THENL
  [CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (f x:B,g x) <= b` THENL
   [HYP SIMP_TAC "bound2 f g" [];
    MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (f(x:A):B,g x)`]] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN HYP MESON_TAC "B x" [];
   CLAIM_TAC "@B. B" `?b. !x:A. x IN s ==> mdist m (g x:B,h x) <= b` THENL
   [HYP SIMP_TAC "bound2 g h" []; ALL_TAC] THEN
   MAP_EVERY EXISTS_TAC [`B:real`; `mdist m (g(x:A):B,h x)`] THEN
   REWRITE_TAC[IN_ELIM_THM; IN_UNIV; REAL_LE_REFL] THEN
   HYP MESON_TAC "B x" []]);;

let FUNSPACE_IMP_WELLDEFINED = prove
 (`!s m f:A->B x. f IN mspace (funspace s m) /\ x IN s ==> f x IN mspace m`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_EXTENSIONAL = prove
 (`!s m f:A->B. f IN mspace (funspace s m) ==> f IN EXTENSIONAL s`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_BOUNDED_IMAGE = prove
 (`!s m f:A->B. f IN mspace (funspace s m) ==> mbounded m (IMAGE f s)`,
  SIMP_TAC[FUNSPACE; IN_ELIM_THM]);;

let FUNSPACE_IMP_BOUNDED = prove
 (`!s m f:A->B. f IN mspace (funspace s m)
                ==> s = {} \/ (?c b. !x. x IN s ==> mdist m (c,f x) <= b)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[FUNSPACE; MBOUNDED; IMAGE_EQ_EMPTY; IN_ELIM_THM] THEN
  ASM_CASES_TAC `s:A->bool = {}` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let FUNSPACE_IMP_BOUNDED2 = prove
 (`!s m f g:A->B. f IN mspace (funspace s m) /\ g IN mspace (funspace s m)
                  ==> (?b. !x. x IN s ==> mdist m (f x,g x) <= b)`,
  REWRITE_TAC[FUNSPACE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  CUT_TAC `mbounded m (IMAGE (f:A->B) s UNION IMAGE g s)` THENL
  [REWRITE_TAC[MBOUNDED_IFF_FINITE_DIAMETER; SUBSET; IN_UNION] THEN
   STRIP_TAC THEN EXISTS_TAC `b:real` THEN ASM SET_TAC [];
   ASM_REWRITE_TAC[MBOUNDED_UNION]]);;

let FUNSPACE_MDIST_LE = prove
 (`!s m f g:A->B a.
     ~(s = {}) /\
     f IN mspace (funspace s m) /\
     g IN mspace (funspace s m)
     ==> (mdist (funspace s m) (f,g) <= a <=>
          !x. x IN s ==> mdist m (f x, g x) <= a)`,
  INTRO_TAC "! *; ne f g" THEN
  HYP (DESTRUCT_TAC "@b. b" o
    MATCH_MP FUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
  ASM_REWRITE_TAC[FUNSPACE] THEN
  MP_TAC (ISPECL [`{mdist m (f x:B,g x) | x:A IN s}`; `a:real`]
    REAL_SUP_LE_EQ) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[IN_ELIM_THM]] THEN
  MESON_TAC[]);;

let MCOMPLETE_FUNSPACE = prove
 (`!s:A->bool m:B metric. mcomplete m ==> mcomplete (funspace s m)`,
  REWRITE_TAC[mcomplete] THEN INTRO_TAC "!s m; cpl; ![f]; cy" THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
  [POP_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `\x:A. UNDEFINED:B` THEN
   REMOVE_THEN "cy" MP_TAC THEN
   SIMP_TAC[cauchy_in; LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; NOT_IN_EMPTY;
     IN_ELIM_THM; IN_EXTENSIONAL; IMAGE_CLAUSES; MBOUNDED_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  LABEL_ABBREV_TAC
    `g (x:A) = if x IN s
               then @y. limit (mtopology m) (\n:num. f n x) y sequentially
               else UNDEFINED:B` THEN
  EXISTS_TAC `g:A->B` THEN USE_THEN "cy" MP_TAC THEN
  HYP REWRITE_TAC "nempty"
    [cauchy_in; FUNSPACE; IN_ELIM_THM; FORALL_AND_THM] THEN
  INTRO_TAC "(fwd fext fbd) cy'" THEN
  ASM_REWRITE_TAC[LIMIT_METRIC_SEQUENTIALLY; FUNSPACE; IN_ELIM_THM] THEN
  CLAIM_TAC "gext" `g:A->B IN EXTENSIONAL s` THENL
  [REMOVE_THEN "g" (fun th -> SIMP_TAC[IN_EXTENSIONAL; GSYM th]);
   HYP REWRITE_TAC "gext" []] THEN
  CLAIM_TAC "bd2"
     `!n n'. ?b. !x:A. x IN s ==> mdist m (f (n:num) x:B, f n' x) <= b` THENL
  [REPEAT GEN_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
   ASM_REWRITE_TAC[FUNSPACE; IN_ELIM_THM; ETA_AX];
   ALL_TAC] THEN
  CLAIM_TAC "sup"
    `!n n':num x0:A. x0 IN s
                     ==> mdist m (f n x0:B,f n' x0) <=
                         sup {mdist m (f n x,f n' x) | x IN s}` THENL
  [INTRO_TAC "!n n' x0; x0" THEN MATCH_MP_TAC REAL_LE_SUP THEN
   REMOVE_THEN "bd2" (DESTRUCT_TAC "@b. b" o SPECL[`n:num`;`n':num`]) THEN
   MAP_EVERY EXISTS_TAC
     [`b:real`; `mdist m (f (n:num) (x0:A):B, f n' x0)`] THEN
   REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [HYP MESON_TAC "x0" []; REWRITE_TAC[REAL_LE_REFL]] THEN
   INTRO_TAC "![d]; @y. y d" THEN REMOVE_THEN "d" SUBST1_TAC THEN
   HYP SIMP_TAC "b y" [];
   ALL_TAC] THEN
  CLAIM_TAC "pcy" `!x:A. x IN s ==> cauchy_in m (\n. f n x:B)` THENL
  [INTRO_TAC "!x; x" THEN REWRITE_TAC[cauchy_in] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "!e; e" THEN
   USE_THEN "e" (HYP_TAC "cy': @N.N" o C MATCH_MP) THEN EXISTS_TAC `N:num` THEN
   REPEAT GEN_TAC THEN DISCH_THEN (HYP_TAC "N" o C MATCH_MP) THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f (n:num) x:B,f n' x) | x:A IN s}` THEN
   HYP REWRITE_TAC "N" [] THEN HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CLAIM_TAC "glim"
    `!x:A. x IN s
           ==> limit (mtopology m) (\n. f n x:B) (g x) sequentially` THENL
  [INTRO_TAC "!x; x" THEN
   REMOVE_THEN "g" (fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
   SELECT_ELIM_TAC THEN HYP SIMP_TAC "cpl pcy x" [];
   ALL_TAC] THEN
  CLAIM_TAC "gwd" `!x:A. x IN s ==> g x:B IN mspace m` THENL
  [INTRO_TAC "!x; x" THEN
   MATCH_MP_TAC (ISPECL[`sequentially`] LIMIT_IN_MSPACE) THEN
   EXISTS_TAC `\n:num. f n (x:A):B` THEN HYP SIMP_TAC "glim x" [];
   HYP REWRITE_TAC "gwd" []] THEN
  CLAIM_TAC "unif"
    `!e. &0 < e ==> ?N:num. !x:A n. x IN s /\ N <= n
                    ==> mdist m (f n x:B, g x) < e` THENL
  [INTRO_TAC "!e; e" THEN REMOVE_THEN "cy'" (MP_TAC o SPEC `e / &2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
   EXISTS_TAC `N:num` THEN INTRO_TAC "!x n; x n" THEN
   USE_THEN "x" (HYP_TAC "glim" o C MATCH_MP) THEN
   HYP_TAC "glim: gx glim" (REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   REMOVE_THEN "glim" (MP_TAC o SPEC `e / &2`) THEN
   HYP REWRITE_TAC "e" [REAL_HALF] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   TRANS_TAC REAL_LET_TRANS
     `mdist m (f n (x:A):B, f (MAX N N') x) +
      mdist m (f (MAX N N') x, g x)` THEN
   HYP SIMP_TAC "fwd x gwd" [MDIST_TRIANGLE] THEN
   TRANS_TAC REAL_LTE_TRANS `e / &2 + e / &2` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_ADD2; REWRITE_TAC[REAL_HALF; REAL_LE_REFL]] THEN
   CONJ_TAC THENL [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f n x:B,f (MAX N N') x) | x:A IN s}` THEN
   HYP SIMP_TAC "N n" [ARITH_RULE `N <= MAX N N'`] THEN
   HYP SIMP_TAC "sup x" [];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [HYP_TAC "cy': @N. N" (C MATCH_MP REAL_LT_01) THEN
   USE_THEN "fbd" (MP_TAC o REWRITE_RULE[MBOUNDED] o SPEC `N:num`) THEN
   HYP REWRITE_TAC "nempty" [mbounded; IMAGE_EQ_EMPTY] THEN
   INTRO_TAC "Nwd (@c b. c Nbd)" THEN
   MAP_EVERY EXISTS_TAC [`c:B`; `b + &1`] THEN
   REWRITE_TAC[SUBSET; IN_IMAGE; IN_MCBALL] THEN
   INTRO_TAC "![y]; (@x. y x)" THEN REMOVE_THEN "y" SUBST1_TAC THEN
   HYP SIMP_TAC "x gwd c" [] THEN TRANS_TAC REAL_LE_TRANS
     `mdist m (c:B, f (N:num) (x:A)) + mdist m (f N x, g x)` THEN
   HYP SIMP_TAC "c fwd gwd x" [MDIST_TRIANGLE] THEN
   MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
   [REMOVE_THEN "Nbd" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
    HYP MESON_TAC "x" [];
    REFUTE_THEN (LABEL_TAC "contra" o REWRITE_RULE[REAL_NOT_LE])] THEN
   CLAIM_TAC "@a. a1 a2"
     `?a. &1 < a /\ a < mdist m (f (N:num) (x:A), g x:B)` THENL
   [EXISTS_TAC `(&1 + mdist m (f (N:num) (x:A), g x:B)) / &2` THEN
    REMOVE_THEN "contra" MP_TAC THEN REAL_ARITH_TAC;
    USE_THEN "x" (HYP_TAC "glim" o C MATCH_MP)] THEN
   REMOVE_THEN "glim" (MP_TAC o REWRITE_RULE[LIMIT_METRIC_SEQUENTIALLY]) THEN
   HYP SIMP_TAC "gwd x" [] THEN DISCH_THEN (MP_TAC o SPEC `a - &1`) THEN
   ANTS_TAC THENL [REMOVE_THEN "a1" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   HYP SIMP_TAC "fwd x" [] THEN INTRO_TAC "@N'. N'" THEN
   CUT_TAC `mdist m (f (N:num) (x:A), g x:B) < a` THENL
   [REMOVE_THEN "a2" MP_TAC THEN REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `mdist m (f N (x:A),f (MAX N N') x:B) + mdist m (f (MAX N N') x,g x)` THEN
   HYP SIMP_TAC "fwd gwd x" [MDIST_TRIANGLE] THEN
   SUBST1_TAC (REAL_ARITH `a = &1 + (a - &1)`) THEN
   MATCH_MP_TAC REAL_LT_ADD2 THEN CONJ_TAC THENL
   [ALL_TAC; REMOVE_THEN "N'" MATCH_MP_TAC THEN ARITH_TAC] THEN
   TRANS_TAC REAL_LET_TRANS
     `sup {mdist m (f N x:B,f (MAX N N') x) | x:A IN s}` THEN
   CONJ_TAC THENL
   [HYP SIMP_TAC "sup x" []; REMOVE_THEN "N" MATCH_MP_TAC THEN ARITH_TAC];
   ALL_TAC] THEN
  INTRO_TAC "!e; e" THEN REMOVE_THEN "unif" (MP_TAC o SPEC `e / &2`) THEN
  HYP REWRITE_TAC "e" [REAL_HALF] THEN INTRO_TAC "@N. N" THEN
  EXISTS_TAC `N:num` THEN INTRO_TAC "!n; n" THEN
  TRANS_TAC REAL_LET_TRANS `e / &2` THEN CONJ_TAC THENL
  [ALL_TAC; REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC] THEN
  MATCH_MP_TAC REAL_SUP_LE THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
  [HYP SET_TAC "nempty" []; HYP MESON_TAC "N n" [REAL_LT_IMP_LE]]);;

(* ------------------------------------------------------------------------- *)
(* Metric space of continuous bounded functions.                             *)
(* ------------------------------------------------------------------------- *)

let cfunspace = new_definition
  `cfunspace top m =
   submetric (funspace (topspace top) m)
     {f:A->B | continuous_map (top,mtopology m) f}`;;

let CFUNSPACE = (REWRITE_RULE[GSYM FORALL_AND_THM] o prove)
 (`(!top m.
      mspace (cfunspace top m) =
      {f:A->B | (!x. x IN topspace top ==> f x IN mspace m) /\
                f IN EXTENSIONAL (topspace top) /\
                mbounded m (IMAGE f (topspace top)) /\
                continuous_map (top,mtopology m) f}) /\
     (!f g:A->B.
        mdist (cfunspace top m) (f,g) =
        if topspace top = {} then &0 else
        sup {mdist m (f x,g x) | x IN topspace top})`,
  REWRITE_TAC[cfunspace; SUBMETRIC; FUNSPACE] THEN SET_TAC[]);;

let CFUNSPACE_SUBSET_FUNSPACE = prove
 (`!top:A topology m:B metric.
     mspace (cfunspace top m) SUBSET mspace (funspace (topspace top) m)`,
  SIMP_TAC[SUBSET; FUNSPACE; CFUNSPACE; IN_ELIM_THM]);;

let MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE = prove
 (`!top m f g:A->B.
     mdist (cfunspace top m) (f,g) = mdist (funspace (topspace top) m) (f,g)`,
  REWRITE_TAC[FUNSPACE; CFUNSPACE]);;

let CFUNSPACE_MDIST_LE = prove
 (`!top m f g:A->B a.
     ~(topspace top = {}) /\
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m)
     ==> (mdist (cfunspace top m) (f,g) <= a <=>
          !x. x IN topspace top ==> mdist m (f x, g x) <= a)`,
  INTRO_TAC "! *; ne f g" THEN
  REWRITE_TAC[MDIST_CFUNSPACE_EQ_MDIST_FUNSPACE] THEN
  MATCH_MP_TAC FUNSPACE_MDIST_LE THEN
  ASM_SIMP_TAC[REWRITE_RULE[SUBSET] CFUNSPACE_SUBSET_FUNSPACE]);;

let CFUNSPACE_IMP_BOUNDED2 = prove
 (`!top m f g:A->B.
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m)
     ==> (?b. !x. x IN topspace top ==> mdist m (f x,g x) <= b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FUNSPACE_IMP_BOUNDED2 THEN
  ASM SET_TAC [CFUNSPACE_SUBSET_FUNSPACE]);;

let CFUNSPACE_MDIST_LT = prove
 (`!top m f g:A->B a x.
     compact_in top (topspace top) /\
     f IN mspace (cfunspace top m) /\ g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f, g) < a /\
     x IN topspace top
     ==> mdist m (f x, g x) < a`,
  REPEAT GEN_TAC THEN ASM_CASES_TAC `topspace (top:A topology) = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN INTRO_TAC "cpt f g lt x" THEN
  REMOVE_THEN "lt" MP_TAC THEN ASM_REWRITE_TAC[CFUNSPACE] THEN
  INTRO_TAC "lt" THEN
  TRANS_TAC REAL_LET_TRANS
    `sup {mdist m (f x:B,g x) | x:A IN topspace top}` THEN
  HYP SIMP_TAC "lt" [] THEN  MATCH_MP_TAC REAL_LE_SUP THEN
  HYP (DESTRUCT_TAC "@b. b" o
    MATCH_MP CFUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
  MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f (x:A):B,g x)`] THEN
  REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN HYP MESON_TAC "x b" []);;

let MDIST_CFUNSPACE_LE = prove
 (`!top m B f g.
     &0 <= B /\
     (!x:A. x IN topspace top ==> mdist m (f x:B, g x) <= B)
     ==> mdist (cfunspace top m) (f,g) <= B`,
  INTRO_TAC "!top m B f g; Bpos bound" THEN
  REWRITE_TAC[CFUNSPACE] THEN COND_CASES_TAC THEN
  HYP REWRITE_TAC "Bpos" [] THEN MATCH_MP_TAC REAL_SUP_LE THEN
  CONJ_TAC THENL
  [POP_ASSUM MP_TAC THEN SET_TAC[];
   REWRITE_TAC[IN_ELIM_THM] THEN HYP MESON_TAC "bound" []]);;

let MDIST_CFUNSPACE_IMP_MDIST_LE = prove
 (`!top m f g:A->B a x.
     f IN mspace (cfunspace top m) /\
     g IN mspace (cfunspace top m) /\
     mdist (cfunspace top m) (f,g) <= a /\
     x IN topspace top
     ==> mdist m (f x,g x) <= a`,
  MESON_TAC[MEMBER_NOT_EMPTY; CFUNSPACE_MDIST_LE]);;

let COMPACT_IN_MSPACE_CFUNSPACE = prove
 (`!top m.
     compact_in top (topspace top)
     ==> mspace (cfunspace top m) =
          {f | (!x:A. x IN topspace top ==> f x:B IN mspace m) /\
               f IN EXTENSIONAL (topspace top) /\
               continuous_map (top,mtopology m) f}`,
  REWRITE_TAC[CFUNSPACE; EXTENSION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  EQ_TAC THEN SIMP_TAC[] THEN INTRO_TAC "wd ext cont" THEN
  MATCH_MP_TAC COMPACT_IN_IMP_MBOUNDED THEN
  MATCH_MP_TAC (ISPEC `top:A topology` IMAGE_COMPACT_IN) THEN
  ASM_REWRITE_TAC[]);;

let MCOMPLETE_CFUNSPACE = prove
 (`!top:A topology m:B metric. mcomplete m ==> mcomplete (cfunspace top m)`,
  INTRO_TAC "!top m; cpl" THEN REWRITE_TAC[cfunspace] THEN
  MATCH_MP_TAC SEQUENTIALLY_CLOSED_IN_MCOMPLETE_IMP_MCOMPLETE THEN
  ASM_SIMP_TAC[MCOMPLETE_FUNSPACE] THEN
  REWRITE_TAC[IN_ELIM_THM; LIMIT_METRIC_SEQUENTIALLY] THEN
  INTRO_TAC "![f] [g]; fcont g lim" THEN
  ASM_CASES_TAC `topspace top = {}:A->bool` THENL
  [ASM_REWRITE_TAC[continuous_map; NOT_IN_EMPTY; EMPTY_GSPEC; OPEN_IN_EMPTY];
   POP_ASSUM (LABEL_TAC "nempty")] THEN
  REWRITE_TAC[CONTINUOUS_MAP_TO_METRIC; IN_MBALL] THEN
  INTRO_TAC "!x; x; ![e]; e" THEN CLAIM_TAC "e3pos" `&0 < e / &3` THENL
  [REMOVE_THEN "e" MP_TAC THEN REAL_ARITH_TAC;
   USE_THEN "e3pos" (HYP_TAC "lim: @N. N" o C MATCH_MP)] THEN
  HYP_TAC "N: f lt" (C MATCH_MP (SPEC `N:num` LE_REFL)) THEN
  HYP_TAC "fcont" (REWRITE_RULE[CONTINUOUS_MAP_TO_METRIC]) THEN
  USE_THEN "x" (HYP_TAC "fcont" o C MATCH_MP) THEN
  USE_THEN "e3pos" (HYP_TAC "fcont" o C MATCH_MP) THEN
  HYP_TAC "fcont: @u. u x' inc" (SPEC `N:num`) THEN EXISTS_TAC `u:A->bool` THEN
  HYP REWRITE_TAC "u x'" [] THEN INTRO_TAC "!y; y'" THEN
  CLAIM_TAC "uinc" `!x:A. x IN u ==> x IN topspace top` THENL
  [REMOVE_THEN "u" (MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN SET_TAC[];
   ALL_TAC] THEN
  HYP_TAC "g -> gwd gext gbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  HYP_TAC "f -> fwd fext fbd" (REWRITE_RULE[FUNSPACE; IN_ELIM_THM]) THEN
  CLAIM_TAC "y" `y:A IN topspace top` THENL
  [HYP SIMP_TAC "uinc y'" [OPEN_IN_SUBSET]; HYP SIMP_TAC "gwd x y" []] THEN
  CLAIM_TAC "sup" `!x0:A. x0 IN topspace top
                          ==> mdist m (f (N:num) x0:B,g x0) <= e / &3` THENL
  [INTRO_TAC "!x0; x0" THEN TRANS_TAC REAL_LE_TRANS
     `sup {mdist m (f (N:num) x,g x:B) | x:A IN topspace top}` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_SUP THEN HYP (DESTRUCT_TAC "@b. b" o
      MATCH_MP FUNSPACE_IMP_BOUNDED2 o CONJ_LIST) "f g" [] THEN
    MAP_EVERY EXISTS_TAC [`b:real`; `mdist m (f (N:num) (x0:A), g x0:B)`] THEN
    REWRITE_TAC[IN_ELIM_THM; REAL_LE_REFL] THEN
    CONJ_TAC THENL [HYP SET_TAC "x0" []; HYP MESON_TAC "b" []];
    REMOVE_THEN "lt" MP_TAC THEN HYP REWRITE_TAC "nempty" [FUNSPACE] THEN
    MATCH_ACCEPT_TAC REAL_LT_IMP_LE];
   ALL_TAC] THEN
  TRANS_TAC REAL_LET_TRANS
    `mdist m (g (x:A):B, f (N:num) x) + mdist m (f N x, g y)` THEN
  HYP SIMP_TAC "gwd fwd x y" [MDIST_TRIANGLE] THEN
  SUBST1_TAC (ARITH_RULE `e = e / &3 + (e / &3 + e / &3)`) THEN
  MATCH_MP_TAC REAL_LET_ADD2 THEN HYP SIMP_TAC "gwd fwd x sup" [MDIST_SYM] THEN
  TRANS_TAC REAL_LET_TRANS
    `mdist m (f (N:num) (x:A):B, f N y) + mdist m (f N y, g y)` THEN
  HYP SIMP_TAC "fwd gwd x y" [MDIST_TRIANGLE] THEN
  MATCH_MP_TAC REAL_LTE_ADD2 THEN HYP SIMP_TAC "gwd fwd y sup" [] THEN
  REMOVE_THEN "inc" MP_TAC THEN HYP SIMP_TAC "fwd x y' uinc" [IN_MBALL]);;

(* ------------------------------------------------------------------------- *)
(* The Baire Category theorem for complete metric spaces.                    *)
(* ------------------------------------------------------------------------- *)

let METRIC_BAIRE_CATEGORY = prove
 (`!m:A metric g.
     mcomplete m /\
     COUNTABLE g /\
     (!t. t IN g ==> open_in (mtopology m) t /\
                     mtopology m closure_of t = mspace m)
     ==> mtopology m closure_of INTERS g = mspace m`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN INTRO_TAC "!m; m" THEN
  REWRITE_TAC[FORALL_COUNTABLE_AS_IMAGE; NOT_IN_EMPTY; CLOSURE_OF_UNIV;
  INTERS_0; TOPSPACE_MTOPOLOGY; FORALL_IN_IMAGE; IN_UNIV; FORALL_AND_THM] THEN
  INTRO_TAC "![u]; u_open u_dense" THEN
  REWRITE_TAC[GSYM TOPSPACE_MTOPOLOGY] THEN
  REWRITE_TAC[DENSE_INTERSECTS_OPEN] THEN
  INTRO_TAC "![w]; w_open w_ne" THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  CLAIM_TAC "@x0. x0" `?x0:A. x0 IN u 0 INTER w` THENL
  [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
   ASM_MESON_TAC[DENSE_INTERSECTS_OPEN; TOPSPACE_MTOPOLOGY];
   ALL_TAC] THEN
  CLAIM_TAC "@r0. r0pos r0lt1 sub"
    `?r. &0 < r /\ r < &1 /\ mcball m (x0:A,r) SUBSET u 0 INTER w` THENL
  [SUBGOAL_THEN `open_in (mtopology m) (u 0 INTER w:A->bool)` MP_TAC THENL
   [HYP SIMP_TAC "u_open w_open" [OPEN_IN_INTER]; ALL_TAC] THEN
   REWRITE_TAC[OPEN_IN_MTOPOLOGY] THEN INTRO_TAC "u0w hp" THEN
   REMOVE_THEN "hp" (MP_TAC o SPEC `x0:A`) THEN
   ANTS_TAC THENL [HYP REWRITE_TAC "x0" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r (&1) / &2` THEN
   CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mball m (x0:A,r)` THEN
   HYP REWRITE_TAC "ball" [] THEN
   MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN
   ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (DESTRUCT_TAC "@b. b0 b1" o prove_general_recursive_function_exists)
    `?b:num->(A#real).
       b 0 = (x0:A,r0) /\
       (!n. b (SUC n) =
            @(x,r). &0 < r /\ r < SND (b n) / &2 /\ x IN mspace m /\
                    mcball m (x,r) SUBSET mball m (b n) INTER u n)` THEN
  CLAIM_TAC "rmk"
    `!n. (\ (x:A,r). &0 < r /\ r < SND (b n) / &2 /\ x IN mspace m /\
                   mcball m (x,r) SUBSET mball m (b n) INTER u n)
         (b (SUC n))` THENL
  [LABEL_INDUCT_TAC THENL
   [REMOVE_THEN "b1" (fun b1 -> REWRITE_TAC[b1]) THEN
    MATCH_MP_TAC CHOICE_PAIRED_THM THEN
    REMOVE_THEN "b0" (fun b0 -> REWRITE_TAC[b0]) THEN
    MAP_EVERY EXISTS_TAC [`x0:A`; `r0 / &4`] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
    [CUT_TAC `u 0:A->bool SUBSET mspace m` THENL
     [HYP SET_TAC "x0" [];
      HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
     ALL_TAC] THEN
    TRANS_TAC SUBSET_TRANS `mball m (x0:A,r0)` THEN CONJ_TAC THENL
    [MATCH_MP_TAC MCBALL_SUBSET_MBALL_CONCENTRIC THEN ASM_REAL_ARITH_TAC;
     REWRITE_TAC[SUBSET_INTER; SUBSET_REFL] THEN
     TRANS_TAC SUBSET_TRANS `mcball m (x0:A,r0)` THEN
     REWRITE_TAC [MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "sub" []];
    ALL_TAC] THEN
   USE_THEN "b1" (fun b1 -> GEN_REWRITE_TAC RAND_CONV [b1]) THEN
   MATCH_MP_TAC CHOICE_PAIRED_THM THEN REWRITE_TAC[] THEN
   HYP_TAC "ind_n: rpos rlt x subn" (REWRITE_RULE[LAMBDA_UNPAIR_THM]) THEN
   USE_THEN "u_dense" (MP_TAC o SPEC `SUC n` o
     REWRITE_RULE[GSYM TOPSPACE_MTOPOLOGY]) THEN
   REWRITE_TAC[DENSE_INTERSECTS_OPEN] THEN
   DISCH_THEN (MP_TAC o SPEC `mball m (b (SUC n):A#real)`) THEN
   (DESTRUCT_TAC "@x1 r1. bsuc" o MESON[PAIR])
     `?x1:A r1:real. b (SUC n) = x1,r1` THEN
   HYP REWRITE_TAC "bsuc" [] THEN
   REMOVE_THEN "bsuc"
    (fun th -> RULE_ASSUM_TAC (REWRITE_RULE[th]) THEN LABEL_TAC "bsuc" th) THEN
   ANTS_TAC THENL
   [HYP REWRITE_TAC "x" [OPEN_IN_MBALL; MBALL_EQ_EMPTY; DE_MORGAN_THM] THEN
    ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN INTRO_TAC "@z. hp" THEN
   EXISTS_TAC `z:A` THEN
   SUBGOAL_THEN `open_in (mtopology m) (mball m (x1:A,r1) INTER u (SUC n))`
     (DESTRUCT_TAC "hp1 hp2" o REWRITE_RULE[OPEN_IN_MTOPOLOGY_MCBALL]) THENL
   [HYP SIMP_TAC "u_open" [OPEN_IN_INTER; OPEN_IN_MBALL]; ALL_TAC] THEN
   CLAIM_TAC "z" `z:A IN mspace m` THENL
   [CUT_TAC `u (SUC n):A->bool SUBSET mspace m` THENL
    [HYP SET_TAC "hp" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "z" []] THEN
   REMOVE_THEN "hp2" (MP_TAC o SPEC `z:A`) THEN
   ANTS_TAC THENL [HYP SET_TAC "hp" []; ALL_TAC] THEN
   INTRO_TAC "@r. rpos ball" THEN EXISTS_TAC `min r (r1 / &4)` THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (z:A,r)` THEN
   HYP SIMP_TAC "ball" [MCBALL_SUBSET_CONCENTRIC; REAL_MIN_MIN];
   ALL_TAC] THEN
  CLAIM_TAC "@x r. b" `?x r. !n:num. b n = x n:A, r n:real` THENL
  [MAP_EVERY EXISTS_TAC
     [`FST o (b:num->A#real)`; `SND o (b:num->A#real)`] THEN
   REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  REMOVE_THEN "b"
    (fun b -> RULE_ASSUM_TAC (REWRITE_RULE[b]) THEN LABEL_TAC "b" b) THEN
  HYP_TAC "b0: x_0 r_0" (REWRITE_RULE[PAIR_EQ]) THEN
  REMOVE_THEN "x_0" (SUBST_ALL_TAC o GSYM) THEN
  REMOVE_THEN "r_0" (SUBST_ALL_TAC o GSYM) THEN
  HYP_TAC "rmk: r1pos r1lt x1 ball" (REWRITE_RULE[FORALL_AND_THM]) THEN
  CLAIM_TAC "x" `!n:num. x n:A IN mspace m` THENL
  [LABEL_INDUCT_TAC THENL
   [CUT_TAC `u 0:A->bool SUBSET mspace m` THENL
    [HYP SET_TAC "x0" [];
     HYP SIMP_TAC "u_open" [GSYM TOPSPACE_MTOPOLOGY; OPEN_IN_SUBSET]];
    HYP REWRITE_TAC "x1" []];
   ALL_TAC] THEN
  CLAIM_TAC "rpos" `!n:num. &0 < r n` THENL
  [LABEL_INDUCT_TAC THENL
   [HYP REWRITE_TAC "r0pos" []; HYP REWRITE_TAC "r1pos" []];
   ALL_TAC] THEN
  CLAIM_TAC "rmono" `!p q:num. p <= q ==> r q <= r p` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[REAL_LE_REFL] THEN
   INTRO_TAC "!p q; pq rpq" THEN
   REMOVE_THEN "r1lt" (MP_TAC o SPEC `q:num`) THEN
   REMOVE_THEN "rpos" (MP_TAC o SPEC `q:num`) THEN
   ASM_REAL_ARITH_TAC;
   ALL_TAC] THEN
  CLAIM_TAC "rlt" `!n:num. r n < inv (&2 pow n)` THENL
  [LABEL_INDUCT_TAC THENL
   [CONV_TAC (RAND_CONV REAL_RAT_REDUCE_CONV) THEN HYP REWRITE_TAC "r0lt1" [];
    TRANS_TAC REAL_LTE_TRANS `r (n:num) / &2` THEN
    HYP REWRITE_TAC "r1lt" [real_pow] THEN REMOVE_THEN "ind_n" MP_TAC THEN
    REMOVE_THEN "rpos" (MP_TAC o SPEC `n:num`) THEN CONV_TAC REAL_FIELD];
   ALL_TAC] THEN
  CLAIM_TAC "nested"
    `!p q:num. p <= q ==> mball m (x q:A, r q) SUBSET mball m (x p, r p)` THENL
  [MATCH_MP_TAC LE_INDUCT THEN REWRITE_TAC[SUBSET_REFL] THEN
   INTRO_TAC "!p q; pq sub" THEN
   TRANS_TAC SUBSET_TRANS `mball m (x (q:num):A,r q)` THEN
   HYP REWRITE_TAC "sub" [] THEN
   TRANS_TAC SUBSET_TRANS `mcball m (x (SUC q):A,r(SUC q))` THEN
   REWRITE_TAC[MBALL_SUBSET_MCBALL] THEN HYP SET_TAC "ball" [];
   ALL_TAC] THEN
  CLAIM_TAC "in_ball" `!p q:num. p <= q ==> x q:A IN mball m (x p, r p)` THENL
  [INTRO_TAC "!p q; le" THEN CUT_TAC `x (q:num):A IN mball m (x q, r q)` THENL
   [HYP SET_TAC "nested le" []; HYP SIMP_TAC "x rpos" [CENTRE_IN_MBALL_EQ]];
   ALL_TAC] THEN
  CLAIM_TAC "@l. l" `?l:A. limit (mtopology m) x l sequentially` THENL
  [HYP_TAC "m" (REWRITE_RULE[mcomplete]) THEN REMOVE_THEN "m" MATCH_MP_TAC THEN
   HYP REWRITE_TAC "x" [cauchy_in] THEN INTRO_TAC "!e; epos" THEN
   CLAIM_TAC "@N. N" `?N. inv(&2 pow N) < e` THENL
   [REWRITE_TAC[REAL_INV_POW] THEN MATCH_MP_TAC REAL_ARCH_POW_INV THEN
    HYP REWRITE_TAC "epos" [] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
   EXISTS_TAC `N:num` THEN MATCH_MP_TAC WLOG_LE THEN CONJ_TAC THENL
   [HYP SIMP_TAC "x" [MDIST_SYM] THEN MESON_TAC[]; ALL_TAC] THEN
   INTRO_TAC "!n n'; le; n n'" THEN
   TRANS_TAC REAL_LT_TRANS `inv (&2 pow N)` THEN HYP REWRITE_TAC "N" [] THEN
   TRANS_TAC REAL_LT_TRANS `r (N:num):real` THEN HYP REWRITE_TAC "rlt" [] THEN
   CUT_TAC `x (n':num):A IN mball m (x n, r n)` THENL
   [HYP REWRITE_TAC "x" [IN_MBALL] THEN INTRO_TAC "hp" THEN
    TRANS_TAC REAL_LTE_TRANS `r (n:num):real` THEN
    HYP SIMP_TAC "n rmono hp" [];
    HYP SIMP_TAC "in_ball le" []];
   ALL_TAC] THEN
  EXISTS_TAC `l:A` THEN
  CLAIM_TAC "in_mcball" `!n:num. l:A IN mcball m (x n, r n)` THENL
  [GEN_TAC THEN
   (MATCH_MP_TAC o ISPECL [`sequentially`; `mtopology (m:A metric)`])
   LIMIT_IN_CLOSED_IN THEN EXISTS_TAC `x:num->A` THEN
   HYP REWRITE_TAC "l" [TRIVIAL_LIMIT_SEQUENTIALLY; CLOSED_IN_MCBALL] THEN
   REWRITE_TAC[EVENTUALLY_SEQUENTIALLY] THEN EXISTS_TAC `n:num` THEN
   INTRO_TAC "![p]; p" THEN CUT_TAC `x (p:num):A IN mball m (x n, r n)` THENL
   [SET_TAC[MBALL_SUBSET_MCBALL]; HYP SIMP_TAC "in_ball p" []];
   ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
  [REWRITE_TAC[IN_INTERS; FORALL_IN_IMAGE; IN_UNIV] THEN
   LABEL_INDUCT_TAC THENL
   [HYP SET_TAC "in_mcball sub " []; HYP SET_TAC "in_mcball ball " []];
   HYP SET_TAC "sub in_mcball" []]);;

(* ------------------------------------------------------------------------- *)
(* Basic definition of the small inductive dimension relation ind t <= n.    *)
(* We plan to prove most of the theorems in R^n so this is as good a         *)
(* definition as any other, but the present stuff works in any top space.    *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("dimension_le",(12,"right"));;

let DIMENSION_LE_RULES,DIMENSION_LE_INDUCT,DIMENSION_LE_CASES =
  new_inductive_definition
  `!top n. -- &1 <= n /\
           (!v a. open_in top v /\ a IN v
                  ==> ?u. a IN u /\ u SUBSET v /\ open_in top u /\
                          subtopology top (top frontier_of u)
                          dimension_le (n - &1))
            ==> (top:A topology) dimension_le (n:int)`;;

let DIMENSION_LE_BOUND = prove
 (`!top:(A)topology n. top dimension_le n ==> -- &1 <= n`,
  MATCH_MP_TAC DIMENSION_LE_INDUCT THEN SIMP_TAC[]);;

let DIMENSION_LE_MONO = prove
 (`!top:(A)topology m n. top dimension_le m /\ m <= n ==> top dimension_le n`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC DIMENSION_LE_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`top:(A)topology`; `m:int`] THEN STRIP_TAC THEN
  X_GEN_TAC `n:int` THEN DISCH_TAC THEN
  GEN_REWRITE_TAC I [DIMENSION_LE_CASES] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[INT_LE_TRANS]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`v:A->bool`; `a:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:A->bool`; `a:A`]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_INT_ARITH_TAC);;

let DIMENSION_LE_EQ_EMPTY = prove
 (`!top:(A)topology. top dimension_le (-- &1) <=> topspace top = {}`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[DIMENSION_LE_CASES] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN `!top:A topology. ~(top dimension_le --(&2))`
   (fun th -> REWRITE_TAC[th])
  THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP DIMENSION_LE_BOUND) THEN
    INT_ARITH_TAC;
    EQ_TAC THENL
     [DISCH_THEN(MP_TAC o SPEC `topspace top:A->bool`) THEN
      REWRITE_TAC[OPEN_IN_TOPSPACE] THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
      ASM SET_TAC[]]]);;

let DIMENSION_LE_SUBTOPOLOGY = prove
 (`!top n s:A->bool.
        top dimension_le n ==> (subtopology top s) dimension_le n`,
  REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN MATCH_MP_TAC DIMENSION_LE_INDUCT THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `n:int`] THEN STRIP_TAC THEN
  X_GEN_TAC `s:A->bool` THEN GEN_REWRITE_TAC I [DIMENSION_LE_CASES] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`u':A->bool`; `a:A`] THEN
  GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[IMP_CONJ; LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `u:A->bool` THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:A->bool`; `a:A`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `v:A->bool` THEN STRIP_TAC THEN
  EXISTS_TAC `s INTER v:A->bool` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[OPEN_IN_SUBTOPOLOGY] THEN ASM_MESON_TAC[INTER_COMM];
    FIRST_X_ASSUM(MP_TAC o SPEC
     `subtopology top s frontier_of (s INTER v):A->bool`) THEN
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN MATCH_MP_TAC(SET_RULE
     `s SUBSET u /\ s SUBSET t ==> t INTER s = u INTER s`) THEN
    REWRITE_TAC[FRONTIER_OF_SUBSET_SUBTOPOLOGY] THEN
    REWRITE_TAC[FRONTIER_OF_CLOSURES; CLOSURE_OF_SUBTOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; INTER_ASSOC] THEN
    MATCH_MP_TAC(SET_RULE
     `t SUBSET u /\ v SUBSET w
      ==> s INTER t INTER s INTER v SUBSET u INTER w`) THEN
    CONJ_TAC THEN MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[]]);;

let DIMENSION_LE_SUBTOPOLOGIES = prove
 (`!top n s t:A->bool.
        s SUBSET t /\
        subtopology top t dimension_le n
        ==> (subtopology top s) dimension_le n`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o
    ISPEC `s:A->bool` o MATCH_MP DIMENSION_LE_SUBTOPOLOGY) THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[SET_RULE `s SUBSET t ==> t INTER s = s`]);;

let DIMENSION_LE_EQ_SUBTOPOLOGY = prove
 (`!top s:A->bool n.
        (subtopology top s) dimension_le n <=>
        -- &1 <= n /\
        !v a. open_in top v /\ a IN v /\ a IN s
              ==> ?u. a IN u /\ u SUBSET v /\ open_in top u /\
                      subtopology top
                       ((subtopology top s frontier_of (s INTER u)))
                      dimension_le (n - &1)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [DIMENSION_LE_CASES] THEN
  REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; OPEN_IN_SUBTOPOLOGY] THEN
  REWRITE_TAC[LEFT_AND_EXISTS_THM; LEFT_IMP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[MESON[]
   `(!v a t. (P t /\ Q v t) /\ R a v t ==> S a v t) <=>
    (!t a v. Q v t ==> P t /\ R a v t ==> S a v t)`] THEN
  REWRITE_TAC[FORALL_UNWIND_THM2] THEN AP_TERM_TAC THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `v:A->bool` THEN REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN
  X_GEN_TAC `a:A` THEN REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC(TAUT `(p ==> (q <=> r)) ==> (p ==> q <=> p ==> r)`) THEN
  STRIP_TAC THEN REWRITE_TAC[RIGHT_AND_EXISTS_THM] THEN
  GEN_REWRITE_TAC LAND_CONV [SWAP_EXISTS_THM] THEN
  ONCE_REWRITE_TAC[TAUT
    `p /\ q /\ (r /\ s) /\ t <=> s /\ p /\ q /\ r /\ t`] THEN
  ASM_REWRITE_TAC[UNWIND_THM2; IN_INTER] THEN
  EQ_TAC THEN DISCH_THEN(X_CHOOSE_THEN `u:A->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `u INTER v:A->bool` THEN
  ASM_SIMP_TAC[IN_INTER; OPEN_IN_INTER] THEN
  (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
  ASM_SIMP_TAC[SET_RULE `u SUBSET v ==> u INTER v = u`;
               SET_RULE `u INTER s SUBSET v INTER s
                         ==> s INTER u INTER v = s INTER u`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  ASM_SIMP_TAC[FRONTIER_OF_SUBSET_SUBTOPOLOGY;
               SET_RULE `v SUBSET u ==> u INTER v = v`] THEN
  STRIP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]);;

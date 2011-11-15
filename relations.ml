(* ------------------------------------------------------------------------- *)
(* Theory of relations.                                                      *)
(* ------------------------------------------------------------------------- *)

needs "sets.ml";;

logfile "relation-def";;

let set_to_relation_def = new_definition
  `!s (x:A) (y:B). set_to_relation s x y <=> (x,y) IN s`;;

export_thm set_to_relation_def;;

let relation_to_set_def = new_definition
  `!(r : A -> B -> bool). relation_to_set r = { (x,y) | r x y }`;;

export_thm relation_to_set_def;;

let emptyr_def = new_definition
  `(emptyr : A -> B -> bool) = set_to_relation EMPTY`;;

export_thm emptyr_def;;

let univr_def = new_definition
  `(univr : A -> B -> bool) = set_to_relation UNIV`;;

export_thm univr_def;;

let subrelation_def = new_definition
  `!(r : A -> B -> bool) s.
     subrelation r s <=> relation_to_set r SUBSET relation_to_set s`;;

export_thm subrelation_def;;

let unionr_def = new_definition
  `!(r : A -> B -> bool) s.
     unionr r s =
     set_to_relation (relation_to_set r UNION relation_to_set s)`;;

export_thm unionr_def;;

let interr_def = new_definition
  `!(r : A -> B -> bool) s.
     interr r s =
     set_to_relation (relation_to_set r INTER relation_to_set s)`;;

export_thm interr_def;;

let big_unionr_def = new_definition
  `!(s : (A -> B -> bool) set).
     big_unionr s = set_to_relation (UNIONS (IMAGE relation_to_set s))`;;

export_thm big_unionr_def;;

let big_interr_def = new_definition
  `!(s : (A -> B -> bool) set).
     big_interr s = set_to_relation (INTERS (IMAGE relation_to_set s))`;;

export_thm big_interr_def;;

let reflexive_def = new_definition
  `!r. reflexive r <=> (!(x:A). r x x)`;;

export_thm reflexive_def;;

let irreflexive_def = new_definition
  `!r. irreflexive r <=> (!(x:A). ~r x x)`;;

export_thm irreflexive_def;;

let transitive_def = new_definition
  `!r. transitive r <=> (!x (y:A) z. r x y /\ r y z ==> r x z)`;;

export_thm transitive_def;;

let transitive_closure_def = new_definition
  `!(r : A -> A -> bool).
     transitive_closure r =
     big_interr { s | subrelation r s /\ transitive s }`;;

export_thm transitive_closure_def;;

logfile "relation-thm";;

let relation_to_set = prove
  (`!r (x:A) (y:B). (x,y) IN relation_to_set r <=> r x y`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [relation_to_set_def; IN_ELIM_THM; PAIR_EQ] THEN
   REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL
   [ASM_REWRITE_TAC [];
    EXISTS_TAC `x:A` THEN
    EXISTS_TAC `y:B` THEN
    ASM_REWRITE_TAC []]);;

export_thm relation_to_set;;

let emptyr = prove
  (`!(x:A) (y:B). ~emptyr x y`,
   REWRITE_TAC [emptyr_def; set_to_relation_def; NOT_IN_EMPTY]);;

export_thm emptyr;;

let univr = prove
  (`!(x:A) (y:B). univr x y`,
   REWRITE_TAC [univr_def; set_to_relation_def; IN_UNIV]);;

export_thm univr;;

let subrelation = prove
  (`!(r : A -> B -> bool) s.
      subrelation r s <=> !(x:A) (y:B). r x y ==> s x y`,
   REWRITE_TAC [subrelation_def; SUBSET; FORALL_PAIR_THM; relation_to_set]);;

export_thm subrelation;;

let unionr = prove
  (`!r s (x:A) (y:B). unionr r s x y <=> r x y \/ s x y`,
   REWRITE_TAC [unionr_def; set_to_relation_def; IN_UNION; relation_to_set]);;

export_thm unionr;;

let interr = prove
  (`!r s (x:A) (y:B). interr r s x y <=> r x y /\ s x y`,
   REWRITE_TAC [interr_def; set_to_relation_def; IN_INTER; relation_to_set]);;

export_thm interr;;

let big_unionr = prove
  (`!s (x:A) (y:B). big_unionr s x y <=> ?r. r IN s /\ r x y`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [big_unionr_def; set_to_relation_def; IN_UNIONS; IN_IMAGE] THEN
   EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `x' : A -> B -> bool` THEN
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [relation_to_set];
    STRIP_TAC THEN
    EXISTS_TAC `relation_to_set (r : A -> B -> bool)` THEN
    ASM_REWRITE_TAC [relation_to_set] THEN
    EXISTS_TAC `r : A -> B -> bool` THEN
    ASM_REWRITE_TAC []]);;

export_thm big_unionr;;

let big_interr = prove
  (`!s (x:A) (y:B). big_interr s x y <=> !r. r IN s ==> r x y`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [big_interr_def; set_to_relation_def; IN_INTERS; IN_IMAGE] THEN
   EQ_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPEC `relation_to_set (r : A -> B -> bool)`) THEN
    REWRITE_TAC [relation_to_set] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `r : A -> B -> bool` THEN
    ASM_REWRITE_TAC [];
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [relation_to_set] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm big_interr;;

let reflexive = prove
  (`!r (x:A). reflexive r ==> r x x`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [reflexive_def] THEN
   DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm reflexive;;

let irreflexive = prove
  (`!r (x:A). irreflexive r ==> ~r x x`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [irreflexive_def] THEN
   DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm irreflexive;;

let irreflexive_emptyr = prove
  (`irreflexive (emptyr : A -> A -> bool)`,
   REWRITE_TAC [irreflexive_def; emptyr]);;

export_thm irreflexive_emptyr;;

let transitive_emptyr = prove
  (`transitive (emptyr : A -> A -> bool)`,
   REWRITE_TAC [transitive_def; emptyr]);;

export_thm transitive_emptyr;;

let reflexive_univr = prove
  (`reflexive (univr : A -> A -> bool)`,
   REWRITE_TAC [reflexive_def; univr]);;

export_thm reflexive_univr;;

let transitive_univr = prove
  (`transitive (univr : A -> A -> bool)`,
   REWRITE_TAC [transitive_def; univr]);;

export_thm transitive_univr;;

let relation_extension_imp = prove
  (`!r s. (!(x:A) (y:B). r x y <=> s x y) ==> r = s`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [FUN_EQ_THM] THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm relation_extension_imp;;

let set_to_relation_to_set = prove
  (`!(s : (A # B) set). relation_to_set (set_to_relation s) = s`,
   GEN_TAC THEN
   MATCH_MP_TAC EXTENSION_IMP THEN
   REWRITE_TAC [FORALL_PAIR_THM; relation_to_set; set_to_relation_def]);;

export_thm set_to_relation_to_set;;

let relation_to_set_to_relation = prove
  (`!(r : A -> B -> bool). set_to_relation (relation_to_set r) = r`,
   GEN_TAC THEN
   MATCH_MP_TAC relation_extension_imp THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [relation_to_set; set_to_relation_def]);;

export_thm relation_to_set_to_relation;;

let relation_to_set_inj = prove
  (`!(r : A -> B -> bool) s. relation_to_set r = relation_to_set s ==> r = s`,
   REPEAT STRIP_TAC THEN
   CONV_TAC (LAND_CONV (REWR_CONV (GSYM relation_to_set_to_relation))) THEN
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM relation_to_set_to_relation))) THEN
   AP_TERM_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm relation_to_set_inj;;

let subrelation_refl = prove
  (`!(r : A -> B -> bool). subrelation r r`,
   GEN_TAC THEN
   REWRITE_TAC [subrelation]);;

export_thm subrelation_refl;;

let subrelation_antisym = prove
  (`!(r : A -> B -> bool) s. subrelation r s /\ subrelation s r ==> r = s`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [subrelation_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC relation_to_set_inj THEN
   MATCH_MP_TAC SUBSET_ANTISYM THEN
   ASM_REWRITE_TAC []);;

export_thm subrelation_antisym;;

let subrelation_trans = prove
  (`!(r : A -> B -> bool) s t.
      subrelation r s /\ subrelation s t ==> subrelation r t`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [subrelation_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC SUBSET_TRANS THEN
   EXISTS_TAC `relation_to_set (s : A -> B -> bool)` THEN
   ASM_REWRITE_TAC []);;

export_thm subrelation_trans;;

let subrelation_big_interr = prove
  (`!(r : A -> B -> bool) s.
      subrelation r (big_interr s) <=>
      (!(t : A -> B -> bool). t IN s ==> subrelation r t)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [subrelation_def; big_interr_def; set_to_relation_to_set] THEN
   REWRITE_TAC [SUBSET_INTERS; FORALL_IN_IMAGE]);;

export_thm subrelation_big_interr;;

let transitive_closure_subrelation = prove
  (`!(r : A -> A -> bool). subrelation r (transitive_closure r)`,
   GEN_TAC THEN
   REWRITE_TAC [transitive_closure_def; subrelation; big_interr; IN_ELIM] THEN
   REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm transitive_closure_subrelation;;

let transitive_closure_transitive = prove
  (`!(r : A -> A -> bool). transitive (transitive_closure r)`,
   GEN_TAC THEN
   REWRITE_TAC [transitive_def] THEN
   REWRITE_TAC [transitive_closure_def; big_interr; IN_ELIM] THEN
   REPEAT STRIP_TAC THEN
   REPEAT (FIRST_X_ASSUM (MP_TAC o SPEC `r' : A -> A -> bool`)) THEN
   ASM_REWRITE_TAC [] THEN
   REWRITE_TAC [IMP_IMP] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC [transitive_def] THEN
   DISCH_THEN MATCH_ACCEPT_TAC);;

export_thm transitive_closure_transitive;;

let transitive_closure_smallest = prove
  (`!(r : A -> A -> bool) s.
     subrelation r s /\ transitive s ==>
     subrelation (transitive_closure r) s`,
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [subrelation] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [transitive_closure_def; big_interr; IN_ELIM] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm transitive_closure_smallest;;

logfile "relation-natural-def";;

let successor_def = new_definition
  `!m n. successor m n <=> SUC m = n`;;

export_thm successor_def;;

logfile "relation-natural-thm";;

let subrelation_successor_lt = prove
 (`subrelation successor (<)`,
  REWRITE_TAC [subrelation; successor_def] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN SUBST_VAR_TAC THEN
  MATCH_ACCEPT_TAC SUC_LT);;

export_thm subrelation_successor_lt;;

let transitive_lt = prove
 (`transitive (<)`,
  REWRITE_TAC [transitive_def] THEN
  ACCEPT_TAC LT_TRANS);;

export_thm transitive_lt;;

let transitive_successor_lt = prove
 (`!r. subrelation successor r /\ transitive r ==> subrelation (<) r`,
  GEN_TAC THEN
  REWRITE_TAC [transitive_def; subrelation] THEN
  STRIP_TAC THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [LT_EXISTS] THEN
  DISCH_THEN (CHOOSE_THEN SUBST_VAR_TAC) THEN
  SPEC_TAC (`d:num`,`k:num`) THEN
  INDUCT_TAC THENL
  [FIRST_X_ASSUM (K ALL_TAC) THEN
   REWRITE_TAC [ADD_CLAUSES] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [successor_def];
   ONCE_REWRITE_TAC [ADD_CLAUSES] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   EXISTS_TAC `x + SUC k` THEN
   ASM_REWRITE_TAC [] THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC [successor_def]]);;

export_thm transitive_successor_lt;;

let transitive_closure_successor_lt = prove
 (`transitive_closure successor = (<)`,
  MATCH_MP_TAC subrelation_antisym THEN
  CONJ_TAC THENL
  [MATCH_MP_TAC transitive_closure_smallest THEN
   REWRITE_TAC [subrelation_successor_lt; transitive_lt];
   REWRITE_TAC [transitive_closure_def; subrelation_big_interr; IN_ELIM] THEN
   ACCEPT_TAC transitive_successor_lt]);;

export_thm transitive_closure_successor_lt;;

(* ------------------------------------------------------------------------- *)
(* A common lemma for transitive relations.                                  *)
(* ------------------------------------------------------------------------- *)

let TRANSITIVE_STEPWISE_LT = prove
 (`!R. (!x y z. R x y /\ R y z ==> R x z) /\ (!n. R n (SUC n))
       ==> !m n. m < n ==> R m n`,
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `R : num -> num -> bool` transitive_successor_lt) THEN
  ASM_REWRITE_TAC [subrelation; successor_def; transitive_def] THEN
  ANTS_TAC THENL
  [REPEAT GEN_TAC THEN
   DISCH_THEN SUBST_VAR_TAC THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC;
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC]);;

let TRANSITIVE_STEPWISE_LT_EQ = prove
 (`!R. (!x y z. R x y /\ R y z ==> R x z)
         ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[LT] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LT THEN
  CONJ_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

let TRANSITIVE_STEPWISE_LE = prove
 (`!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z) /\
       (!n. R n (SUC n))
       ==> !m n. m <= n ==> R m n`,
  ONCE_REWRITE_TAC [LE_LT] THEN
  REPEAT STRIP_TAC THENL
  [MP_TAC (SPEC `R : num -> num -> bool` TRANSITIVE_STEPWISE_LT) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC;
   ASM_REWRITE_TAC []]);;

let TRANSITIVE_STEPWISE_LE_EQ = prove
 (`!R. (!x. R x x) /\ (!x y z. R x y /\ R y z ==> R x z)
       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_SIMP_TAC[LE; LE_REFL] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
  REPEAT CONJ_TAC THEN
  FIRST_ASSUM ACCEPT_TAC);;

logfile_end ();;

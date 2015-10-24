(* ========================================================================= *)
(* STREAM PARSERS                                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Theory requirements.                                                      *)
(* ------------------------------------------------------------------------- *)

import_theories
  ["base"];;

(* ------------------------------------------------------------------------- *)
(* Theory interpretation.                                                    *)
(* ------------------------------------------------------------------------- *)

export_interpretation "opentheory/theories/parser/parser.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of parse streams.                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-stream-def";;

let (pstream_induct,pstream_recursion) =
  let (induct0,recursion0) = define_type
    "pstream = ErrorPstream
             | EofPstream
             | ConsPstream A pstream" in
  let induct = prove
    (`!p : A pstream -> bool.
         p ErrorPstream /\
         p EofPstream /\
         (!x xs. p xs ==> p (ConsPstream x xs)) ==>
         (!xs. p xs)`,
     ACCEPT_TAC induct0) in
  let recursion = prove
    (`!e b f. ?fn : A pstream -> B.
         fn ErrorPstream = e /\
         fn EofPstream = b /\
         !x xs. fn (ConsPstream x xs) = f x xs (fn xs)`,
     MATCH_ACCEPT_TAC recursion0) in
  (induct,recursion);;

export_thm pstream_induct;;
export_thm pstream_recursion;;

let (case_pstream_error,case_pstream_eof,case_pstream_cons) =
  let def = new_recursive_definition pstream_recursion
    `(!(e : B) b f. case_pstream e b f ErrorPstream = e) /\
     (!e b f. case_pstream e b f EofPstream = b) /\
     (!e b f (x : A) xs. case_pstream e b f (ConsPstream x xs) = f x xs)` in
  CONJ_TRIPLE def;;

export_thm case_pstream_error;;
export_thm case_pstream_eof;;
export_thm case_pstream_cons;;

let case_pstream_def =
    CONJ case_pstream_error (CONJ case_pstream_eof case_pstream_cons);;

let (map_pstream_error,map_pstream_eof,map_pstream_cons) =
  let def = new_recursive_definition pstream_recursion
    `(!(f : A -> B). map_pstream f ErrorPstream = ErrorPstream) /\
     (!f. map_pstream f EofPstream = EofPstream) /\
     (!f x xs.
        map_pstream f (ConsPstream x xs) =
        ConsPstream (f x) (map_pstream f xs))` in
  CONJ_TRIPLE def;;

export_thm map_pstream_error;;
export_thm map_pstream_eof;;
export_thm map_pstream_cons;;

let map_pstream_def =
  CONJ map_pstream_error (CONJ map_pstream_eof map_pstream_cons);;

let (length_pstream_error,length_pstream_eof,length_pstream_cons) =
  let def = new_recursive_definition pstream_recursion
    `(length_pstream ErrorPstream = 0) /\
     (length_pstream EofPstream = 0) /\
     (!(x : A) xs.
        length_pstream (ConsPstream x xs) = SUC (length_pstream xs))` in
  CONJ_TRIPLE def;;

export_thm length_pstream_error;;
export_thm length_pstream_eof;;
export_thm length_pstream_cons;;

let length_pstream_def =
  CONJ length_pstream_error (CONJ length_pstream_eof length_pstream_cons);;

let ((is_proper_suffix_pstream_error,
      is_proper_suffix_pstream_eof,
      is_proper_suffix_pstream_cons),
     is_suffix_pstream_def) =
  let pdef = new_recursive_definition pstream_recursion
    `(!xs. is_proper_suffix_pstream xs ErrorPstream = F) /\
     (!xs. is_proper_suffix_pstream xs EofPstream = F) /\
     (!xs (y : A) ys.
        is_proper_suffix_pstream xs (ConsPstream y ys) =
        ((xs = ys) \/ is_proper_suffix_pstream xs ys))` in
  let def = new_definition
    `!xs ys : A pstream.
       is_suffix_pstream xs ys =
       ((xs = ys) \/ is_proper_suffix_pstream xs ys)` in
  (CONJ_TRIPLE (REWRITE_RULE [GSYM def] pdef), def);;

export_thm is_proper_suffix_pstream_error;;
export_thm is_proper_suffix_pstream_eof;;
export_thm is_proper_suffix_pstream_cons;;
export_thm is_suffix_pstream_def;;

let is_proper_suffix_pstream_def =
  CONJ is_proper_suffix_pstream_error
    (CONJ is_proper_suffix_pstream_eof is_proper_suffix_pstream_cons);;

let (pstream_to_list_error,
     pstream_to_list_eof,
     pstream_to_list_cons) =
  let def = new_recursive_definition pstream_recursion
    `(pstream_to_list ErrorPstream = ([],T)) /\
     (pstream_to_list EofPstream = ([],F)) /\
     (!(x : A) xs. pstream_to_list (ConsPstream x xs) =
        let (l,e) = pstream_to_list xs in
        (CONS x l, e))` in
  CONJ_TRIPLE def;;

export_thm pstream_to_list_error;;
export_thm pstream_to_list_eof;;
export_thm pstream_to_list_cons;;

let pstream_to_list_def =
  CONJ pstream_to_list_error
    (CONJ pstream_to_list_eof pstream_to_list_cons);;

let (append_pstream_nil,append_pstream_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!xs. append_pstream [] xs = xs) /\
     (!(h : A) t xs.
        append_pstream (CONS h t) xs = ConsPstream h (append_pstream t xs))` in
  CONJ_PAIR def;;

export_thm append_pstream_nil;;
export_thm append_pstream_cons;;

let append_pstream_def = CONJ append_pstream_nil append_pstream_cons;;

let list_to_pstream_def = new_definition
  `!(l : A list). list_to_pstream l = append_pstream l EofPstream`;;

export_thm list_to_pstream_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of parse streams.                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-stream-thm";;

export_thm case_pstream_def;;
export_thm map_pstream_def;;
export_thm pstream_to_list_def;;
export_thm append_pstream_def;;

let pstream_cases = prove
 (`!(xs : A pstream).
      xs = ErrorPstream \/
      xs = EofPstream \/
      ?x xt. xs = ConsPstream x xt`,
  ACCEPT_TAC (prove_cases_thm pstream_induct));;

export_thm pstream_cases;;

let (pstream_distinct_error_eof,
     pstream_distinct_error_cons,
     pstream_distinct_eof_cons) =
  let th = prove
    (`~((ErrorPstream : A pstream) = EofPstream) /\
      (!(x : A) xs. ~(ErrorPstream = ConsPstream x xs)) /\
      (!(x : A) xs. ~(EofPstream = ConsPstream x xs))`,
     ACCEPT_TAC (prove_constructors_distinct pstream_recursion)) in
  CONJ_TRIPLE th;;

export_thm pstream_distinct_error_eof;;
export_thm pstream_distinct_error_cons;;
export_thm pstream_distinct_eof_cons;;

let pstream_distinct =
  CONJ pstream_distinct_error_eof
    (CONJ pstream_distinct_error_cons pstream_distinct_eof_cons);;

let pstream_inj = prove
 (`!(x : A) xs y ys.
     ConsPstream x xs = ConsPstream y ys <=> x = y /\ xs = ys`,
  ACCEPT_TAC (prove_constructors_injective pstream_recursion));;

export_thm pstream_inj;;

let is_proper_suffix_pstream_length = prove
 (`!xs ys : A pstream.
     is_proper_suffix_pstream xs ys ==>
     length_pstream xs < length_pstream ys`,
  GEN_TAC THEN
  MATCH_MP_TAC pstream_induct THEN
  ASM_REWRITE_TAC
    [is_proper_suffix_pstream_def; length_pstream_def; LT_SUC_LE] THEN
  GEN_TAC THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `(xs : A pstream) = ys` THEN
  ASM_REWRITE_TAC [LE_REFL; is_suffix_pstream_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC LT_IMP_LE THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm is_proper_suffix_pstream_length;;

let is_proper_suffix_pstream_wf = prove
 (`WF (is_proper_suffix_pstream : A pstream -> A pstream -> bool)`,
  MATCH_MP_TAC
    (ISPECL [`is_proper_suffix_pstream : A pstream -> A pstream -> bool`;
             `MEASURE (length_pstream : A pstream -> num)`] WF_SUBSET) THEN
  REWRITE_TAC [WF_MEASURE] THEN
  REWRITE_TAC [MEASURE; is_proper_suffix_pstream_length]);;

export_thm is_proper_suffix_pstream_wf;;

let is_proper_suffix_pstream_refl = prove
 (`!xs : A pstream. ~is_proper_suffix_pstream xs xs`,
  GEN_TAC THEN
  MATCH_MP_TAC WF_REFL THEN
  ACCEPT_TAC is_proper_suffix_pstream_wf);;

export_thm is_proper_suffix_pstream_refl;;

let is_proper_suffix_pstream_induct = prove
 (`!(p : A pstream -> bool).
      (!xs. (!ys. is_proper_suffix_pstream ys xs ==> p ys) ==> p xs) ==>
      !xs. p xs`,
  REWRITE_TAC [GSYM WF_IND; is_proper_suffix_pstream_wf]);;

export_thm is_proper_suffix_pstream_induct;;

let is_proper_suffix_pstream_recursion = prove
 (`!(h : (A pstream -> B) -> A pstream -> B).
      (!f g xs.
         (!ys. is_proper_suffix_pstream ys xs ==> (f ys = g ys)) ==>
         (h f xs = h g xs)) ==>
      ?fn. !xs. fn xs = h fn xs`,
  MATCH_MP_TAC WF_REC THEN
  REWRITE_TAC [is_proper_suffix_pstream_wf]);;

export_thm is_proper_suffix_pstream_recursion;;

let is_proper_suffix_pstream_trans = prove
 (`!xs ys zs : A pstream.
     is_proper_suffix_pstream xs ys /\ is_proper_suffix_pstream ys zs ==>
     is_proper_suffix_pstream xs zs`,
  GEN_TAC THEN
  GEN_TAC THEN
  MATCH_MP_TAC pstream_induct THEN
  ASM_REWRITE_TAC [is_proper_suffix_pstream_def] THEN
  X_GEN_TAC `zs : A pstream` THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [is_suffix_pstream_def] THEN
  ASM_CASES_TAC `xs = (zs : A pstream)` THEN
  ASM_REWRITE_TAC [] THEN
  ASM_CASES_TAC `ys = (zs : A pstream)` THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  UNDISCH_TAC `is_suffix_pstream (ys : A pstream) zs` THEN
  ASM_REWRITE_TAC [is_suffix_pstream_def]);;

export_thm is_proper_suffix_pstream_trans;;

let is_proper_suffix_pstream_trans2 = prove
 (`!xs ys zs : A pstream.
     is_suffix_pstream xs ys /\ is_proper_suffix_pstream ys zs ==>
     is_proper_suffix_pstream xs zs`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `xs = (ys : A pstream)` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ASM_REWRITE_TAC [is_suffix_pstream_def] THEN
   MATCH_ACCEPT_TAC is_proper_suffix_pstream_trans]);;

export_thm is_proper_suffix_pstream_trans2;;

let is_proper_suffix_pstream_trans1 = prove
 (`!xs ys zs : A pstream.
     is_proper_suffix_pstream xs ys /\ is_suffix_pstream ys zs ==>
     is_proper_suffix_pstream xs zs`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `ys = (zs : A pstream)` THENL
  [ASM_REWRITE_TAC [] THEN
   STRIP_TAC;
   ASM_REWRITE_TAC [is_suffix_pstream_def] THEN
   MATCH_ACCEPT_TAC is_proper_suffix_pstream_trans]);;

export_thm is_proper_suffix_pstream_trans1;;

let is_suffix_pstream_proper = prove
 (`!xs ys : A pstream.
     is_proper_suffix_pstream xs ys ==> is_suffix_pstream xs ys`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [is_suffix_pstream_def] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm is_suffix_pstream_proper;;

let is_suffix_pstream_refl = prove
 (`!xs : A pstream. is_suffix_pstream xs xs`,
  REWRITE_TAC [is_suffix_pstream_def]);;

export_thm is_suffix_pstream_refl;;

let is_suffix_pstream_error = prove
 (`!xs : A pstream. is_suffix_pstream xs ErrorPstream <=> xs = ErrorPstream`,
  REWRITE_TAC [is_suffix_pstream_def; is_proper_suffix_pstream_error]);;

export_thm is_suffix_pstream_error;;

let is_suffix_pstream_eof = prove
 (`!xs : A pstream. is_suffix_pstream xs EofPstream <=> xs = EofPstream`,
  REWRITE_TAC [is_suffix_pstream_def; is_proper_suffix_pstream_eof]);;

export_thm is_suffix_pstream_eof;;

let is_suffix_pstream_trans = prove
 (`!xs ys zs : A pstream.
     is_suffix_pstream xs ys /\ is_suffix_pstream ys zs ==>
     is_suffix_pstream xs zs`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `xs = (ys : A pstream)` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_THEN
    `is_suffix_pstream xs (ys : A pstream)`
    (MP_TAC o REWRITE_RULE [is_suffix_pstream_def]) THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC is_suffix_pstream_proper THEN
  MATCH_MP_TAC is_proper_suffix_pstream_trans1 THEN
  EXISTS_TAC `ys : A pstream` THEN
  ASM_REWRITE_TAC []);;

export_thm is_suffix_pstream_trans;;

let is_suffix_pstream_length = prove
 (`!xs ys : A pstream.
     is_suffix_pstream xs ys ==>
     length_pstream xs <= length_pstream ys`,
  REPEAT GEN_TAC THEN
  ASM_CASES_TAC `(xs : A pstream) = ys` THENL
  [ASM_REWRITE_TAC [LE_REFL];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [is_suffix_pstream_def] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC LT_IMP_LE THEN
  MATCH_MP_TAC is_proper_suffix_pstream_length THEN
  ASM_REWRITE_TAC []);;

export_thm is_suffix_pstream_length;;

let append_pstream_assoc = prove
 (`!xs ys zs : A pstream.
     append_pstream (APPEND xs ys) zs =
     append_pstream xs (append_pstream ys zs)`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [APPEND; append_pstream_def]);;

export_thm append_pstream_assoc;;

let list_to_pstream_nil = prove
 (`list_to_pstream ([] : A list) = EofPstream`,
  REWRITE_TAC [list_to_pstream_def; append_pstream_nil]);;

export_thm list_to_pstream_nil;;

let list_to_pstream_cons = prove
 (`!(h : A) t. list_to_pstream (CONS h t) = ConsPstream h (list_to_pstream t)`,
  REWRITE_TAC [list_to_pstream_def; append_pstream_cons]);;

export_thm list_to_pstream_cons;;

let list_to_pstream_append = prove
 (`!l1 l2 : A list.
     list_to_pstream (APPEND l1 l2) = append_pstream l1 (list_to_pstream l2)`,
  REWRITE_TAC [list_to_pstream_def; append_pstream_assoc]);;

export_thm list_to_pstream_append;;

let list_to_pstream_to_list = prove
 (`!l : A list. pstream_to_list (list_to_pstream l) = (l,F)`,
  REWRITE_TAC [list_to_pstream_def] THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [pstream_to_list_def; append_pstream_def];
   ASM_REWRITE_TAC [pstream_to_list_def; append_pstream_def] THEN
   REWRITE_TAC [LET_DEF; LET_END_DEF]]);;

export_thm list_to_pstream_to_list;;

let pstream_to_list_append = prove
 (`!(l : A list) xs ys e.
     pstream_to_list (append_pstream l xs) = (APPEND l ys, e) <=>
     pstream_to_list xs = (ys,e)`,
  REPEAT GEN_TAC THEN
  SPEC_TAC (`l : A list`,`l : A list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [APPEND; append_pstream_def];
   ALL_TAC] THEN
  POP_ASSUM (SUBST1_TAC o SYM) THEN
  REWRITE_TAC [APPEND; append_pstream_def; pstream_to_list_def] THEN
  MP_TAC
    (ISPEC
       `pstream_to_list (append_pstream (t : A list) xs)`
       PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zs : A list`
       (X_CHOOSE_THEN `z : bool` SUBST1_TAC)) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ; CONS_11]);;

export_thm pstream_to_list_append;;

let append_pstream_length = prove
 (`!(l : A list) xs.
     length_pstream (append_pstream l xs) = LENGTH l + length_pstream xs`,
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [length_pstream_def; append_pstream_def; LENGTH; ADD];
   ASM_REWRITE_TAC [length_pstream_def; append_pstream_def; LENGTH; ADD]]);;

export_thm append_pstream_length;;

let list_to_pstream_length = prove
 (`!l : A list. length_pstream (list_to_pstream l) = LENGTH l`,
  REWRITE_TAC
    [list_to_pstream_def; append_pstream_length; length_pstream_def; ADD_0]);;

export_thm list_to_pstream_length;;

let pstream_to_list_length = prove
 (`!(xs : A pstream) ys e.
     pstream_to_list xs = (ys,e) ==>
     length_pstream xs = LENGTH ys`,
  MATCH_MP_TAC pstream_induct THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [length_pstream_def; LENGTH];
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [length_pstream_def; LENGTH];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
  MP_TAC (ISPEC `pstream_to_list (xs : A pstream)` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zs : A list`
       (X_CHOOSE_THEN `z : bool` SUBST1_TAC)) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  DISCH_THEN (MP_TAC o SPECL [`zs : A list`; `z : bool`]) THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NOT_CONS_NIL];
   ALL_TAC] THEN
  GEN_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [CONS_11] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_VAR_TAC) SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC [length_pstream_def; LENGTH]);;

export_thm pstream_to_list_length;;

let length_fst_pstream_to_list = prove
 (`!(xs : A pstream).
     length_pstream xs = LENGTH (FST (pstream_to_list xs))`,
  GEN_TAC THEN
  MATCH_MP_TAC pstream_to_list_length THEN
  EXISTS_TAC `SND (pstream_to_list (xs : A pstream))` THEN
  REWRITE_TAC []);;

export_thm length_fst_pstream_to_list;;

let pstream_to_list_map = prove
 (`!(f : A -> B) xs ys e.
     pstream_to_list xs = (ys,e) ==>
     pstream_to_list (map_pstream f xs) = (MAP f ys, e)`,
  GEN_TAC THEN
  MATCH_MP_TAC pstream_induct THEN
  REPEAT CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [map_pstream_def; pstream_to_list_def; MAP];
   REPEAT GEN_TAC THEN
   PURE_REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [map_pstream_def; pstream_to_list_def; MAP];
   ALL_TAC] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [pstream_to_list_def; PAIR_EQ] THEN
  MP_TAC (ISPEC `pstream_to_list (xs : A pstream)` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `zs : A list`
       (X_CHOOSE_THEN `z : bool` SUBST1_TAC)) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  DISCH_THEN (MP_TAC o SPECL [`zs : A list`; `z : bool`]) THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [NOT_CONS_NIL];
   ALL_TAC] THEN
  GEN_TAC THEN
  POP_ASSUM (K ALL_TAC) THEN
  REWRITE_TAC [CONS_11] THEN
  DISCH_THEN (CONJUNCTS_THEN2 (CONJUNCTS_THEN SUBST_VAR_TAC) SUBST_VAR_TAC) THEN
  ASM_REWRITE_TAC
    [map_pstream_def; pstream_to_list_def; MAP; LET_DEF; LET_END_DEF]);;

export_thm pstream_to_list_map;;

let length_pstream_src = prove
 (`(length_pstream (ErrorPstream : A pstream) = 0) /\
   (length_pstream (EofPstream : A pstream) = 0) /\
   (!(x : A) xs. length_pstream (ConsPstream x xs) = length_pstream xs + 1)`,
  REWRITE_TAC [length_pstream_def; ADD1]);;

export_thm length_pstream_src;;

let arbitrary_pstream = prove
 (`ONTO
     (\ ((l : A list), b).
        append_pstream l (if b then ErrorPstream else EofPstream))`,
  REWRITE_TAC [ONTO] THEN
  MATCH_MP_TAC pstream_induct THEN
  REPEAT CONJ_TAC THENL
  [EXISTS_TAC `([] : A list, T)` THEN
   REWRITE_TAC [append_pstream_nil];
   EXISTS_TAC `([] : A list, F)` THEN
   REWRITE_TAC [append_pstream_nil];
   X_GEN_TAC `x : A` THEN
   X_GEN_TAC `xs : A pstream` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `l : A list`
        (X_CHOOSE_THEN `b : bool` SUBST_VAR_TAC) o
      REWRITE_RULE [EXISTS_PAIR_THM]) THEN
   EXISTS_TAC `(CONS (x : A) l, (b : bool))` THEN
   REWRITE_TAC [append_pstream_cons]]);;

export_thm arbitrary_pstream;;

(* ------------------------------------------------------------------------- *)
(* Definition of stream parser combinators.                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-comb-def";;

(* A type of parsers *)

let is_parser_def = new_definition
  `!(p : A -> A pstream -> (B # A pstream) option).
     is_parser p <=>
     !x xs.
       case_option
         T
         (\ (y,ys). is_suffix_pstream ys xs)
         (p x xs)`;;

export_thm is_parser_def;;

let parser_exists = prove
 (`?(p : A -> A pstream -> (B # A pstream) option). is_parser p`,
  EXISTS_TAC `\(x:A) (s:A pstream). (NONE : (B # A pstream) option)` THEN
  REWRITE_TAC [is_parser_def; case_option_def]);;

let (mk_dest_parser,dest_mk_parser) =
  let tybij =
    new_type_definition "parser" ("mk_parser","dest_parser") parser_exists in
  CONJ_PAIR tybij;;

export_thm mk_dest_parser;;
export_thm dest_mk_parser;;

let parser_tybij = CONJ mk_dest_parser dest_mk_parser;;

let (apply_parser_error,apply_parser_eof,apply_parser_cons) =
  let def = new_recursive_definition pstream_recursion
    `(!p : (A,B) parser. apply_parser p ErrorPstream = NONE) /\
     (!p : (A,B) parser. apply_parser p EofPstream = NONE) /\
     (!p : (A,B) parser. !x xs.
        apply_parser p (ConsPstream x xs) = dest_parser p x xs)` in
  CONJ_TRIPLE def;;

export_thm apply_parser_error;;
export_thm apply_parser_eof;;
export_thm apply_parser_cons;;

let apply_parser_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ apply_parser_error (CONJ apply_parser_eof apply_parser_cons));;

(* Parser inverses *)

let parser_inverse_def = new_definition
  `!p e.
     parser_inverse p (e : B -> A list) <=>
     !x xs. apply_parser p (append_pstream (e x) xs) = SOME (x,xs)`;;

export_thm parser_inverse_def;;

let parser_strong_inverse_def = new_definition
  `!p e.
     parser_strong_inverse p (e : B -> A list) <=>
     parser_inverse p e /\
     !xs y ys.
       apply_parser p xs = SOME (y,ys) ==>
       xs = append_pstream (e y) ys`;;

export_thm parser_strong_inverse_def;;

(* Primitive parser combinators *)

let parse_token_def = new_definition
  `!(f : A -> B option) (x : A) (xs : A pstream).
     parse_token f x xs =
     case_option
       NONE
       (\y. SOME (y,xs))
       (f x)`;;

export_thm parse_token_def;;

let parser_token_def = new_definition
  `!(f : A -> B option). parser_token f = mk_parser (parse_token f)`;;

export_thm parser_token_def;;

let parse_sequence_def = new_definition
  `!(p : (A, (A,B) parser) parser) x xs.
     parse_sequence p x xs =
     case_option
       NONE
       (\ (q,ys). apply_parser q ys)
       (dest_parser p x xs)`;;

export_thm parse_sequence_def;;

let parser_sequence_def = new_definition
  `!p : (A, (A,B) parser) parser.
     parser_sequence p = mk_parser (parse_sequence p)`;;

export_thm parser_sequence_def;;

let parse_orelse_def = new_definition
  `!(p1 : (A,B) parser) p2 x xs.
     parse_orelse p1 p2 x xs =
     case_option
       (dest_parser p2 x xs)
       (\yys. SOME yys)
       (dest_parser p1 x xs)`;;

export_thm parse_orelse_def;;

let parser_orelse_def = new_definition
  `!(p1 : (A,B) parser) p2.
     parser_orelse p1 p2 = mk_parser (parse_orelse p1 p2)`;;

export_thm parser_orelse_def;;

let parse_map_partial_def = new_definition
  `!(p : (A,B) parser) (f : B -> C option) x xs.
     parse_map_partial p f x xs =
     case_option
       NONE
       (\ (y,ys). case_option NONE (\z. SOME (z,ys)) (f y))
       (dest_parser p x xs)`;;

export_thm parse_map_partial_def;;

let parser_map_partial_def = new_definition
  `!(p : (A,B) parser) (f : B -> C option).
     parser_map_partial p f = mk_parser (parse_map_partial p f)`;;

export_thm parser_map_partial_def;;

(* Derived parser combinators *)

let parser_none_def = new_definition
  `(parser_none : (A,B) parser) = parser_token (K NONE)`;;

export_thm parser_none_def;;

let parser_some_def = new_definition
  `!p.
     parser_some (p : A -> bool) =
     parser_token (\x. if p x then SOME x else NONE)`;;

export_thm parser_some_def;;

let parser_any_def = new_definition
  `(parser_any : (A,A) parser) = parser_some (K T)`;;

export_thm parser_any_def;;

let parser_map_def = new_definition
  `!(p : (A,B) parser) (f : B -> C).
     parser_map p f = parser_map_partial p (\x. SOME (f x))`;;

export_thm parser_map_def;;

let parser_filter_def = new_definition
  `!(p : (A,B) parser) (f : B -> bool).
     parser_filter p f =
     parser_map_partial p (\x. if f x then SOME x else NONE)`;;

export_thm parser_filter_def;;

let parser_pair_def = new_definition
  `!(p1 : (A,B) parser) (p2 : (A,C) parser).
     parser_pair p1 p2 =
     parser_sequence (parser_map p1 (\x. parser_map p2 (\y. (x,y))))`;;

export_thm parser_pair_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of stream parser combinators.                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-comb-thm";;

let dest_is_parser = prove
 (`!p : (A,B) parser. is_parser (dest_parser p)`,
  REWRITE_TAC [parser_tybij]);;

export_thm dest_is_parser;;

let dest_parser_inj = prove
 (`!p1 p2 : (A,B) parser. dest_parser p1 = dest_parser p2 <=> p1 = p2`,
  REPEAT GEN_TAC THEN
  EQ_TAC THENL
  [STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM mk_dest_parser] THEN
   ASM_REWRITE_TAC [];
   STRIP_TAC THEN
   ASM_REWRITE_TAC []]);;

export_thm dest_parser_inj;;

let is_parser_cases = prove
 (`!(p : A -> A pstream -> (B # A pstream) option) x xs.
      is_parser p ==>
      (p x xs = NONE) \/
      (?y ys. p x xs = SOME (y,ys) /\ is_suffix_pstream ys xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [is_parser_def] THEN
  DISCH_THEN (MP_TAC o SPECL [`x : A`; `xs : A pstream`]) THEN
  MP_TAC
    (ISPEC `(p : A -> A pstream -> (B # A pstream) option) x xs`
       option_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST1_TAC
       (X_CHOOSE_THEN `yys : (B # A pstream)` SUBST1_TAC)) THEN
  REWRITE_TAC [case_option_def] THEN
  MP_TAC (ISPEC `yys : B # A pstream` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `y : B`
       (X_CHOOSE_THEN `ys : A pstream` SUBST_VAR_TAC)) THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  DISJ2_TAC THEN
  EXISTS_TAC `y : B` THEN
  EXISTS_TAC `ys : A pstream` THEN
  ASM_REWRITE_TAC []);;

export_thm is_parser_cases;;

let dest_parser_cases = prove
 (`!(p : (A,B) parser) x xs.
      (dest_parser p x xs = NONE) \/
      (?y ys. dest_parser p x xs = SOME (y,ys) /\ is_suffix_pstream ys xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPECL [`dest_parser (p : (A,B) parser)`; `x : A`; `xs : A pstream`]
            is_parser_cases) THEN
  REWRITE_TAC [dest_is_parser]);;

export_thm dest_parser_cases;;

let dest_parser_suffix_pstream = prove
 (`!(p : (A,B) parser) x xs y ys.
      dest_parser p x xs = SOME (y,ys) ==> is_suffix_pstream ys xs`,
  REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  MP_TAC (SPECL [`p : (A,B) parser`; `x : A`; `xs : A pstream`]
            dest_parser_cases) THEN
  ASM_REWRITE_TAC [option_distinct; option_inj; PAIR_EQ] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm dest_parser_suffix_pstream;;

let apply_parser_cases = prove
 (`!(p : (A,B) parser) xs.
     (apply_parser p xs = NONE) \/
     (?y ys.
        apply_parser p xs = SOME (y,ys) /\
        is_proper_suffix_pstream ys xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `x : A`
          (X_CHOOSE_THEN `xt : A pstream` SUBST_VAR_TAC)))) THEN
  REWRITE_TAC [apply_parser_def] THEN
  MP_TAC (SPECL [`p : (A,B) parser`; `x : A`; `xt : A pstream`]
            dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [] THEN
  DISJ2_TAC THEN
  EXISTS_TAC `y : B` THEN
  EXISTS_TAC `ys : A pstream` THEN
  ASM_REWRITE_TAC [is_proper_suffix_pstream_def]);;

export_thm apply_parser_cases;;

let is_parser_token = prove
 (`!f : A -> B option. is_parser (parse_token f)`,
  REWRITE_TAC [is_parser_def; parse_token_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `(f : A -> B option) x` option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def; is_suffix_pstream_refl]);;

export_thm is_parser_token;;

let dest_parser_token = prove
 (`!f : A -> B option. dest_parser (parser_token f) = parse_token f`,
  REWRITE_TAC
    [parser_token_def; GSYM (CONJUNCT2 parser_tybij); is_parser_token]);;

export_thm dest_parser_token;;

let apply_parser_token = prove
 (`!f : A -> B option.
     apply_parser (parser_token f) =
     case_pstream
       NONE
       NONE
       (\x xs. case_option NONE (\y. SOME (y,xs)) (f x))`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `xs : A pstream` THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_def; case_pstream_def; dest_parser_token; parse_token_def]);;

export_thm apply_parser_token;;

let parser_token_inverse = prove
 (`!(f : A -> B option) e.
      (!x. f (e x) = SOME x) ==>
      parser_inverse (parser_token f) (\x. CONS (e x) [])`,
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_token; append_pstream_def; case_pstream_def;
     case_option_def]);;

export_thm parser_token_inverse;;

let parser_token_strong_inverse = prove
 (`!(f : A -> B option) e.
     (!x. f (e x) = SOME x) /\
     (!y1 y2 x. f y1 = SOME x /\ f y2 = SOME x ==> y1 = y2) ==>
     parser_strong_inverse (parser_token f) (\x. CONS (e x) [])`,
  REWRITE_TAC [parser_strong_inverse_def] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC parser_token_inverse THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_token; append_pstream_def] THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_pstream_def; option_distinct; pstream_inj] THEN
  MP_TAC (ISPEC `(f : A -> B option) x` option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
  DISCH_THEN (CONJUNCTS_THEN SUBST_VAR_TAC) THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `y : B` THEN
  ASM_REWRITE_TAC []);;

export_thm parser_token_strong_inverse;;

let is_parser_sequence = prove
 (`!p : (A, (A,B) parser) parser. is_parser (parse_sequence p)`,
  GEN_TAC THEN
  REWRITE_TAC [is_parser_def; parse_sequence_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC
    (ISPECL [`p : (A, (A,B) parser) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  MP_TAC
    (ISPECL [`y : (A,B) parser`; `ys : A pstream`]
       apply_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `z : B`
          (X_CHOOSE_THEN `zs : A pstream` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  MATCH_MP_TAC is_suffix_pstream_trans THEN
  EXISTS_TAC `ys : A pstream` THEN
  ASM_REWRITE_TAC [] THEN
  MATCH_MP_TAC is_suffix_pstream_proper THEN
  ASM_REWRITE_TAC []);;

export_thm is_parser_sequence;;

let dest_parser_sequence = prove
 (`!p : (A, (A,B) parser) parser.
     dest_parser (parser_sequence p) = parse_sequence p`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_sequence_def; GSYM (CONJUNCT2 parser_tybij); is_parser_sequence]);;

export_thm dest_parser_sequence;;

let apply_parser_sequence = prove
 (`!(p : (A, (A,B) parser) parser) xs.
     apply_parser (parser_sequence p) xs =
     case_option
       NONE
       (\ (y,ys). apply_parser y ys)
       (apply_parser p xs)`,
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [apply_parser_def; case_option_def] THEN
   REWRITE_TAC [dest_parser_sequence; parse_sequence_def]);;

export_thm apply_parser_sequence;;

let is_parser_orelse = prove
 (`!p1 p2 : (A,B) parser. is_parser (parse_orelse p1 p2)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [is_parser_def; parse_orelse_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC
    (ISPECL [`p1 : (A,B) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  MP_TAC
    (ISPECL [`p2 : (A,B) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def]);;

export_thm is_parser_orelse;;

let dest_parser_orelse = prove
 (`!p1 p2 : (A,B) parser.
     dest_parser (parser_orelse p1 p2) = parse_orelse p1 p2`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_orelse_def; GSYM (CONJUNCT2 parser_tybij); is_parser_orelse]);;

export_thm dest_parser_orelse;;

let apply_parser_orelse = prove
 (`!(p1 : (A,B) parser) p2 xs.
     apply_parser (parser_orelse p1 p2) xs =
     case_option
       (apply_parser p2 xs)
       (\yys. SOME yys)
       (apply_parser p1 xs)`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [apply_parser_def; case_option_def] THEN
   REWRITE_TAC [dest_parser_orelse; parse_orelse_def]);;

export_thm apply_parser_orelse;;

let is_parser_map_partial = prove
 (`!(p : (A,B) parser) (f : B -> C option).
     is_parser (parse_map_partial p f)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [is_parser_def; parse_map_partial_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC
    (ISPECL [`p : (A,B) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  MP_TAC (ISPECL [`(f : B -> C option) y`] option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def]);;

export_thm is_parser_map_partial;;

let dest_parser_map_partial = prove
 (`!(p : (A,B) parser) (f : B -> C option).
     dest_parser (parser_map_partial p f) = parse_map_partial p f`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_map_partial_def; GSYM (CONJUNCT2 parser_tybij);
     is_parser_map_partial]);;

export_thm dest_parser_map_partial;;

let apply_parser_map_partial = prove
 (`!(p : (A,B) parser) (f : B -> C option) xs.
     apply_parser (parser_map_partial p f) xs =
     case_option
       NONE
       (\ (y,ys). case_option NONE (\z. SOME (z,ys)) (f y))
       (apply_parser p xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_def; case_option_def] THEN
  REWRITE_TAC [dest_parser_map_partial; parse_map_partial_def]);;

export_thm apply_parser_map_partial;;

let parser_map_partial_inverse = prove
 (`!(p : (A,B) parser) (f : B -> C option) g e.
     parser_inverse p e /\
     (!x. f (g x) = SOME x) ==>
     parser_inverse (parser_map_partial p f) (\x. e (g x))`,
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_map_partial; append_pstream_def; case_pstream_def;
     case_option_def]);;

export_thm parser_map_partial_inverse;;

let parser_map_partial_strong_inverse = prove
 (`!(p : (A,B) parser) (f : B -> C option) g e.
     parser_strong_inverse p e /\
     (!x. f (g x) = SOME x) /\
     (!y1 y2 x. f y1 = SOME x /\ f y2 = SOME x ==> y1 = y2) ==>
     parser_strong_inverse (parser_map_partial p f) (\x. e (g x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_strong_inverse_def] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC parser_map_partial_inverse THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_map_partial; append_pstream_def] THEN
  MP_TAC
    (ISPECL [`p : (A,B) parser`; `xs : A pstream`] apply_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `z : B`
        (X_CHOOSE_THEN `zs : A pstream` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
  MP_TAC (ISPEC `(f : B -> C option) z` option_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `w : C` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `w : C` THEN
  ASM_REWRITE_TAC []);;

export_thm parser_map_partial_strong_inverse;;

let dest_parser_none = prove
 (`!x xs. dest_parser (parser_none : (A,B) parser) x xs = NONE`,
  REWRITE_TAC
    [parser_none_def; dest_parser_token; parse_token_def; K_THM;
     case_option_def]);;

export_thm dest_parser_none;;

let apply_parser_none = prove
 (`!xs. apply_parser (parser_none : (A,B) parser) xs = NONE`,
  GEN_TAC THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_def; case_pstream_def; case_option_def; dest_parser_none]);;

export_thm apply_parser_none;;

let dest_parser_some = prove
 (`!p (x : A) xs.
     dest_parser (parser_some p) x xs =
     if p x then SOME (x,xs) else NONE`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_some_def; dest_parser_token; parse_token_def] THEN
  BOOL_CASES_TAC `(p : A -> bool) x` THEN
  REWRITE_TAC [case_option_def]);;

export_thm dest_parser_some;;

let apply_parser_some = prove
 (`!p : A -> bool.
     apply_parser (parser_some p) =
     case_pstream
       NONE
       NONE
       (\x xs. if p x then SOME (x,xs) else NONE)`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `xs : A pstream` THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_def; case_pstream_def; dest_parser_some]);;

export_thm apply_parser_some;;

let dest_parser_any = prove
 (`!(x : A) xs. dest_parser parser_any x xs = SOME (x,xs)`,
  REWRITE_TAC [parser_any_def; dest_parser_some; K_THM]);;

export_thm dest_parser_any;;

let apply_parser_any = prove
 (`apply_parser (parser_any : (A,A) parser) =
   case_pstream NONE NONE (\x xs. SOME (x,xs))`,
  REWRITE_TAC [parser_any_def; apply_parser_some; K_THM]);;

export_thm apply_parser_any;;

let parser_any_inverse = prove
 (`parser_inverse (parser_any : (A,A) parser) (\x. CONS x [])`,
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_any; append_pstream_def; case_pstream_def;
     case_option_def]);;

export_thm parser_any_inverse;;

let parser_any_strong_inverse = prove
 (`parser_strong_inverse (parser_any : (A,A) parser) (\x. CONS x [])`,
  REWRITE_TAC [parser_strong_inverse_def; parser_any_inverse] THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [apply_parser_any; append_pstream_def] THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC
    [case_pstream_def; option_distinct; option_inj; PAIR_EQ; pstream_inj]);;

export_thm parser_any_strong_inverse;;

let parser_map_partial_any = prove
 (`!(f : A -> B option). parser_map_partial parser_any f = parser_token f`,
  GEN_TAC THEN
  ONCE_REWRITE_TAC [GSYM dest_parser_inj] THEN
  REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `x : A` THEN
  X_GEN_TAC `xs : A pstream` THEN
  REWRITE_TAC
    [dest_parser_map_partial; parse_map_partial_def; dest_parser_token;
     parse_token_def; dest_parser_any; case_option_def]);;

export_thm parser_map_partial_any;;

let dest_parser_map = prove
 (`!(p : (A,B) parser) (f : B -> C) x xs.
     dest_parser (parser_map p f) x xs =
     case_option
       NONE
       (\ (y,ys). SOME (f y, ys))
       (dest_parser p x xs)`,
  REWRITE_TAC
    [parser_map_def; dest_parser_map_partial; parse_map_partial_def;
     case_option_def]);;

export_thm dest_parser_map;;

let apply_parser_map = prove
 (`!(p : (A,B) parser) (f : B -> C) xs.
     apply_parser (parser_map p f) xs =
     case_option
       NONE
       (\ (y,ys). SOME (f y, ys))
       (apply_parser p xs)`,
  REWRITE_TAC [parser_map_def; apply_parser_map_partial; case_option_def]);;

export_thm apply_parser_map;;

let parser_map_inverse = prove
 (`!(p : (A,B) parser) (f : B -> C) g e.
     parser_inverse p e /\
     (!x. f (g x) = x) ==>
     parser_inverse (parser_map p f) (\x. e (g x))`,
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC
    [apply_parser_map; append_pstream_def; case_pstream_def;
     case_option_def]);;

export_thm parser_map_inverse;;

let parser_map_strong_inverse = prove
 (`!(p : (A,B) parser) (f : B -> C) g e.
     parser_strong_inverse p e /\
     (!x. f (g x) = x) /\
     (!y1 y2 x. f y1 = x /\ f y2 = x ==> y1 = y2) ==>
     parser_strong_inverse (parser_map p f) (\x. e (g x))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_strong_inverse_def] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC parser_map_inverse THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_map] THEN
  MP_TAC (ISPECL [`p : (A,B) parser`; `xs : A pstream`] apply_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `z : B`
          (X_CHOOSE_THEN `zs : A pstream` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `y : C` THEN
  ASM_REWRITE_TAC []);;

export_thm parser_map_strong_inverse;;

let dest_parser_filter = prove
 (`!(p : (A,B) parser) (f : B -> bool) x xs.
     dest_parser (parser_filter p f) x xs =
     case_option
       NONE
       (\ (y,ys). if f y then SOME (y,ys) else NONE)
       (dest_parser p x xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_filter_def; dest_parser_map_partial; parse_map_partial_def] THEN
  MP_TAC
    (ISPECL
       [`p : (A,B) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [case_option_def]);;

export_thm dest_parser_filter;;

let apply_parser_filter = prove
 (`!(p : (A,B) parser) (f : B -> bool) xs.
     apply_parser (parser_filter p f) xs =
     case_option
       NONE
       (\ (y,ys). if f y then SOME (y,ys) else NONE)
       (apply_parser p xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_filter_def; apply_parser_map_partial] THEN
  MP_TAC
    (ISPECL
       [`p : (A,B) parser`; `xs : A pstream`]
       apply_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  COND_CASES_TAC THEN
  REWRITE_TAC [case_option_def]);;

export_thm apply_parser_filter;;

let parser_filter_any = prove
 (`!(p : A -> bool). parser_filter parser_any p = parser_some p`,
  REWRITE_TAC [parser_filter_def; parser_map_partial_any; parser_some_def]);;

export_thm parser_filter_any;;

let dest_parser_pair = prove
 (`!(p1 : (A,B) parser) (p2 : (A,C) parser) x xs.
     dest_parser (parser_pair p1 p2) x xs =
     case_option
       NONE
       (\ (y,ys).
          case_option
            NONE
            (\ (z,zs). SOME ((y,z),zs))
            (apply_parser p2 ys))
       (dest_parser p1 x xs)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_pair_def; dest_parser_sequence; parse_sequence_def;
     dest_parser_map] THEN
  MP_TAC
    (ISPECL [`p1 : (A,B) parser`; `x : A`; `xs : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  REWRITE_TAC [apply_parser_map]);;

export_thm dest_parser_pair;;

let apply_parser_pair = prove
 (`!(p1 : (A,B) parser) (p2 : (A,C) parser) xs.
     apply_parser (parser_pair p1 p2) xs =
     case_option
       NONE
       (\ (y,ys).
          case_option
            NONE
            (\ (z,zs). SOME ((y,z),zs))
            (apply_parser p2 ys))
       (apply_parser p1 xs)`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [apply_parser_def; case_option_def] THEN
   REWRITE_TAC [dest_parser_pair]);;

export_thm apply_parser_pair;;

let parser_pair_inverse = prove
 (`!(p1 : (A,B) parser) (p2 : (A,C) parser) e1 e2.
     parser_inverse p1 e1 /\ parser_inverse p2 e2 ==>
     parser_inverse (parser_pair p1 p2) (\ (x1,x2). APPEND (e1 x1) (e2 x2))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [apply_parser_pair] THEN
  MP_TAC (ISPEC `x : B # C` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `y : B`
       (X_CHOOSE_THEN `z : C` SUBST_VAR_TAC)) THEN
  ASM_REWRITE_TAC [append_pstream_assoc; case_option_def]);;

export_thm parser_pair_inverse;;

let parser_pair_strong_inverse = prove
 (`!(p1 : (A,B) parser) (p2 : (A,C) parser) e1 e2.
     parser_strong_inverse p1 e1 /\ parser_strong_inverse p2 e2 ==>
     parser_strong_inverse (parser_pair p1 p2)
       (\ (x1,x2). APPEND (e1 x1) (e2 x2))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [parser_strong_inverse_def] THEN
  REPEAT STRIP_TAC THENL
  [MATCH_MP_TAC parser_pair_inverse THEN
   ASM_REWRITE_TAC [];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  MP_TAC (ISPEC `y : B # C` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `x1 : B`
       (X_CHOOSE_THEN `x2 : C` SUBST_VAR_TAC)) THEN
  ASM_REWRITE_TAC [apply_parser_pair; append_pstream_assoc] THEN
  MP_TAC
    (ISPECL [`p1 : (A,B) parser`; `xs : A pstream`] apply_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `z : B`
          (X_CHOOSE_THEN `zs : A pstream` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
  MP_TAC
    (ISPECL [`p2 : (A,C) parser`; `zs : A pstream`] apply_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `w : C`
          (X_CHOOSE_THEN `ws : A pstream` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
  REWRITE_TAC [option_inj; PAIR_EQ] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC []);;

export_thm parser_pair_strong_inverse;;

let apply_parser_src = prove
 (`(!p : (A,B) parser. apply_parser p ErrorPstream = NONE) /\
   (!p : (A,B) parser. apply_parser p EofPstream = NONE) /\
   (!p : (A,B) parser. !x xs.
      apply_parser p (ConsPstream x xs) = dest_parser p x xs)`,
  REWRITE_TAC [apply_parser_def]);;

export_thm apply_parser_src;;

(* ------------------------------------------------------------------------- *)
(* Definition of the fold parsers.                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-fold-def";;

let parse_fold_exists = prove
 (`!(f : A -> C -> (B + C) option). ?g. !s x xs.
     g s x xs =
     case_option
       NONE
       (\y.
          case_sum
            (\z. SOME (z,xs))
            (\t.
               case_pstream
                 NONE
                 NONE
                 (\z zs. g t z zs)
                 xs)
            y)
       (f x s)`,
  GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ ((s : C), (x : A), (xs : A pstream)).
          case_option
            F
            (\y : B + C.
               case_sum
                 (\z. F)
                 (\t.
                    case_pstream
                      F
                      F
                      (\z zs. T)
                      xs)
                 y)
            (f x s)`;
       `\ ((s : C), (x : A), (xs : A pstream)).
          case_option
            (s,x,xs)
            (\y : B + C.
               case_sum
                 (\z. (s,x,xs))
                 (\t.
                    case_pstream
                      (s,x,xs)
                      (s,x,xs)
                      (\z zs. (t,z,zs))
                      xs)
                 y)
            (f x s)`;
       `\ ((s : C), (x : A), (xs : A pstream)).
          case_option
            NONE
            (\y : B + C.
               case_sum
                 (\z. SOME (z,xs))
                 (\t.
                    case_pstream
                      NONE
                      NONE
                      (\z zs. NONE)
                      xs)
                 y)
            (f x s)`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ps : (C # A # A pstream) -> (B # A pstream) option`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
    `\ (s : C) (x : A) (xs : A pstream).
       (ps (s,x,xs) : (B # A pstream) option)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [] THEN
  MP_TAC (ISPEC `(f : A -> C -> (B + C) option) x s` option_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `y : B + C` SUBST1_TAC)) THEN
  REWRITE_TAC [case_option_def] THEN
  MP_TAC (ISPEC `y : B + C` sum_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `z : B` SUBST1_TAC)
       (X_CHOOSE_THEN `t : C` SUBST1_TAC)) THEN
  REWRITE_TAC [case_sum_def] THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (DISJ_CASES_THEN2 SUBST1_TAC
          (X_CHOOSE_THEN `z : A`
             (X_CHOOSE_THEN `z : A pstream` SUBST1_TAC)))) THEN
  REWRITE_TAC [case_pstream_def]);;

let parse_fold_def =
  new_specification ["parse_fold"]
    (REWRITE_RULE [SKOLEM_THM] parse_fold_exists);;

export_thm parse_fold_def;;

let parser_fold_def = new_definition
  `!(f : A -> C -> (B + C) option) s.
     parser_fold f s = mk_parser (parse_fold f s)`;;

export_thm parser_fold_def;;

let parser_foldn_def = new_definition
  `!(f : A -> B -> B option) n s.
     parser_foldn f n s =
     parser_fold
       (\x (m,t).
          map_option
            (\u. if m = 0 then INL u else INR (m - 1, u))
            (f x t))
       (n,s)`;;

export_thm parser_foldn_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of the fold parsers.                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-fold-thm";;

let is_parser_fold = prove
 (`!(f : A -> C -> (B + C) option) s. is_parser (parse_fold f s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [is_parser_def] THEN
  REPEAT GEN_TAC THEN
  SPEC_TAC (`s : C`, `s : C`) THEN
  SPEC_TAC (`x : A`, `x : A`) THEN
  SPEC_TAC (`xs : A pstream`, `xs : A pstream`) THEN
  MATCH_MP_TAC pstream_induct THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [parse_fold_def] THEN
   MP_TAC (ISPEC `(f : A -> C -> (B + C) option) x s` option_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `y : B + C` SUBST1_TAC)) THEN
   REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `y : B + C` sum_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `z : B` SUBST1_TAC)
        (X_CHOOSE_THEN `t : C` SUBST1_TAC)) THEN
   REWRITE_TAC
     [case_sum_def; case_option_def; case_pstream_def; is_suffix_pstream_refl];
   ALL_TAC] THEN
  CONJ_TAC THENL
  [REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [parse_fold_def] THEN
   MP_TAC (ISPEC `(f : A -> C -> (B + C) option) x s` option_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `y : B + C` SUBST1_TAC)) THEN
   REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `y : B + C` sum_CASES) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2
        (X_CHOOSE_THEN `z : B` SUBST1_TAC)
        (X_CHOOSE_THEN `t : C` SUBST1_TAC)) THEN
   REWRITE_TAC
     [case_sum_def; case_option_def; case_pstream_def; is_suffix_pstream_refl];
   ALL_TAC] THEN
  X_GEN_TAC `z : A` THEN
  X_GEN_TAC `zs : A pstream` THEN
  STRIP_TAC THEN
  X_GEN_TAC `x : A` THEN
  X_GEN_TAC `s : C` THEN
  ONCE_REWRITE_TAC [parse_fold_def] THEN
  MP_TAC (ISPEC `(f : A -> C -> (B + C) option) x s` option_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `y : B + C` SUBST1_TAC)) THEN
  REWRITE_TAC [case_option_def] THEN
  MP_TAC (ISPEC `y : B + C` sum_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       (X_CHOOSE_THEN `w : B` SUBST1_TAC)
       (X_CHOOSE_THEN `t : C` SUBST1_TAC)) THEN
  REWRITE_TAC
    [case_sum_def; case_option_def; case_pstream_def;
     is_suffix_pstream_refl] THEN
  POP_ASSUM (MP_TAC o SPECL [`z : A`; `t : C`]) THEN
  MP_TAC
    (ISPEC
       `parse_fold (f : A -> C -> (B + C) option) t z zs`
       option_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `yys : B # A pstream` SUBST1_TAC)) THEN
  REWRITE_TAC [case_option_def] THEN
  MP_TAC (ISPEC `yys : B # A pstream` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `y : B`
       (X_CHOOSE_THEN `ys : A pstream` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC is_suffix_pstream_proper THEN
  ASM_REWRITE_TAC [is_proper_suffix_pstream_def]);;

export_thm is_parser_fold;;

let dest_parser_fold = prove
 (`!(f : A -> C -> (B + C) option) s.
      dest_parser (parser_fold f s) = parse_fold f s`,
  REWRITE_TAC
    [parser_fold_def; GSYM (CONJUNCT2 parser_tybij); is_parser_fold]);;

export_thm dest_parser_fold;;

let apply_parser_fold = prove
 (`!(f : A -> C -> (B + C) option) s.
     apply_parser (parser_fold f s) =
     case_pstream
       NONE
       NONE
       (\x xs. parse_fold f s x xs)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
  X_GEN_TAC `xs : A pstream` THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [apply_parser_def; case_pstream_def; dest_parser_fold]);;

export_thm apply_parser_fold;;

let parser_fold_src = prove
 (`!f : A -> C -> (B + C) option.
     parser_fold f = mk_parser o parse_fold f`,
  REWRITE_TAC [FUN_EQ_THM; parser_fold_def; o_THM]);;

export_thm parser_fold_src;;

(* ------------------------------------------------------------------------- *)
(* Definition of the whole stream parser.                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-all-def";;

let parse_exists = prove
 (`!(p : (A,B) parser). ?f.
     (f ErrorPstream = ErrorPstream) /\
     (f EofPstream = EofPstream) /\
     (!x xs.
        f (ConsPstream x xs) =
          case_option
            ErrorPstream
            (\ (y,ys). ConsPstream y (f ys))
            (dest_parser p x xs))`,
  GEN_TAC THEN
  REVERSE_TAC
    (SUBGOAL_THEN
       `?f : A pstream -> B pstream. !xs.
          f xs =
          (\g.
             case_pstream
               ErrorPstream
               EofPstream
               (\x xt.
                  case_option
                    ErrorPstream
                    (\ (y,ys). ConsPstream y (g ys))
                    (dest_parser p x xt))) f xs`
        STRIP_ASSUME_TAC) THENL
  [EXISTS_TAC `f : A pstream -> B pstream` THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (fun th -> CONV_TAC (LAND_CONV (REWR_CONV th))) THEN
   ASM_REWRITE_TAC [case_pstream_def];
   ALL_TAC] THEN
  MATCH_MP_TAC is_proper_suffix_pstream_recursion THEN
  REPEAT STRIP_TAC THEN
  MP_TAC (SPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_pstream_def] THEN
  MP_TAC
    (ISPECL [`p : (A,B) parser`; `x : A`; `xt : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [is_proper_suffix_pstream_def]);;

let (parse_error,parse_eof,parse_cons) =
  let def =
    new_specification ["parse"]
    (REWRITE_RULE [SKOLEM_THM] parse_exists) in
  CONJ_TRIPLE (REWRITE_RULE [FORALL_AND_THM] def);;

export_thm parse_error;;
export_thm parse_eof;;
export_thm parse_cons;;

let parse_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ parse_error (CONJ parse_eof parse_cons));;

(* ------------------------------------------------------------------------- *)
(* Properties of the whole stream parser.                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-all-thm";;

let parse_apply = prove
 (`!(p : (A,B) parser) xs.
     parse p xs =
     case_option
       (case_pstream ErrorPstream EofPstream (\y ys. ErrorPstream) xs)
       (\ (y,ys). ConsPstream y (parse p ys))
       (apply_parser p xs)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `xs : A pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `x : A`
          (X_CHOOSE_THEN `xt : A pstream` SUBST_VAR_TAC)))) THEN
  REWRITE_TAC
    [parse_def; apply_parser_def; case_option_def; case_pstream_def]);;

export_thm parse_apply;;

let parse_map = prove
 (`!(p : (A,B) parser) (f : B -> C) xs.
     parse (parser_map p f) xs = map_pstream f (parse p xs)`,
  GEN_TAC THEN
  GEN_TAC THEN
  MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
  X_GEN_TAC `xs : A pstream` THEN
  STRIP_TAC THEN
  MP_TAC (SPEC `xs : A pstream` pstream_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST_VAR_TAC
      (DISJ_CASES_THEN2 SUBST_VAR_TAC
        (X_CHOOSE_THEN `x : A`
          (X_CHOOSE_THEN `xt : A pstream` SUBST_VAR_TAC)))) THENL
  [REWRITE_TAC [parse_def; map_pstream_def];
   REWRITE_TAC [parse_def; map_pstream_def];
   ALL_TAC] THEN
  REWRITE_TAC [parse_def; dest_parser_map] THEN
  MP_TAC
    (SPECL [`p : (A,B) parser`; `x : A`; `xt : A pstream`]
       dest_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `y : B`
        (X_CHOOSE_THEN `ys : A pstream` STRIP_ASSUME_TAC))) THENL
  [REWRITE_TAC [case_option_def; map_pstream_def];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [case_option_def; map_pstream_def] THEN
  AP_TERM_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC [is_proper_suffix_pstream_def]);;

export_thm parse_map;;

let parse_append = prove
 (`!(p : (A,B) parser) e x xs.
     parser_inverse p e ==>
     parse p (append_pstream (e x) xs) =
     ConsPstream x (parse p xs)`,
  REWRITE_TAC [parser_inverse_def] THEN
  REPEAT STRIP_TAC THEN
  POP_ASSUM (MP_TAC o SPECL [`x : B`; `xs : A pstream`]) THEN
  MP_TAC (ISPEC `(e : B -> A list) x` list_cases) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [append_pstream_def] THEN
   MP_TAC
     (ISPECL [`p : (A,B) parser`; `xs : A pstream`] apply_parser_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [option_distinct];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
   STRIP_TAC THEN
   SUBGOAL_THEN `F` CONTR_TAC THEN
   UNDISCH_TAC `is_proper_suffix_pstream ys (xs : A pstream)` THEN
   ASM_REWRITE_TAC [is_proper_suffix_pstream_refl];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [parse_def; apply_parser_def; append_pstream_def] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [case_option_def]);;

export_thm parse_append;;

let parse_inverse = prove
 (`!(p : (A,B) parser) e l.
     parser_inverse p e ==>
     parse p (list_to_pstream (concat (MAP e l))) =
     list_to_pstream l`,
  REPEAT STRIP_TAC THEN
  SPEC_TAC (`l : B list`, `l : B list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC
     [MAP; concat_def; parse_def; list_to_pstream_def; append_pstream_def];
   ALL_TAC] THEN
  POP_ASSUM MP_TAC THEN
  REWRITE_TAC
    [MAP; concat_def; parse_def; list_to_pstream_def; append_pstream_def] THEN
  DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
  REWRITE_TAC [append_pstream_assoc] THEN
  MATCH_MP_TAC parse_append THEN
  FIRST_ASSUM ACCEPT_TAC);;

export_thm parse_inverse;;

let parse_strong_inverse = prove
 (`!(p : (A,B) parser) e xs ys ye.
     parser_strong_inverse p e /\
     pstream_to_list (parse p xs) = (ys,ye) ==>
     ye \/ xs = list_to_pstream (concat (MAP e ys))`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM MP_TAC THEN
  SPEC_TAC (`ys : B list`, `ys : B list`) THEN
  SPEC_TAC (`xs : A pstream`, `xs : A pstream`) THEN
  MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
  GEN_TAC THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THENL
  [DISCH_THEN (K ALL_TAC) THEN
   GEN_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [pstream_to_list_def; parse_def; PAIR_EQ] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [];
   DISCH_THEN (K ALL_TAC) THEN
   GEN_TAC THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   PURE_REWRITE_TAC [pstream_to_list_def; parse_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [MAP; concat_def; list_to_pstream_def; append_pstream_def];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC
    [is_proper_suffix_pstream_def; pstream_to_list_def; parse_def;
     case_option_def; MAP; concat_def] THEN
  STRIP_TAC THEN
  GEN_TAC THEN
  MP_TAC
    (ISPECL [`p : (A,B) parser`; `x : A`; `xt : A pstream`]
       dest_parser_cases) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `z : B`
          (X_CHOOSE_THEN `zs : A pstream` STRIP_ASSUME_TAC))) THENL
  [PURE_REWRITE_TAC [case_option_def; pstream_to_list_def; PAIR_EQ] THEN
   DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
   REWRITE_TAC [];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [case_option_def; pstream_to_list_def] THEN
  MP_TAC
    (ISPEC
       `pstream_to_list (parse (p : (A,B) parser) zs)`
       PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `ws : B list`
       (X_CHOOSE_THEN `we : bool` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF; PAIR_EQ] THEN
  DISCH_THEN (CONJUNCTS_THEN (SUBST_VAR_TAC o SYM)) THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `zs : A pstream`) THEN
  ASM_REWRITE_TAC [] THEN
  DISCH_THEN (MP_TAC o SPEC `ws : B list`) THEN
  REWRITE_TAC [] THEN
  ASM_CASES_TAC `we : bool` THEN
  ASM_REWRITE_TAC [] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM
    (STRIP_ASSUME_TAC o CONV_RULE (REWR_CONV parser_strong_inverse_def)) THEN
  POP_ASSUM
    (MP_TAC o
     SPECL [`ConsPstream (x : A) xt`; `z : B`; `zs : A pstream`]) THEN
  ASM_REWRITE_TAC [apply_parser_def] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC [MAP; concat_def; list_to_pstream_def; append_pstream_assoc]);;

export_thm parse_strong_inverse;;

let parse_length = prove
 (`!(p : (A,B) parser) xs.
     length_pstream (parse p xs) <= length_pstream xs`,
  GEN_TAC THEN
  MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
  GEN_TAC THEN
  MP_TAC (ISPEC `xs : A pstream` pstream_cases) THEN
  STRIP_TAC THENL
  [POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [length_pstream_def; parse_def; LE_REFL];
   POP_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [length_pstream_def; parse_def; LE_REFL];
   ALL_TAC] THEN
  POP_ASSUM SUBST_VAR_TAC THEN
  STRIP_TAC THEN
  REWRITE_TAC [parse_def] THEN
  MP_TAC
    (ISPECL [`p : (A,B) parser`; `x : A`; `xt : A pstream`]
       dest_parser_cases) THEN
  STRIP_TAC THENL
  [ASM_REWRITE_TAC [case_option_def; length_pstream_def; LE_0];
   ALL_TAC] THEN
  ASM_REWRITE_TAC [case_option_def] THEN
  REWRITE_TAC [length_pstream_def; LE_SUC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `length_pstream (ys : A pstream)` THEN
  CONJ_TAC THENL
  [FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC [is_proper_suffix_pstream_def];
   MATCH_MP_TAC is_suffix_pstream_length THEN
   FIRST_ASSUM ACCEPT_TAC]);;

export_thm parse_length;;

let parse_src = prove
 (`(!p : (A,B) parser. parse p ErrorPstream = ErrorPstream) /\
   (!p : (A,B) parser. parse p EofPstream = EofPstream) /\
   (!p : (A,B) parser. !x xs.
      parse p (ConsPstream x xs) =
      case_option
        ErrorPstream
        (\(y,ys). ConsPstream y (parse p ys))
        (dest_parser p x xs))`,
  REWRITE_TAC [parse_def]);;

export_thm parse_src;;

(* ------------------------------------------------------------------------- *)
(* HOL Light theorem names.                                                  *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-hol-light-thm";;

export_theory_thm_names "parser"
  ["parser-stream-def";
   "parser-stream-thm";
   "parser-comb-def";
   "parser-comb-thm";
   "parser-fold-def";
   "parser-fold-thm";
   "parser-all-def";
   "parser-all-thm"];;

(* ------------------------------------------------------------------------- *)
(* Haskell source.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-haskell-src";;

export_thm case_pstream_def;;  (* Haskell *)
export_thm map_pstream_def;;  (* Haskell *)
export_thm length_pstream_src;;  (* Haskell *)
export_thm pstream_to_list_def;;  (* Haskell *)
export_thm append_pstream_def;;  (* Haskell *)
export_thm list_to_pstream_def;;  (* Haskell *)
export_thm arbitrary_pstream;;  (* Haskell *)
export_thm mk_dest_parser;;  (* Haskell *)
export_thm apply_parser_src;;  (* Haskell *)
export_thm parse_token_def;;  (* Haskell *)
export_thm parser_token_def;;  (* Haskell *)
export_thm parse_sequence_def;;  (* Haskell *)
export_thm parser_sequence_def;;  (* Haskell *)
export_thm parse_orelse_def;;  (* Haskell *)
export_thm parser_orelse_def;;  (* Haskell *)
export_thm parse_map_partial_def;;  (* Haskell *)
export_thm parser_map_partial_def;;  (* Haskell *)
export_thm parser_none_def;;  (* Haskell *)
export_thm parser_some_def;;  (* Haskell *)
export_thm parser_any_def;;  (* Haskell *)
export_thm parser_map_def;;  (* Haskell *)
export_thm parser_filter_def;;  (* Haskell *)
export_thm parser_pair_def;;  (* Haskell *)
export_thm parse_fold_def;;  (* Haskell *)
export_thm parser_fold_src;;  (* Haskell *)
export_thm parser_foldn_def;;  (* Haskell *)
export_thm parse_src;;  (* Haskell *)

(* ------------------------------------------------------------------------- *)
(* Haskell tests.                                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "parser-haskell-test";;

export_thm list_to_pstream_to_list;;  (* Haskell *)
export_thm length_fst_pstream_to_list;;  (* Haskell *)

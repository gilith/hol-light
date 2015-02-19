(* ========================================================================= *)
(* STREAM PARSERS                                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for stream parsers.                                       *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/parser/parser.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of parse streams.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "parser-stream-def";;

let (pstream_induct,pstream_recursion) = define_type
    "pstream = ErrorPstream
             | EofPstream
             | ConsPstream A pstream";;

export_thm pstream_induct;;
export_thm pstream_recursion;;

let (case_pstream_error,case_pstream_eof,case_pstream_cons) =
  let def = new_recursive_definition pstream_recursion
    `(!e b f. case_pstream e b f ErrorPstream = (e:B)) /\
     (!e b f. case_pstream e b f EofPstream = b) /\
     (!e b f a s. case_pstream e b f (ConsPstream a s) = f (a:A) s)` in
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
     (!f a s.
        map_pstream f (ConsPstream a s) =
        ConsPstream (f a) (map_pstream f s))` in
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
     (!(a:A) s. length_pstream (ConsPstream a s) = SUC (length_pstream s))` in
  CONJ_TRIPLE def;;

export_thm length_pstream_error;;
export_thm length_pstream_eof;;
export_thm length_pstream_cons;;

let length_pstream_def =
  CONJ length_pstream_error (CONJ length_pstream_eof length_pstream_cons);;

let (is_proper_suffix_pstream_error,
     is_proper_suffix_pstream_eof,
     is_proper_suffix_pstream_cons) =
  let def = new_recursive_definition pstream_recursion
  `(!s. is_proper_suffix_pstream s ErrorPstream = F) /\
   (!s. is_proper_suffix_pstream s EofPstream = F) /\
   (!s a s'. is_proper_suffix_pstream s (ConsPstream (a:A) s') =
      ((s = s') \/ is_proper_suffix_pstream s s'))` in
   CONJ_TRIPLE (REWRITE_RULE [] def);;

export_thm is_proper_suffix_pstream_error;;
export_thm is_proper_suffix_pstream_eof;;
export_thm is_proper_suffix_pstream_cons;;

let is_proper_suffix_pstream_def =
  CONJ is_proper_suffix_pstream_error
    (CONJ is_proper_suffix_pstream_eof is_proper_suffix_pstream_cons);;

let is_suffix_pstream_def = new_definition
  `!s s'.
     is_suffix_pstream s s' =
     (((s : A pstream) = s') \/ is_proper_suffix_pstream s s')`;;

export_thm is_suffix_pstream_def;;

let (pstream_to_list_error,
     pstream_to_list_eof,
     pstream_to_list_cons) =
  let def = new_recursive_definition pstream_recursion
    `(pstream_to_list ErrorPstream = NONE) /\
     (pstream_to_list EofPstream = SOME []) /\
     (!a s. pstream_to_list (ConsPstream a s) =
        case_option
          NONE
          (\l. SOME (CONS (a:A) l))
          (pstream_to_list s))` in
  CONJ_TRIPLE def;;

export_thm pstream_to_list_error;;
export_thm pstream_to_list_eof;;
export_thm pstream_to_list_cons;;

let pstream_to_list_def =
  CONJ pstream_to_list_error
    (CONJ pstream_to_list_eof pstream_to_list_cons);;

let (append_pstream_nil,append_pstream_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!s. append_pstream [] s = s) /\
     (!h t s. append_pstream (CONS h t) s = ConsPstream (h:A) (append_pstream t s))` in
  CONJ_PAIR def;;

export_thm append_pstream_nil;;
export_thm append_pstream_cons;;

let append_pstream_def = CONJ append_pstream_nil append_pstream_cons;;

let list_to_pstream_def = new_definition
  `!(l : A list). list_to_pstream l = append_pstream l EofPstream`;;

export_thm list_to_pstream_def;;

let rdecode_pstream_def = new_definition
  `!r.
     rdecode_pstream (d : random -> A # random) r =
     let (l,r') = rdecode_list d r in
     let (b,r'') = rbit r' in
     (append_pstream l (if b then ErrorPstream else EofPstream), r'')`;;

export_thm rdecode_pstream_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of parse streams.                                              *)
(* ------------------------------------------------------------------------- *)

logfile "parser-stream-thm";;

export_thm case_pstream_def;;
export_thm map_pstream_def;;
export_thm pstream_to_list_def;;
export_thm append_pstream_def;;

let pstream_cases = prove_cases_thm pstream_induct;;

export_thm pstream_cases;;

let (pstream_distinct_error_eof,
     pstream_distinct_error_cons,
     pstream_distinct_eof_cons) =
    CONJ_TRIPLE (prove_constructors_distinct pstream_recursion);;

export_thm pstream_distinct_error_eof;;
export_thm pstream_distinct_error_cons;;
export_thm pstream_distinct_eof_cons;;

let pstream_distinct =
    CONJ pstream_distinct_error_eof
      (CONJ pstream_distinct_error_cons pstream_distinct_eof_cons);;

let pstream_inj = prove_constructors_injective pstream_recursion;;

export_thm pstream_inj;;

let is_proper_suffix_pstream_trans = prove
  (`!x y z : A pstream.
      is_proper_suffix_pstream x y /\ is_proper_suffix_pstream y z ==>
      is_proper_suffix_pstream x z`,
   GEN_TAC THEN
   GEN_TAC THEN
   MATCH_MP_TAC pstream_induct THEN
   ASM_REWRITE_TAC [is_proper_suffix_pstream_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_MESON_TAC []);;

export_thm is_proper_suffix_pstream_trans;;

let is_proper_suffix_pstream_length = prove
  (`!x y : A pstream.
      is_proper_suffix_pstream x y ==> length_pstream x < length_pstream y`,
   GEN_TAC THEN
   MATCH_MP_TAC pstream_induct THEN
   ASM_REWRITE_TAC
     [is_proper_suffix_pstream_def; length_pstream_def; LT_SUC_LE] THEN
   REPEAT STRIP_TAC THEN
   ASM_MESON_TAC [LE_REFL; LT_IMP_LE]);;

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
  (`!x : A pstream. ~is_proper_suffix_pstream x x`,
   GEN_TAC THEN
   MATCH_MP_TAC WF_REFL THEN
   ACCEPT_TAC is_proper_suffix_pstream_wf);;

export_thm is_proper_suffix_pstream_refl;;

let is_proper_suffix_pstream_induct = prove
  (`!(p : A pstream -> bool).
       (!x. (!y. is_proper_suffix_pstream y x ==> p y) ==> p x) ==> !x. p x`,
   REWRITE_TAC [GSYM WF_IND; is_proper_suffix_pstream_wf]);;

export_thm is_proper_suffix_pstream_induct;;

let is_proper_suffix_pstream_recursion = prove
  (`!(h : (A pstream -> B) -> A pstream -> B).
       (!f g s.
          (!s'. is_proper_suffix_pstream s' s ==> (f s' = g s')) ==>
          (h f s = h g s)) ==>
       ?f. !s. f s = h f s`,
   MATCH_MP_TAC WF_REC THEN
   REWRITE_TAC [is_proper_suffix_pstream_wf]);;

export_thm is_proper_suffix_pstream_recursion;;

let is_suffix_pstream_proper = prove
  (`!x y : A pstream. is_proper_suffix_pstream x y ==> is_suffix_pstream x y`,
   SIMP_TAC [is_suffix_pstream_def]);;

export_thm is_suffix_pstream_proper;;

let is_suffix_pstream_refl = prove
  (`!x : A pstream. is_suffix_pstream x x`,
   SIMP_TAC [is_suffix_pstream_def]);;

export_thm is_suffix_pstream_refl;;

let is_suffix_pstream_trans = prove
  (`!x y z : A pstream.
      is_suffix_pstream x y /\ is_suffix_pstream y z ==>
      is_suffix_pstream x z`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_suffix_pstream_def] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   ASM_MESON_TAC [is_proper_suffix_pstream_trans]);;

export_thm is_suffix_pstream_trans;;

let append_pstream_assoc = prove
  (`!x y z : A pstream.
      append_pstream (APPEND x y) z = append_pstream x (append_pstream y z)`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND; append_pstream_def]);;

export_thm append_pstream_assoc;;

let list_to_pstream_to_list = prove
  (`!l : A list. pstream_to_list (list_to_pstream l) = SOME l`,
   REWRITE_TAC [list_to_pstream_def] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [pstream_to_list_def; append_pstream_def];
    REWRITE_TAC [pstream_to_list_def; append_pstream_def] THEN
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm list_to_pstream_to_list;;

let pstream_to_list_append = prove
  (`!(l : A list) s.
      pstream_to_list (append_pstream l s) =
      case_option NONE (\ls. SOME (APPEND l ls)) (pstream_to_list s)`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [APPEND; append_pstream_def] THEN
    CONV_TAC (DEPTH_CONV ETA_CONV) THEN
    REWRITE_TAC [case_option_id];
    ALL_TAC] THEN
   GEN_TAC THEN
   REWRITE_TAC [APPEND; append_pstream_def; pstream_to_list_def] THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (ISPEC `pstream_to_list (s : A pstream)` option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm pstream_to_list_append;;

let is_suffix_pstream_length = prove
  (`!x y : A pstream.
      is_suffix_pstream x y ==> length_pstream x <= length_pstream y`,
   REWRITE_TAC [is_suffix_pstream_def; LE_LT] THEN
   REPEAT STRIP_TAC THENL
   [DISJ2_TAC THEN
    ASM_REWRITE_TAC [];
    DISJ1_TAC THEN
    MATCH_MP_TAC is_proper_suffix_pstream_length THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm is_suffix_pstream_length;;

let append_pstream_length = prove
  (`!(l : A list) s.
      length_pstream (append_pstream l s) = LENGTH l + length_pstream s`,
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
  (`!s : A pstream.
     case_option T (\l. LENGTH l = length_pstream s) (pstream_to_list s)`,
   MATCH_MP_TAC pstream_induct THEN
   CONJ_TAC THENL
   [REWRITE_TAC [pstream_to_list_def; case_option_def];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC
      [pstream_to_list_def; case_option_def; LENGTH; length_pstream_def];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [pstream_to_list_def] THEN
   MP_TAC (ISPEC `pstream_to_list (a1 : A pstream)` option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   REWRITE_TAC [LENGTH; length_pstream_def; SUC_INJ]);;

export_thm pstream_to_list_length;;

let pstream_to_list_map = prove
  (`!(f : A -> B) (s : A pstream).
      pstream_to_list (map_pstream f s) =
      map_option (MAP f) (pstream_to_list s)`,
   GEN_TAC THEN
   MATCH_MP_TAC pstream_induct THEN
   REWRITE_TAC [map_pstream_def; pstream_to_list_def; map_option_def; MAP] THEN
   X_GEN_TAC `a : A` THEN
   X_GEN_TAC `s' : A pstream` THEN
   DISCH_THEN SUBST1_TAC THEN
   MP_TAC (ISPEC `pstream_to_list (s' : A pstream)` option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def; MAP]);;

export_thm pstream_to_list_map;;

let length_pstream_src = prove
 (`(length_pstream (ErrorPstream : A pstream) = 0) /\
   (length_pstream (EofPstream : A pstream) = 0) /\
   (!(a : A) s. length_pstream (ConsPstream a s) = length_pstream s + 1)`,
  REWRITE_TAC [length_pstream_def; ADD1]);;

export_thm length_pstream_src;;

(* ------------------------------------------------------------------------- *)
(* Definition of stream parser combinators.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "parser-comb-def";;

let is_parser_def = new_definition
  `!(p : A -> A pstream -> (B # A pstream) option).
     is_parser p <=>
       !x xs.
         case_option
           T
           (\ (y,xs'). is_suffix_pstream xs' xs)
           (p x xs)`;;

export_thm is_parser_def;;

let parser_exists = prove
  (`?(p : A -> A pstream -> (B # A pstream) option). is_parser p`,
   EXISTS_TAC `\(x:A) (s:A pstream). (NONE : (B # A pstream) option)` THEN
   REWRITE_TAC [is_parser_def; case_option_def]);;

let (parser_abs_rep,parser_rep_abs) =
  let tybij =
    new_type_definition "parser" ("mk_parser","dest_parser") parser_exists in
  CONJ_PAIR tybij;;

export_thm parser_abs_rep;;
export_thm parser_rep_abs;;

let parser_tybij = CONJ parser_abs_rep parser_rep_abs;;

let (parse_error,parse_eof,parse_cons) =
  let def = new_recursive_definition pstream_recursion
    `(!p : (A,B) parser. parse p ErrorPstream = NONE) /\
     (!p : (A,B) parser. parse p EofPstream = NONE) /\
     (!p : (A,B) parser. !a s.
        parse p (ConsPstream a s) = dest_parser p a s)` in
  CONJ_TRIPLE def;;

export_thm parse_error;;
export_thm parse_eof;;
export_thm parse_cons;;

let parse_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ parse_error (CONJ parse_eof parse_cons));;

let parse_inverse_def = new_definition
  `!p e.
     parse_inverse p (e : B -> A list) <=>
     !x s. parse p (append_pstream (e x) s) = SOME (x,s)`;;

export_thm parse_inverse_def;;

let parse_strong_inverse_def = new_definition
  `!p e.
     parse_strong_inverse p (e : B -> A list) <=>
     parse_inverse p e /\
     !s x s'. parse p s = SOME (x,s') ==> s = append_pstream (e x) s'`;;

export_thm parse_strong_inverse_def;;

let parser_none_def = new_definition
  `!a s.
     parser_none (a : A) (s : A pstream) =
     (NONE : (B # A pstream) option)`;;

export_thm parser_none_def;;

let parse_none_def = new_definition
  `(parse_none : (A,B) parser) = mk_parser parser_none`;;

export_thm parse_none_def;;

let parser_any_def = new_definition
  `!a s. parser_any (a : A) (s : A pstream) = SOME (a,s)`;;

export_thm parser_any_def;;

let parse_any_def = new_definition
  `(parse_any : (A,A) parser) = mk_parser parser_any`;;

export_thm parse_any_def;;

let parser_map_partial_def = new_definition
  `!f p a s.
     parser_map_partial (f : B -> C option) (p : (A,B) parser) a s =
     case_option
       NONE
       (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
       (dest_parser p a s)`;;

export_thm parser_map_partial_def;;

let parse_map_partial_def = new_definition
  `!f p.
     parse_map_partial (f : B -> C option) (p : (A,B) parser) =
     mk_parser (parser_map_partial f p)`;;

export_thm parse_map_partial_def;;

let parse_map_def = new_definition
  `!f p.
     parse_map (f : B -> C) (p : (A,B) parser) =
     parse_map_partial (\b. SOME (f b)) p`;;

export_thm parse_map_def;;

let parser_pair_def = new_definition
  `!p1 p2 a s.
     parser_pair (p1 : (A,B) parser) (p2 : (A,C) parser) a s =
     case_option
       NONE
       (\ (b1,s').
          case_option
            NONE
            (\ (b2,s''). SOME ((b1,b2),s''))
            (parse p2 s'))
       (dest_parser p1 a s)`;;

export_thm parser_pair_def;;

let parse_pair_def = new_definition
  `!p1 p2.
     parse_pair (p1 : (A,B) parser) (p2 : (A,C) parser) =
     mk_parser (parser_pair p1 p2)`;;

export_thm parse_pair_def;;

let parse_option_def = new_definition
  `!f. parse_option (f : A -> B option) = parse_map_partial f parse_any`;;

export_thm parse_option_def;;

let parse_some_def = new_definition
  `!p.
     parse_some (p : A -> bool) =
     parse_option (\a. if p a then SOME a else NONE)`;;

export_thm parse_some_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of stream parser combinators.                                  *)
(* ------------------------------------------------------------------------- *)

logfile "parser-comb-thm";;

let dest_is_parser = prove
  (`!p : (A,B) parser. is_parser (dest_parser p)`,
   REWRITE_TAC [parser_tybij]);;

export_thm dest_is_parser;;

let is_parser_cases = prove
  (`!(p : A -> A pstream -> (B # A pstream) option) a s.
       is_parser p ==>
       (p a s = NONE) \/
       (?b s'. p a s = SOME (b,s') /\ is_suffix_pstream s' s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def] THEN
   DISCH_THEN (MP_TAC o SPECL [`a:A`;`s:A pstream`]) THEN
   MP_TAC
     (ISPEC `(p : A -> A pstream -> (B # A pstream) option) a s`
        option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `a' : B # A pstream` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   DISJ2_TAC THEN
   EXISTS_TAC `a'':B` THEN
   EXISTS_TAC `b:A pstream` THEN
   ASM_REWRITE_TAC []);;

export_thm is_parser_cases;;

let dest_parser_cases = prove
  (`!(p : (A,B) parser) a s.
       (dest_parser p a s = NONE) \/
       (?b s'. dest_parser p a s = SOME (b,s') /\ is_suffix_pstream s' s)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`dest_parser (p : (A,B) parser)`; `a:A`; `s:A pstream`]
             is_parser_cases) THEN
   REWRITE_TAC [dest_is_parser]);;

export_thm dest_parser_cases;;

let dest_parser_suffix_pstream = prove
  (`!(p : (A,B) parser) a s b s'.
       dest_parser p a s = SOME (b,s') ==> is_suffix_pstream s' s`,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`p : (A,B) parser`; `a:A`; `s:A pstream`]
             dest_parser_cases) THEN
   ASM_REWRITE_TAC [option_distinct; option_inj; PAIR_EQ] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm dest_parser_suffix_pstream;;

let parse_cases = prove
  (`!(p : (A,B) parser) s.
       (parse p s = NONE) \/
       (?b s'. parse p s = SOME (b,s') /\ is_proper_suffix_pstream s' s)`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def] THEN
   MP_TAC (SPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A pstream`]
             dest_parser_cases) THEN
   REWRITE_TAC [is_suffix_pstream_def] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   DISJ2_TAC THEN
   EXISTS_TAC `b : B` THEN
   EXISTS_TAC `s' : A pstream` THEN
   ASM_REWRITE_TAC [is_proper_suffix_pstream_def]);;

export_thm parse_cases;;

let is_parser_none = prove
  (`is_parser (parser_none : A -> A pstream -> (B # A pstream) option)`,
   REWRITE_TAC [is_parser_def; parser_none_def; case_option_def]);;

export_thm is_parser_none;;

let dest_parse_none = prove
  (`dest_parser (parse_none : (A,B) parser) = parser_none`,
   REWRITE_TAC
     [parse_none_def; GSYM (CONJUNCT2 parser_tybij); is_parser_none]);;

export_thm dest_parse_none;;

let parse_parse_none = prove
  (`!s. parse (parse_none : (A,B) parser) s = NONE`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_pstream_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_none; parser_none_def]);;

export_thm parse_parse_none;;

let is_parser_any = prove
  (`is_parser (parser_any : A -> A pstream -> (A # A pstream) option)`,
   REWRITE_TAC
     [is_parser_def; parser_any_def; case_option_def; is_suffix_pstream_refl]);;

export_thm is_parser_any;;

let dest_parse_any = prove
  (`dest_parser (parse_any : (A,A) parser) = parser_any`,
   REWRITE_TAC
     [parse_any_def; GSYM (CONJUNCT2 parser_tybij); is_parser_any]);;

export_thm dest_parse_any;;

let parse_parse_any_cons = prove
  (`!(x : A) s. parse parse_any (ConsPstream x s) = SOME (x,s)`,
    REPEAT GEN_TAC THEN
    ASM_REWRITE_TAC [parse_def; dest_parse_any; parser_any_def]);;

export_thm parse_parse_any_cons;;

let parse_parse_any = prove
  (`parse (parse_any : (A,A) parser) =
    case_pstream NONE NONE (\a s. SOME (a,s))`,
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `x : A pstream` pstream_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC
      [parse_error; parse_eof; parse_parse_any_cons; case_pstream_def]);;

export_thm parse_parse_any;;

let parse_any_inverse = prove
  (`parse_inverse (parse_any : (A,A) parser) (\a. CONS a [])`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_any; append_pstream_def; case_pstream_def;
      case_option_def]);;

export_thm parse_any_inverse;;

let parse_any_strong_inverse = prove
  (`parse_strong_inverse (parse_any : (A,A) parser) (\a. CONS a [])`,
   REWRITE_TAC [parse_strong_inverse_def; parse_any_inverse] THEN
   ASM_REWRITE_TAC [parse_parse_any; append_pstream_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [case_pstream_def; option_distinct; pstream_inj; option_inj; PAIR_EQ]);;

export_thm parse_any_strong_inverse;;

let is_parser_map_partial = prove
  (`!f p.
      is_parser (parser_map_partial (f : B -> C option) (p : (A,B) parser))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def; parser_map_partial_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPECL [`p : (A,B) parser`;
                   `x : A`; `xs : A pstream`] dest_parser_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPECL [`(f : B -> C option) b`] option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm is_parser_map_partial;;

let dest_parse_map_partial = prove
  (`!f p.
      dest_parser (parse_map_partial (f : B -> C option) (p : (A,B) parser)) =
      parser_map_partial f p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [parse_map_partial_def; GSYM (CONJUNCT2 parser_tybij);
      is_parser_map_partial]);;

export_thm dest_parse_map_partial;;

let parse_parse_map_partial = prove
  (`!f p s.
      parse (parse_map_partial (f : B -> C option) (p : (A,B) parser)) s =
      case_option
        NONE
        (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
        (parse p s)`,
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_map_partial; parser_map_partial_def]);;

export_thm parse_parse_map_partial;;

let parse_map_partial_inverse = prove
  (`!f p g e.
      parse_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = SOME b) ==>
      parse_inverse (parse_map_partial (f : B -> C option) p) (\c. e (g c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_map_partial; append_pstream_def; case_pstream_def;
      case_option_def]);;

export_thm parse_map_partial_inverse;;

let parse_map_partial_strong_inverse = prove
  (`!(f : B -> C option) p g e.
      parse_strong_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = SOME b) /\
      (!b1 b2 c. f b1 = SOME c /\ f b2 = SOME c ==> b1 = b2) ==>
      parse_strong_inverse (parse_map_partial f p) (\c. e (g c))`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_map_partial_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_map_partial; append_pstream_def] THEN
    MP_TAC (ISPECL [`p : (A,B) parser`; `s : A pstream`] parse_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
    MP_TAC (ISPEC `(f : B -> C option) b` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x : C` THEN
    ASM_REWRITE_TAC []]);;

export_thm parse_map_partial_strong_inverse;;

let dest_parse_map = prove
  (`!f p a s.
      dest_parser (parse_map (f : B -> C) (p : (A,B) parser)) a s =
      case_option
        NONE
        (\ (b,s'). SOME (f b, s'))
        (dest_parser p a s)`,
   REWRITE_TAC
     [parse_map_def; dest_parse_map_partial; parser_map_partial_def;
      case_option_def]);;

export_thm dest_parse_map;;

let parse_parse_map = prove
  (`!f p s.
      parse (parse_map (f : B -> C) (p : (A,B) parser)) s =
      case_option
        NONE
        (\ (b,s'). SOME (f b, s'))
        (parse p s)`,
   REWRITE_TAC [parse_map_def; parse_parse_map_partial; case_option_def]);;

export_thm parse_parse_map;;

let parse_map_inverse = prove
  (`!f p g e.
      parse_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = b) ==>
      parse_inverse (parse_map (f : B -> C) p) (\c. e (g c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_map; append_pstream_def; case_pstream_def;
      case_option_def]);;

export_thm parse_map_inverse;;

let parse_map_strong_inverse = prove
  (`!(f : B -> C) p g e.
      parse_strong_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = b) /\
      (!b1 b2 c. f b1 = c /\ f b2 = c ==> b1 = b2) ==>
      parse_strong_inverse (parse_map f p) (\c. e (g c))`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_map_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_map; append_pstream_def] THEN
    MP_TAC (ISPECL [`p : (A,B) parser`; `s : A pstream`] parse_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `x : C` THEN
    ASM_REWRITE_TAC []]);;

export_thm parse_map_strong_inverse;;

let is_parser_pair = prove
  (`!p1 p2. is_parser (parser_pair (p1 : (A,B) parser) (p2 : (A,C) parser))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def; parser_pair_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`p1 : (A,B) parser`; `x : A`; `xs : A pstream`]
             dest_parser_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPECL [`p2 : (A,C) parser`; `s' : A pstream`]
             parse_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   ASM_MESON_TAC [is_suffix_pstream_trans; is_suffix_pstream_proper]);;

export_thm is_parser_pair;;

let dest_parse_pair = prove
  (`!p1 p2.
      dest_parser (parse_pair (p1 : (A,B) parser) (p2 : (A,C) parser)) =
      parser_pair p1 p2`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [parse_pair_def; GSYM (CONJUNCT2 parser_tybij); is_parser_pair]);;

export_thm dest_parse_pair;;

let parse_parse_pair = prove
  (`!p1 p2 s.
      parse (parse_pair p1 p2 : (A, B # C) parser) s =
      case_option
        NONE
        (\ (b,s').
           case_option
             NONE
             (\ (c,s''). SOME ((b,c),s''))
             (parse p2 s'))
        (parse p1 s)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_pair; parser_pair_def]);;

export_thm parse_parse_pair;;

let parse_pair_inverse = prove
  (`!p1 p2 e1 e2.
      parse_inverse p1 e1 /\ parse_inverse p2 e2 ==>
      parse_inverse
        (parse_pair p1 p2 : (A, B # C) parser)
        (\ (b,c). APPEND (e1 b) (e2 c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [parse_parse_pair] THEN
   MP_TAC (ISPEC `x : B # C` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [append_pstream_assoc; case_option_def]);;

export_thm parse_pair_inverse;;

let parse_pair_strong_inverse = prove
  (`!p1 p2 e1 e2.
      parse_strong_inverse p1 e1 /\ parse_strong_inverse p2 e2 ==>
      parse_strong_inverse
        (parse_pair p1 p2 : (A, B # C) parser)
        (\ (b,c). APPEND (e1 b) (e2 c))`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_pair_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `x : B # C` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_pair; append_pstream_assoc] THEN
    MP_TAC (ISPEC `parse (p1 : (A,B) parser) s` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `a' : B # A pstream` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC (ISPEC `parse (p2 : (A,C) parser) b'` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `a''' : C # A pstream` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [option_inj; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `parse (p2 : (A,C) parser) b' = SOME (a'''',b'')` THEN
    UNDISCH_TAC `parse (p1 : (A,B) parser) s = SOME (a'',b')` THEN
    ASM_REWRITE_TAC [] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm parse_pair_strong_inverse;;

let dest_parse_option = prove
  (`!f a s.
      dest_parser (parse_option (f : A -> B option)) a s =
      case_option NONE (\b. SOME (b,s)) (f a)`,
   REWRITE_TAC
     [parse_option_def; dest_parse_map_partial; parser_map_partial_def;
      case_option_def; dest_parse_any; parser_any_def]);;

export_thm dest_parse_option;;

let parse_parse_option = prove
  (`!f.
      parse (parse_option (f : A -> B option)) =
      case_pstream
        NONE
        NONE
        (\a s. case_option NONE (\b. SOME (b,s)) (f a))`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC
     [parse_option_def; parse_parse_map_partial; parse_parse_any] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPEC `x : A pstream` pstream_cases) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [case_pstream_def; case_option_def]);;

export_thm parse_parse_option;;

let parse_option_inverse = prove
  (`!f e.
      (!b. f (e b) = SOME b) ==>
      parse_inverse (parse_option (f : A -> B option)) (\b. CONS (e b) [])`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_option; append_pstream_def; case_pstream_def;
      case_option_def]);;

export_thm parse_option_inverse;;

let parse_option_strong_inverse = prove
  (`!f e.
      (!b. f (e b) = SOME b) /\
      (!a1 a2 b. f a1 = SOME b /\ f a2 = SOME b ==> a1 = a2) ==>
      parse_strong_inverse
        (parse_option (f : A -> B option)) (\b. CONS (e b) [])`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_option_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_option; append_pstream_def] THEN
    MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_pstream_def; option_distinct; pstream_inj] THEN
    MP_TAC (ISPEC `(f : A -> B option) a0` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct; option_inj; PAIR_EQ] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `a : B` THEN
    ASM_REWRITE_TAC []]);;

export_thm parse_option_strong_inverse;;

let dest_parse_some = prove
  (`!p a s.
      dest_parser (parse_some (p : A -> bool)) a s =
      if p a then SOME (a,s) else NONE`,
   REWRITE_TAC [parse_some_def; dest_parse_option] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `(p : A -> bool) a` BOOL_CASES_AX) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def; COND_CLAUSES]);;

export_thm dest_parse_some;;

let parse_parse_some = prove
  (`!p.
      parse (parse_some (p : A -> bool)) =
      case_pstream
        NONE
        NONE
        (\a s. if p a then SOME (a,s) else NONE)`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `x : A pstream` pstream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def; case_pstream_def; dest_parse_some]);;

export_thm parse_parse_some;;

let parse_src = prove
 (`(!p : (A,B) parser. parse p ErrorPstream = NONE) /\
   (!p : (A,B) parser. parse p EofPstream = NONE) /\
   (!p : (A,B) parser. !a s.
      parse p (ConsPstream a s) = dest_parser p a s)`,
  REWRITE_TAC [parse_def]);;

export_thm parse_src;;

(* ------------------------------------------------------------------------- *)
(* Definition of the whole stream parser.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "parser-all-def";;

let parse_pstream_exists = prove
  (`!(p : (A,B) parser). ?f.
      (f ErrorPstream = ErrorPstream) /\
      (f EofPstream = EofPstream) /\
      (!a s.
         f (ConsPstream a s) =
           case_option
             ErrorPstream
             (\ (b,s'). ConsPstream b (f s'))
             (dest_parser p a s))`,
   let exists0 = prove
     (`!(p : (A,B) parser). ?f.
         !s.
           f s =
           (\f'.
              case_pstream
                ErrorPstream
                EofPstream
                (\a s'.
                   case_option
                     ErrorPstream
                     (\ (b,s''). ConsPstream b (f' s''))
                     (dest_parser p a s'))) f s`,
      GEN_TAC THEN
      MATCH_MP_TAC is_proper_suffix_pstream_recursion THEN
      SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPEC `s : A pstream` pstream_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_pstream_def] THEN
      MP_TAC (ISPEC `dest_parser (p : (A,B) parser) a0 a1` option_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      POP_ASSUM MP_TAC THEN
      MP_TAC (ISPEC `a : B # A pstream` PAIR_SURJECTIVE) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [pstream_inj] THEN
      STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [is_proper_suffix_pstream_def] THEN
      REWRITE_TAC [GSYM is_suffix_pstream_def] THEN
      MATCH_MP_TAC
        (ISPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A pstream`;
                 `a' : B`; `b : A pstream`] dest_parser_suffix_pstream) THEN
      ASM_REWRITE_TAC []) in
   GEN_TAC THEN
   MP_TAC (SPEC `p : (A,B) parser` exists0) THEN
   STRIP_TAC THEN
   EXISTS_TAC `f : A pstream -> B pstream` THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (fun th -> CONV_TAC (LAND_CONV (REWR_CONV th))) THEN
   REWRITE_TAC [case_pstream_def]);;

let (parse_pstream_error,
     parse_pstream_eof,
     parse_pstream_cons) =
  let def =
    new_specification ["parse_pstream"]
    (REWRITE_RULE [SKOLEM_THM] parse_pstream_exists) in
  CONJ_TRIPLE (REWRITE_RULE [FORALL_AND_THM] def);;

export_thm parse_pstream_error;;
export_thm parse_pstream_eof;;
export_thm parse_pstream_cons;;

let parse_pstream_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ parse_pstream_error (CONJ parse_pstream_eof parse_pstream_cons));;

(* ------------------------------------------------------------------------- *)
(* Properties of the whole stream parser.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "parser-all-thm";;

let parse_pstream_map = prove
  (`!(f : B -> C) (p : (A,B) parser).
      parse_pstream (parse_map f p) = map_pstream f o parse_pstream p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [FUN_EQ_THM; o_THM] THEN
   MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
   X_GEN_TAC `s : A pstream` THEN
   STRIP_TAC THEN
   MP_TAC (SPEC `s : A pstream` pstream_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST_VAR_TAC
       (DISJ_CASES_THEN2 SUBST_VAR_TAC
         (X_CHOOSE_THEN `a : A`
           (X_CHOOSE_THEN `s' : A pstream` SUBST_VAR_TAC)))) THENL
   [REWRITE_TAC [parse_pstream_def; map_pstream_def];
    REWRITE_TAC [parse_pstream_def; map_pstream_def];
    ALL_TAC] THEN
   REWRITE_TAC [parse_pstream_def; dest_parse_map] THEN
   MP_TAC (SPECL [`p : (A,B) parser`; `a : A`; `s' : A pstream`]
           dest_parser_cases) THEN
   DISCH_THEN
     (DISJ_CASES_THEN2 SUBST1_TAC
       (X_CHOOSE_THEN `b : B`
         (X_CHOOSE_THEN `s'' : A pstream` STRIP_ASSUME_TAC))) THENL
   [REWRITE_TAC [case_option_def; map_pstream_def];
    ALL_TAC] THEN
   FIRST_X_ASSUM SUBST1_TAC THEN
   REWRITE_TAC [case_option_def; map_pstream_def] THEN
   AP_TERM_TAC THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC
     [is_proper_suffix_pstream_def; GSYM is_suffix_pstream_def]);;

export_thm parse_pstream_map;;

let parse_pstream_append = prove
  (`!p (e : A -> B list) x s.
      parse_inverse p e ==>
      parse_pstream p (append_pstream (e x) s) =
      ConsPstream x (parse_pstream p s)`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o SPECL [`x : A`; `s : B pstream`]) THEN
   MP_TAC (ISPEC `(e : A -> B list) x` list_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [append_pstream_def] THEN
    MP_TAC (ISPECL [`p : (B,A) parser`; `s : B pstream`] parse_cases) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [option_distinct];
     ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
     STRIP_TAC THEN
     PAT_ASSUM `is_proper_suffix_pstream (X : A pstream) Y` THEN
     ASM_REWRITE_TAC [is_proper_suffix_pstream_refl]];
    ASM_REWRITE_TAC [parse_def; parse_pstream_def; append_pstream_def] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm parse_pstream_append;;

let parse_pstream_inverse = prove
  (`!p (e : A -> B list) l.
      parse_inverse p e ==>
      parse_pstream p (list_to_pstream (concat (MAP e l))) =
      list_to_pstream l`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`l : A list`, `l : A list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [MAP; concat_def; parse_pstream_def; list_to_pstream_def;
       append_pstream_def];
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC
     [MAP; concat_def; parse_pstream_def; list_to_pstream_def;
      append_pstream_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
   REWRITE_TAC [append_pstream_assoc] THEN
   MATCH_MP_TAC parse_pstream_append THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm parse_pstream_inverse;;

let parse_pstream_strong_inverse = prove
  (`!p (e : A -> B list) s.
      parse_strong_inverse p e ==>
      case_option T (\l. pstream_to_list s = SOME (concat (MAP e l)))
        (pstream_to_list (parse_pstream p s))`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`s : B pstream`, `s : B pstream`) THEN
   MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `s : B pstream` pstream_cases) THEN
   STRIP_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [pstream_to_list_def; parse_pstream_def; case_option_def];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC
      [pstream_to_list_def; parse_pstream_def; case_option_def; MAP;
       concat_def];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [parse_pstream_def] THEN
   MP_TAC (ISPECL [`p : (B,A) parser`; `a0 : B`; `a1 : B pstream`]
           dest_parser_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def; pstream_to_list_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   CONV_TAC (RAND_CONV (REWRITE_CONV [pstream_to_list_def])) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `s' : B pstream`) THEN
   COND_TAC THENL
   [PAT_ASSUM `is_suffix_pstream (X : B pstream) Y` THEN
    REWRITE_TAC [is_suffix_pstream_def; is_proper_suffix_pstream_def];
    ALL_TAC] THEN
   MP_TAC (ISPEC `pstream_to_list (parse_pstream (p : (B,A) parser) s')`
           option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   PAT_ASSUM `parse_strong_inverse (p : (B,A) parser) e` THEN
   REWRITE_TAC [parse_strong_inverse_def] THEN
   DISCH_THEN (MP_TAC o SPECL [`ConsPstream (a0 : B) a1`; `b : A`;
                               `s' : B pstream`] o CONJUNCT2) THEN
   COND_TAC THENL
   [ASM_REWRITE_TAC [parse_def];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [pstream_to_list_append] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [case_option_def; option_inj; MAP; concat_def]);;

export_thm parse_pstream_strong_inverse;;

let parse_pstream_length = prove
  (`!(p : (A,B) parser) s.
      length_pstream (parse_pstream p s) <= length_pstream s`,
   GEN_TAC THEN
   MATCH_MP_TAC is_proper_suffix_pstream_induct THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `s : A pstream` pstream_cases) THEN
   STRIP_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [length_pstream_def; parse_pstream_def; LE_REFL];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [length_pstream_def; parse_pstream_def; LE_REFL];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [parse_pstream_def] THEN
   MP_TAC (ISPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A pstream`]
           dest_parser_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def; length_pstream_def; LE_0];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   REWRITE_TAC [length_pstream_def; LE_SUC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `length_pstream (s' : A pstream)` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    PAT_ASSUM `is_suffix_pstream (X : A pstream) Y` THEN
    REWRITE_TAC [is_suffix_pstream_def; is_proper_suffix_pstream_def];
    MATCH_MP_TAC is_suffix_pstream_length THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm parse_pstream_length;;

let parse_pstream_src = prove
 (`(!p : (A,B) parser. parse_pstream p ErrorPstream = ErrorPstream) /\
   (!p : (A,B) parser. parse_pstream p EofPstream = EofPstream) /\
   (!p : (A,B) parser. !a s.
      parse_pstream p (ConsPstream a s) =
      case_option
        ErrorPstream
        (\(b,s'). ConsPstream b (parse_pstream p s'))
        (dest_parser p a s))`,
  REWRITE_TAC [parse_pstream_def]);;

export_thm parse_pstream_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for stream parsers.                                        *)
(* ------------------------------------------------------------------------- *)

logfile "parser-haskell-src";;

export_thm case_pstream_def;;  (* Haskell *)
export_thm map_pstream_def;;  (* Haskell *)
export_thm length_pstream_src;;  (* Haskell *)
export_thm pstream_to_list_def;;  (* Haskell *)
export_thm append_pstream_def;;  (* Haskell *)
export_thm list_to_pstream_def;;  (* Haskell *)
export_thm parser_abs_rep;;  (* Haskell *)
export_thm parse_src;;  (* Haskell *)
export_thm parser_none_def;;  (* Haskell *)
export_thm parse_none_def;;  (* Haskell *)
export_thm parser_any_def;;  (* Haskell *)
export_thm parse_any_def;;  (* Haskell *)
export_thm parser_map_partial_def;;  (* Haskell *)
export_thm parse_map_partial_def;;  (* Haskell *)
export_thm parse_map_def;;  (* Haskell *)
export_thm parser_pair_def;;  (* Haskell *)
export_thm parse_pair_def;;  (* Haskell *)
export_thm parse_option_def;;  (* Haskell *)
export_thm parse_some_def;;  (* Haskell *)
export_thm parse_pstream_src;;  (* Haskell *)

logfile_end ();;

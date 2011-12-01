(* ------------------------------------------------------------------------- *)
(* Simple stream parsers.                                                    *)
(* ------------------------------------------------------------------------- *)

logfile "parser-stream-def";;

let stream_induct,stream_recursion = define_type
    "stream = Error
            | Eof
            | Stream A stream";;

export_thm stream_induct;;
export_thm stream_recursion;;

let (case_stream_error,case_stream_eof,case_stream_stream) =
  let def = new_recursive_definition stream_recursion
    `(!e b f. case_stream e b f Error = (e:B)) /\
     (!e b f. case_stream e b f Eof = b) /\
     (!e b f a s. case_stream e b f (Stream a s) = f (a:A) s)` in
  CONJ_TRIPLE def;;

export_thm case_stream_error;;
export_thm case_stream_eof;;
export_thm case_stream_stream;;

let case_stream_def =
  CONJ case_stream_error (CONJ case_stream_eof case_stream_stream);;

let (length_stream_error,length_stream_eof,length_stream_stream) =
  let def = new_recursive_definition stream_recursion
    `(length_stream Error = 0) /\
     (length_stream Eof = 0) /\
     (!(a:A) s. length_stream (Stream a s) = SUC (length_stream s))` in
  CONJ_TRIPLE def;;

export_thm length_stream_error;;
export_thm length_stream_eof;;
export_thm length_stream_stream;;

let length_stream_def =
  CONJ length_stream_error (CONJ length_stream_eof length_stream_stream);;

let (is_proper_suffix_stream_error,
     is_proper_suffix_stream_eof,
     is_proper_suffix_stream_stream) =
  let def = new_recursive_definition stream_recursion
  `(!s. is_proper_suffix_stream s Error = F) /\
   (!s. is_proper_suffix_stream s Eof = F) /\
   (!s a s'. is_proper_suffix_stream s (Stream (a:A) s') =
      ((s = s') \/ is_proper_suffix_stream s s'))` in
   CONJ_TRIPLE (REWRITE_RULE [] def);;

export_thm is_proper_suffix_stream_error;;
export_thm is_proper_suffix_stream_eof;;
export_thm is_proper_suffix_stream_stream;;

let is_proper_suffix_stream_def =
  CONJ is_proper_suffix_stream_error
    (CONJ is_proper_suffix_stream_eof is_proper_suffix_stream_stream);;

let is_suffix_stream_def = new_definition
  `!s s'.
     is_suffix_stream s s' =
     (((s : A stream) = s') \/ is_proper_suffix_stream s s')`;;

export_thm is_suffix_stream_def;;

let (stream_to_list_error,
     stream_to_list_eof,
     stream_to_list_stream) =
  let def = new_recursive_definition stream_recursion
    `(stream_to_list Error = NONE) /\
     (stream_to_list Eof = SOME []) /\
     (!a s. stream_to_list (Stream a s) =
        case_option
          NONE
          (\l. SOME (CONS (a:A) l))
          (stream_to_list s))` in
  CONJ_TRIPLE def;;

export_thm stream_to_list_error;;
export_thm stream_to_list_eof;;
export_thm stream_to_list_stream;;

let stream_to_list_def =
  CONJ stream_to_list_error
    (CONJ stream_to_list_eof stream_to_list_stream);;

let (append_stream_nil,append_stream_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!s. append_stream [] s = s) /\
     (!h t s. append_stream (CONS h t) s = Stream (h:A) (append_stream t s))` in
  CONJ_PAIR def;;

export_thm append_stream_nil;;
export_thm append_stream_cons;;

let append_stream_def = CONJ append_stream_nil append_stream_cons;;

let list_to_stream_def = new_definition
  `!(l : A list). list_to_stream l = append_stream l Eof`;;

export_thm list_to_stream_def;;

logfile "parser-stream-thm";;

let stream_cases = prove_cases_thm stream_induct;;

export_thm stream_cases;;

let (stream_distinct_error_eof,
     stream_distinct_error_stream,
     stream_distinct_eof_stream) =
    CONJ_TRIPLE (distinctness "stream");;

export_thm stream_distinct_error_eof;;
export_thm stream_distinct_error_stream;;
export_thm stream_distinct_eof_stream;;

let stream_distinct =
    CONJ stream_distinct_error_eof
      (CONJ stream_distinct_error_stream stream_distinct_eof_stream);;

let stream_inj = injectivity "stream";;

export_thm stream_inj;;

let is_proper_suffix_stream_trans = prove
  (`!x y z : A stream.
      is_proper_suffix_stream x y /\ is_proper_suffix_stream y z ==>
      is_proper_suffix_stream x z`,
   GEN_TAC THEN
   GEN_TAC THEN
   MATCH_MP_TAC stream_induct THEN
   ASM_REWRITE_TAC [is_proper_suffix_stream_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_MESON_TAC []);;

export_thm is_proper_suffix_stream_trans;;

let is_proper_suffix_stream_length = prove
  (`!x y : A stream.
      is_proper_suffix_stream x y ==> length_stream x < length_stream y`,
   GEN_TAC THEN
   MATCH_MP_TAC stream_induct THEN
   ASM_REWRITE_TAC
     [is_proper_suffix_stream_def; length_stream_def; LT_SUC_LE] THEN
   REPEAT STRIP_TAC THEN
   ASM_MESON_TAC [LE_REFL; LT_IMP_LE]);;

export_thm is_proper_suffix_stream_length;;

let is_proper_suffix_stream_wf = prove
  (`WF (is_proper_suffix_stream : A stream -> A stream -> bool)`,
   MATCH_MP_TAC
     (ISPECL [`is_proper_suffix_stream : A stream -> A stream -> bool`;
              `MEASURE (length_stream : A stream -> num)`] WF_SUBSET) THEN
   REWRITE_TAC [WF_MEASURE] THEN
   REWRITE_TAC [MEASURE; is_proper_suffix_stream_length]);;

export_thm is_proper_suffix_stream_wf;;

let is_proper_suffix_stream_refl = prove
  (`!x : A stream. ~is_proper_suffix_stream x x`,
   GEN_TAC THEN
   MATCH_MP_TAC WF_REFL THEN
   ACCEPT_TAC is_proper_suffix_stream_wf);;

export_thm is_proper_suffix_stream_refl;;

let is_proper_suffix_stream_induct = prove
  (`!(p : A stream -> bool).
       (!x. (!y. is_proper_suffix_stream y x ==> p y) ==> p x) ==> !x. p x`,
   REWRITE_TAC [GSYM WF_IND; is_proper_suffix_stream_wf]);;

export_thm is_proper_suffix_stream_induct;;

let is_proper_suffix_stream_recursion = prove
  (`!(h : (A stream -> B) -> A stream -> B).
       (!f g s.
          (!s'. is_proper_suffix_stream s' s ==> (f s' = g s')) ==>
          (h f s = h g s)) ==>
       ?f. !s. f s = h f s`,
   MATCH_MP_TAC WF_REC THEN
   REWRITE_TAC [is_proper_suffix_stream_wf]);;

export_thm is_proper_suffix_stream_recursion;;

let is_suffix_stream_proper = prove
  (`!x y : A stream. is_proper_suffix_stream x y ==> is_suffix_stream x y`,
   SIMP_TAC [is_suffix_stream_def]);;

export_thm is_suffix_stream_proper;;

let is_suffix_stream_refl = prove
  (`!x : A stream. is_suffix_stream x x`,
   SIMP_TAC [is_suffix_stream_def]);;

export_thm is_suffix_stream_refl;;

let is_suffix_stream_trans = prove
  (`!x y z : A stream.
      is_suffix_stream x y /\ is_suffix_stream y z ==>
      is_suffix_stream x z`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_suffix_stream_def] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   ASM_MESON_TAC [is_proper_suffix_stream_trans]);;

export_thm is_suffix_stream_trans;;

let append_stream_assoc = prove
  (`!x y z : A stream.
      append_stream (APPEND x y) z = append_stream x (append_stream y z)`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [APPEND; append_stream_def]);;

export_thm append_stream_assoc;;

let list_to_stream_to_list = prove
  (`!l : A list. stream_to_list (list_to_stream l) = SOME l`,
   REWRITE_TAC [list_to_stream_def] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [stream_to_list_def; append_stream_def];
    REWRITE_TAC [stream_to_list_def; append_stream_def] THEN
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm list_to_stream_to_list;;

let stream_to_list_append = prove
  (`!(l : A list) s.
      stream_to_list (append_stream l s) =
      case_option NONE (\ls. SOME (APPEND l ls)) (stream_to_list s)`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [APPEND; append_stream_def] THEN
    CONV_TAC (DEPTH_CONV ETA_CONV) THEN
    REWRITE_TAC [case_option_id];
    ALL_TAC] THEN
   GEN_TAC THEN
   REWRITE_TAC [APPEND; append_stream_def; stream_to_list_def] THEN
   POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
   MP_TAC (ISPEC `stream_to_list (s : A stream)` option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm stream_to_list_append;;

let is_suffix_stream_length = prove
  (`!x y : A stream.
      is_suffix_stream x y ==> length_stream x <= length_stream y`,
   REWRITE_TAC [is_suffix_stream_def; LE_LT] THEN
   REPEAT STRIP_TAC THENL
   [DISJ2_TAC THEN
    ASM_REWRITE_TAC [];
    DISJ1_TAC THEN
    MATCH_MP_TAC is_proper_suffix_stream_length THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm is_suffix_stream_length;;

let append_stream_length = prove
  (`!(l : A list) s.
      length_stream (append_stream l s) = LENGTH l + length_stream s`,
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [length_stream_def; append_stream_def; LENGTH; ADD];
    ASM_REWRITE_TAC [length_stream_def; append_stream_def; LENGTH; ADD]]);;

export_thm append_stream_length;;

let list_to_stream_length = prove
  (`!l : A list. length_stream (list_to_stream l) = LENGTH l`,
   REWRITE_TAC
     [list_to_stream_def; append_stream_length; length_stream_def; ADD_0]);;

export_thm list_to_stream_length;;

let stream_to_list_length = prove
  (`!s : A stream.
     case_option T (\l. LENGTH l = length_stream s) (stream_to_list s)`,
   MATCH_MP_TAC stream_induct THEN
   CONJ_TAC THENL
   [REWRITE_TAC [stream_to_list_def; case_option_def];
    ALL_TAC] THEN
   CONJ_TAC THENL
   [REWRITE_TAC
      [stream_to_list_def; case_option_def; LENGTH; length_stream_def];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [stream_to_list_def] THEN
   MP_TAC (ISPEC `stream_to_list (a1 : A stream)` option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   REWRITE_TAC [LENGTH; length_stream_def; SUC_INJ]);;

export_thm stream_to_list_length;;

logfile "parser-comb-def";;

let is_parser_def = new_definition
  `!p.
     is_parser (p : A -> A stream -> (B # A stream) option) =
       !x xs.
         case_option
           T
           (\ (y,xs'). is_suffix_stream xs' xs)
           (p x xs)`;;

export_thm is_parser_def;;

let parser_exists = prove
  (`?(p : A -> A stream -> (B # A stream) option). is_parser p`,
   EXISTS_TAC `\(x:A) (s:A stream). (NONE : (B # A stream) option)` THEN
   REWRITE_TAC [is_parser_def; case_option_def]);;

let (parser_abs_rep,parser_rep_abs) =
  let tybij =
    new_type_definition "parser" ("mk_parser","dest_parser") parser_exists in
  CONJ_PAIR tybij;;

export_thm parser_abs_rep;;
export_thm parser_rep_abs;;

let parser_tybij = CONJ parser_abs_rep parser_rep_abs;;

let (parse_error,parse_eof,parse_stream) =
  let def = new_recursive_definition stream_recursion
    `(!p : (A,B) parser. parse p Error = NONE) /\
     (!p : (A,B) parser. parse p Eof = NONE) /\
     (!p : (A,B) parser. !a s. parse p (Stream a s) = dest_parser p a s)` in
  CONJ_TRIPLE def;;

export_thm parse_error;;
export_thm parse_eof;;
export_thm parse_stream;;

let parse_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ parse_error (CONJ parse_eof parse_stream));;

let parse_inverse_def = new_definition
  `!p e.
     parse_inverse p (e : B -> A list) <=>
     !x s. parse p (append_stream (e x) s) = SOME (x,s)`;;

export_thm parse_inverse_def;;

let parse_strong_inverse_def = new_definition
  `!p e.
     parse_strong_inverse p (e : B -> A list) <=>
     parse_inverse p e /\
     !s x s'. parse p s = SOME (x,s') ==> s = append_stream (e x) s'`;;

export_thm parse_strong_inverse_def;;

let parser_none_def = new_definition
  `!a s. parser_none (a : A) (s : A stream) = (NONE : (B # A stream) option)`;;

export_thm parser_none_def;;

let parse_none_def = new_definition
  `(parse_none : (A,B) parser) = mk_parser parser_none`;;

export_thm parse_none_def;;

let parser_all_def = new_definition
  `!a s. parser_all (a : A) (s : A stream) = SOME (a,s)`;;

export_thm parser_all_def;;

let parse_all_def = new_definition
  `(parse_all : (A,A) parser) = mk_parser parser_all`;;

export_thm parse_all_def;;

let parser_partial_map_def = new_definition
  `!f p a s.
     parser_partial_map (f : B -> C option) (p : (A,B) parser) a s =
     case_option
       NONE
       (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
       (dest_parser p a s)`;;

export_thm parser_partial_map_def;;

let parse_partial_map_def = new_definition
  `!f p.
     parse_partial_map (f : B -> C option) (p : (A,B) parser) =
     mk_parser (parser_partial_map f p)`;;

export_thm parse_partial_map_def;;

let parse_map_def = new_definition
  `!f p.
     parse_map (f : B -> C) (p : (A,B) parser) =
     parse_partial_map (\b. SOME (f b)) p`;;

export_thm parse_map_def;;

let parser_pair_def = new_definition
  `!pb pc a s.
     parser_pair (pb : (A,B) parser) (pc : (A,C) parser) a s =
     case_option
       NONE
       (\ (b,s').
          case_option
            NONE
            (\ (c,s''). SOME ((b,c),s''))
            (parse pc s'))
       (dest_parser pb a s)`;;

export_thm parser_pair_def;;

let parse_pair_def = new_definition
  `!pb pc.
     parse_pair (pb : (A,B) parser) (pc : (A,C) parser) =
     mk_parser (parser_pair pb pc)`;;

export_thm parse_pair_def;;

let parse_option_def = new_definition
  `!f. parse_option (f : A -> B option) = parse_partial_map f parse_all`;;

export_thm parse_option_def;;

let parse_some_def = new_definition
  `!p.
     parse_some (p : A -> bool) =
     parse_option (\a. if p a then SOME a else NONE)`;;

export_thm parse_some_def;;

logfile "parser-comb-thm";;

let dest_is_parser = prove
  (`!p : (A,B) parser. is_parser (dest_parser p)`,
   REWRITE_TAC [parser_tybij]);;

export_thm dest_is_parser;;

let is_parser_cases = prove
  (`!(p : A -> A stream -> (B # A stream) option) a s.
       is_parser p ==>
       (p a s = NONE) \/
       (?b s'. p a s = SOME (b,s') /\ is_suffix_stream s' s)`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def] THEN
   DISCH_THEN (MP_TAC o SPECL [`a:A`;`s:A stream`]) THEN
   MP_TAC
     (ISPEC `(p : A -> A stream -> (B # A stream) option) a s`
        option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPEC `a' : B # A stream` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   STRIP_TAC THEN
   DISJ2_TAC THEN
   EXISTS_TAC `x:B` THEN
   EXISTS_TAC `y:A stream` THEN
   ASM_REWRITE_TAC []);;

export_thm is_parser_cases;;

let dest_parser_cases = prove
  (`!(p : (A,B) parser) a s.
       (dest_parser p a s = NONE) \/
       (?b s'. dest_parser p a s = SOME (b,s') /\ is_suffix_stream s' s)`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`dest_parser (p : (A,B) parser)`; `a:A`; `s:A stream`]
             is_parser_cases) THEN
   REWRITE_TAC [dest_is_parser]);;

export_thm dest_parser_cases;;

let dest_parser_suffix_stream = prove
  (`!(p : (A,B) parser) a s b s'.
       dest_parser p a s = SOME (b,s') ==> is_suffix_stream s' s`,
   REPEAT GEN_TAC THEN
   STRIP_TAC THEN
   MP_TAC (SPECL [`p : (A,B) parser`; `a:A`; `s:A stream`]
             dest_parser_cases) THEN
   ASM_REWRITE_TAC [option_distinct; option_inj; PAIR_EQ] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC []);;

export_thm dest_parser_suffix_stream;;

let parse_cases = prove
  (`!(p : (A,B) parser) s.
       (parse p s = NONE) \/
       (?b s'. parse p s = SOME (b,s') /\ is_proper_suffix_stream s' s)`,
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `s : A stream` stream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def] THEN
   MP_TAC (SPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A stream`]
             dest_parser_cases) THEN
   REWRITE_TAC [is_suffix_stream_def] THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   DISJ2_TAC THEN
   EXISTS_TAC `b : B` THEN
   EXISTS_TAC `s' : A stream` THEN
   ASM_REWRITE_TAC [is_proper_suffix_stream_def]);;

export_thm parse_cases;;

let is_parser_none = prove
  (`is_parser (parser_none : A -> A stream -> (B # A stream) option)`,
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
    MP_TAC (ISPEC `s : A stream` stream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_stream_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_none; parser_none_def]);;

export_thm parse_parse_none;;

let is_parser_all = prove
  (`is_parser (parser_all : A -> A stream -> (A # A stream) option)`,
   REWRITE_TAC
     [is_parser_def; parser_all_def; case_option_def; is_suffix_stream_refl]);;

export_thm is_parser_all;;

let dest_parse_all = prove
  (`dest_parser (parse_all : (A,A) parser) = parser_all`,
   REWRITE_TAC
     [parse_all_def; GSYM (CONJUNCT2 parser_tybij); is_parser_all]);;

export_thm dest_parse_none;;

let parse_parse_all = prove
  (`parse (parse_all : (A,A) parser) =
    case_stream NONE NONE (\a s. SOME (a,s))`,
    ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `x : A stream` stream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_stream_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_all; parser_all_def]);;

export_thm parse_parse_all;;

let parse_all_inverse = prove
  (`parse_inverse (parse_all : (A,A) parser) (\a. CONS a [])`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_all; append_stream_def; case_stream_def;
      case_option_def]);;

export_thm parse_all_inverse;;

let parse_all_strong_inverse = prove
  (`parse_strong_inverse (parse_all : (A,A) parser) (\a. CONS a [])`,
   REWRITE_TAC [parse_strong_inverse_def; parse_all_inverse] THEN
   ASM_REWRITE_TAC [parse_parse_all; append_stream_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `s : A stream` stream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC
     [case_stream_def; option_distinct; stream_inj; option_inj; PAIR_EQ]);;

export_thm parse_all_strong_inverse;;

let is_parser_partial_map = prove
  (`!f p. is_parser (parser_partial_map (f : B -> C option) (p : (A,B) parser))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def; parser_partial_map_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPECL [`p : (A,B) parser`;
                   `x : A`; `xs : A stream`] dest_parser_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPECL [`(f : B -> C option) b`] option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def]);;

export_thm is_parser_partial_map;;

let dest_parse_partial_map = prove
  (`!f p.
      dest_parser (parse_partial_map (f : B -> C option) (p : (A,B) parser)) =
      parser_partial_map f p`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC
     [parse_partial_map_def; GSYM (CONJUNCT2 parser_tybij);
      is_parser_partial_map]);;

export_thm dest_parse_partial_map;;

let parse_parse_partial_map = prove
  (`!f p s.
      parse (parse_partial_map (f : B -> C option) (p : (A,B) parser)) s =
      case_option
        NONE
        (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
        (parse p s)`,
    REPEAT GEN_TAC THEN
    MP_TAC (ISPEC `s : A stream` stream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_partial_map; parser_partial_map_def]);;

export_thm parse_parse_partial_map;;

let parse_partial_map_inverse = prove
  (`!f p g e.
      parse_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = SOME b) ==>
      parse_inverse (parse_partial_map (f : B -> C option) p) (\c. e (g c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_partial_map; append_stream_def; case_stream_def;
      case_option_def]);;

export_thm parse_partial_map_inverse;;

let parse_partial_map_strong_inverse = prove
  (`!(f : B -> C option) p g e.
      parse_strong_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = SOME b) /\
      (!b1 b2 c. f b1 = SOME c /\ f b2 = SOME c ==> b1 = b2) ==>
      parse_strong_inverse (parse_partial_map f p) (\c. e (g c))`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_partial_map_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_partial_map; append_stream_def] THEN
    MP_TAC (ISPECL [`p : (A,B) parser`; `s : A stream`] parse_cases) THEN
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

export_thm parse_partial_map_strong_inverse;;

let dest_parse_map = prove
  (`!f p a s.
      dest_parser (parse_map (f : B -> C) (p : (A,B) parser)) a s =
      case_option
        NONE
        (\ (b,s'). SOME (f b, s'))
        (dest_parser p a s)`,
   REWRITE_TAC
     [parse_map_def; dest_parse_partial_map; parser_partial_map_def;
      case_option_def]);;

export_thm dest_parse_map;;

let parse_parse_map = prove
  (`!f p s.
      parse (parse_map (f : B -> C) (p : (A,B) parser)) s =
      case_option
        NONE
        (\ (b,s'). SOME (f b, s'))
        (parse p s)`,
   REWRITE_TAC [parse_map_def; parse_parse_partial_map; case_option_def]);;

export_thm parse_parse_map;;

let parse_map_inverse = prove
  (`!f p g e.
      parse_inverse (p : (A,B) parser) e /\
      (!b. f (g b) = b) ==>
      parse_inverse (parse_map (f : B -> C) p) (\c. e (g c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_map; append_stream_def; case_stream_def;
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
    ASM_REWRITE_TAC [parse_parse_map; append_stream_def] THEN
    MP_TAC (ISPECL [`p : (A,B) parser`; `s : A stream`] parse_cases) THEN
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
  (`!pb pc. is_parser (parser_pair (pb : (A,B) parser) (pc : (A,C) parser))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def; parser_pair_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`pb : (A,B) parser`; `x : A`; `xs : A stream`]
             dest_parser_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MP_TAC (ISPECL [`pc : (A,C) parser`; `s' : A stream`]
             parse_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   ASM_MESON_TAC [is_suffix_stream_trans; is_suffix_stream_proper]);;

export_thm is_parser_pair;;

let dest_parse_pair = prove
  (`!pb pc.
      dest_parser (parse_pair (pb : (A,B) parser) (pc : (A,C) parser)) =
      parser_pair pb pc`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [parse_pair_def; GSYM (CONJUNCT2 parser_tybij); is_parser_pair]);;

export_thm dest_parse_pair;;

let parse_parse_pair = prove
  (`!pb pc s.
      parse (parse_pair pb pc : (A, B # C) parser) s =
      case_option
        NONE
        (\ (b,s').
           case_option
             NONE
             (\ (c,s''). SOME ((b,c),s''))
             (parse pc s'))
        (parse pb s)`,
    REPEAT STRIP_TAC THEN
    MP_TAC (ISPEC `s : A stream` stream_cases) THEN
    REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_def; case_option_def] THEN
    REWRITE_TAC [dest_parse_pair; parser_pair_def]);;

export_thm parse_parse_pair;;

let parse_pair_inverse = prove
  (`!pb pc eb ec.
      parse_inverse pb eb /\ parse_inverse pc ec ==>
      parse_inverse
        (parse_pair pb pc : (A, B # C) parser)
        (\ (b,c). APPEND (eb b) (ec c))`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   REWRITE_TAC [parse_parse_pair] THEN
   MP_TAC (ISPEC `x : B # C` PAIR_SURJECTIVE) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [append_stream_assoc; case_option_def]);;

export_thm parse_pair_inverse;;

let parse_pair_strong_inverse = prove
  (`!pb pc eb ec.
      parse_strong_inverse pb eb /\ parse_strong_inverse pc ec ==>
      parse_strong_inverse
        (parse_pair pb pc : (A, B # C) parser)
        (\ (b,c). APPEND (eb b) (ec c))`,
   REWRITE_TAC [parse_strong_inverse_def] THEN
   REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC parse_pair_inverse THEN
    ASM_REWRITE_TAC [];
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `x : B # C` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [parse_parse_pair; append_stream_assoc] THEN
    MP_TAC (ISPEC `parse (pb : (A,B) parser) s` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `a : B # A stream` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    STRIP_TAC THEN
    MP_TAC (ISPEC `parse (pc : (A,C) parser) y'` option_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def; option_distinct] THEN
    POP_ASSUM MP_TAC THEN
    MP_TAC (ISPEC `a' : C # A stream` PAIR_SURJECTIVE) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [] THEN
    REWRITE_TAC [option_inj; PAIR_EQ] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `parse (pc : (A,C) parser) y' = SOME (x''',y'')` THEN
    UNDISCH_TAC `parse (pb : (A,B) parser) s = SOME (x'',y')` THEN
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
     [parse_option_def; dest_parse_partial_map; parser_partial_map_def;
      case_option_def; dest_parse_all; parser_all_def]);;

export_thm dest_parse_option;;

let parse_parse_option = prove
  (`!f.
      parse (parse_option (f : A -> B option)) =
      case_stream
        NONE
        NONE
        (\a s. case_option NONE (\b. SOME (b,s)) (f a))`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC
     [parse_option_def; parse_parse_partial_map; parse_parse_all] THEN
   REPEAT STRIP_TAC THEN
   MP_TAC (ISPEC `x : A stream` stream_cases) THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC [case_stream_def; case_option_def]);;

export_thm parse_parse_option;;

let parse_option_inverse = prove
  (`!f e.
      (!b. f (e b) = SOME b) ==>
      parse_inverse (parse_option (f : A -> B option)) (\b. CONS (e b) [])`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC
     [parse_parse_option; append_stream_def; case_stream_def;
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
    ASM_REWRITE_TAC [parse_parse_option; append_stream_def] THEN
    MP_TAC (ISPEC `s : A stream` stream_cases) THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_stream_def; option_distinct; stream_inj] THEN
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
      case_stream
        NONE
        NONE
        (\a s. if p a then SOME (a,s) else NONE)`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPEC `x : A stream` stream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [parse_def; case_stream_def; dest_parse_some]);;

export_thm parse_parse_some;;

logfile "parser-all-def";;

let parse_stream_exists = prove
  (`!(p : (A,B) parser). ?f.
      (f Error = Error) /\
      (f Eof = Eof) /\
      (!a s.
         f (Stream a s) =
           case_option
             Error
             (\ (b,s'). Stream b (f s'))
             (dest_parser p a s))`,
   let exists0 = prove
     (`!(p : (A,B) parser). ?f.
         !s.
           f s =
           (\f'.
              case_stream
                Error
                Eof
                (\a s'.
                   case_option
                     Error
                     (\ (b,s''). Stream b (f' s''))
                     (dest_parser p a s'))) f s`,
      GEN_TAC THEN
      MATCH_MP_TAC is_proper_suffix_stream_recursion THEN
      SIMP_TAC [] THEN
      REPEAT STRIP_TAC THEN
      MP_TAC (SPEC `s : A stream` stream_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_stream_def] THEN
      MP_TAC (ISPEC `dest_parser (p : (A,B) parser) a0 a1` option_cases) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [case_option_def] THEN
      POP_ASSUM MP_TAC THEN
      MP_TAC (ISPEC `a : B # A stream` PAIR_SURJECTIVE) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC [stream_inj] THEN
      STRIP_TAC THEN
      FIRST_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [is_proper_suffix_stream_def] THEN
      REWRITE_TAC [GSYM is_suffix_stream_def] THEN
      MATCH_MP_TAC
        (ISPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A stream`;
                 `x : B`; `y : A stream`] dest_parser_suffix_stream) THEN
      ASM_REWRITE_TAC []) in
   GEN_TAC THEN
   MP_TAC (SPEC `p : (A,B) parser` exists0) THEN
   STRIP_TAC THEN
   EXISTS_TAC `f : A stream -> B stream` THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (fun th -> CONV_TAC (LAND_CONV (REWR_CONV th))) THEN
   REWRITE_TAC [case_stream_def]);;

let (parse_stream_error,
     parse_stream_eof,
     parse_stream_stream) =
  let def =
    new_specification ["parse_stream"]
    (REWRITE_RULE [SKOLEM_THM] parse_stream_exists) in
  CONJ_TRIPLE (REWRITE_RULE [FORALL_AND_THM] def);;

export_thm parse_stream_error;;
export_thm parse_stream_eof;;
export_thm parse_stream_stream;;

let parse_stream_def =
  REWRITE_RULE [GSYM FORALL_AND_THM]
    (CONJ parse_stream_error (CONJ parse_stream_eof parse_stream_stream));;

logfile "parser-all-thm";;

let parse_stream_append = prove
  (`!p (e : A -> B list) x s.
      parse_inverse p e ==>
      parse_stream p (append_stream (e x) s) = Stream x (parse_stream p s)`,
   REWRITE_TAC [parse_inverse_def] THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM (MP_TAC o SPECL [`x : A`; `s : B stream`]) THEN
   MP_TAC (ISPEC `(e : A -> B list) x` list_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [append_stream_def] THEN
    MP_TAC (ISPECL [`p : (B,A) parser`; `s : B stream`] parse_cases) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [option_distinct];
     ASM_REWRITE_TAC [option_inj; PAIR_EQ] THEN
     STRIP_TAC THEN
     PAT_ASSUM `is_proper_suffix_stream (X : A stream) Y` THEN
     ASM_REWRITE_TAC [is_proper_suffix_stream_refl]];
    ASM_REWRITE_TAC [parse_def; parse_stream_def; append_stream_def] THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC [case_option_def]]);;

export_thm parse_stream_append;;

let parse_stream_inverse = prove
  (`!p (e : A -> B list) l.
      parse_inverse p e ==>
      parse_stream p (list_to_stream (concat (MAP e l))) =
      list_to_stream l`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`l : A list`, `l : A list`) THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC
      [MAP; concat_def; parse_stream_def; list_to_stream_def;
       append_stream_def];
    ALL_TAC] THEN
   POP_ASSUM MP_TAC THEN
   REWRITE_TAC
     [MAP; concat_def; parse_stream_def; list_to_stream_def;
      append_stream_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [SYM th]) THEN
   REWRITE_TAC [append_stream_assoc] THEN
   MATCH_MP_TAC parse_stream_append THEN
   FIRST_ASSUM ACCEPT_TAC);;

export_thm parse_stream_inverse;;

let parse_stream_strong_inverse = prove
  (`!p (e : A -> B list) s.
      parse_strong_inverse p e ==>
      case_option T (\l. stream_to_list s = SOME (concat (MAP e l)))
        (stream_to_list (parse_stream p s))`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`s : B stream`, `s : B stream`) THEN
   MATCH_MP_TAC is_proper_suffix_stream_induct THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `s : B stream` stream_cases) THEN
   STRIP_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [stream_to_list_def; parse_stream_def; case_option_def];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC
      [stream_to_list_def; parse_stream_def; case_option_def; MAP;
       concat_def];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [parse_stream_def] THEN
   MP_TAC (ISPECL [`p : (B,A) parser`; `a0 : B`; `a1 : B stream`]
           dest_parser_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def; stream_to_list_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   CONV_TAC (RAND_CONV (REWRITE_CONV [stream_to_list_def])) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `s' : B stream`) THEN
   COND_TAC THENL
   [PAT_ASSUM `is_suffix_stream (X : B stream) Y` THEN
    REWRITE_TAC [is_suffix_stream_def; is_proper_suffix_stream_def];
    ALL_TAC] THEN
   MP_TAC (ISPEC `stream_to_list (parse_stream (p : (B,A) parser) s')`
           option_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   PAT_ASSUM `parse_strong_inverse (p : (B,A) parser) e` THEN
   REWRITE_TAC [parse_strong_inverse_def] THEN
   DISCH_THEN (MP_TAC o SPECL [`Stream (a0 : B) a1`; `b : A`;
                               `s' : B stream`] o CONJUNCT2) THEN
   COND_TAC THENL
   [ASM_REWRITE_TAC [parse_def];
    ALL_TAC] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [stream_to_list_append] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REWRITE_TAC [case_option_def; option_inj; MAP; concat_def]);;

export_thm parse_stream_strong_inverse;;

let parse_stream_length = prove
  (`!(p : (A,B) parser) s.
      length_stream (parse_stream p s) <= length_stream s`,
   GEN_TAC THEN
   MATCH_MP_TAC is_proper_suffix_stream_induct THEN
   GEN_TAC THEN
   MP_TAC (ISPEC `s : A stream` stream_cases) THEN
   STRIP_TAC THENL
   [POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [length_stream_def; parse_stream_def; LE_REFL];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [length_stream_def; parse_stream_def; LE_REFL];
    ALL_TAC] THEN
   POP_ASSUM SUBST_VAR_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [parse_stream_def] THEN
   MP_TAC (ISPECL [`p : (A,B) parser`; `a0 : A`; `a1 : A stream`]
           dest_parser_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [case_option_def; length_stream_def; LE_0];
    ALL_TAC] THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   REWRITE_TAC [length_stream_def; LE_SUC] THEN
   MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `length_stream (s' : A stream)` THEN
   CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    PAT_ASSUM `is_suffix_stream (X : A stream) Y` THEN
    REWRITE_TAC [is_suffix_stream_def; is_proper_suffix_stream_def];
    MATCH_MP_TAC is_suffix_stream_length THEN
    FIRST_ASSUM ACCEPT_TAC]);;

export_thm parse_stream_length;;

logfile_end ();;

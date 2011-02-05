(* ------------------------------------------------------------------------- *)
(* A type of parse streams.                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "parser-stream-def";;

let stream_induct,stream_recursion = define_type
    "stream = Error
            | Eof
            | Stream A stream";;

export_thm stream_induct;;
export_thm stream_recursion;;

let case_stream_def = new_recursive_definition stream_recursion
  `(!e b f. case_stream e b f Error = (e:B)) /\
   (!e b f. case_stream e b f Eof = b) /\
   (!e b f a s. case_stream e b f (Stream a s) = f (a:A) s)`;;

export_thm case_stream_def;;

let length_stream_def = new_recursive_definition stream_recursion
  `(length_stream Error = 0) /\
   (length_stream Eof = 0) /\
   (!a s. length_stream (Stream a s) = SUC (length_stream s))`;;

export_thm length_stream_def;;

let is_proper_suffix_stream_def = new_recursive_definition stream_recursion
  `(!s. is_proper_suffix_stream s Error = F) /\
   (!s. is_proper_suffix_stream s Eof = F) /\
   (!s a s'. is_proper_suffix_stream s (Stream (a:A) s') =
      ((s = s') \/ is_proper_suffix_stream s s'))`;;

export_thm is_proper_suffix_stream_def;;

let is_suffix_stream_def = new_definition
  `is_suffix_stream s s' =
     (((s : A stream) = s') \/ is_proper_suffix_stream s s')`;;

export_thm is_suffix_stream_def;;

let stream_to_list_def = new_recursive_definition stream_recursion
  `(stream_to_list Error = NONE) /\
   (stream_to_list Eof = SOME []) /\
   (!a s. stream_to_list (Stream a s) =
      case_option
        NONE
        (\l. SOME (CONS (a:A) l))
        (stream_to_list s))`;;

export_thm stream_to_list_def;;

let append_stream_def = new_recursive_definition list_RECURSION
  `(!s. append_stream [] s = s) /\
   (!h t s. append_stream (CONS h t) s = Stream (h:A) (append_stream t s))`;;

export_thm append_stream_def;;

let list_to_stream_def = new_definition
  `!l. list_to_stream l = append_stream l Eof`;;

export_thm list_to_stream_def;;

logfile "parser-stream-thm";;

let stream_cases = prove_cases_thm stream_induct;;

export_thm stream_cases;;

let stream_distinct = distinctness "stream";;

export_thm stream_distinct;;

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

let is_proper_suffix_stream_induct = prove
  (`!(p: A stream-> bool).
       (!x. (!y. is_proper_suffix_stream y x ==> p y) ==> p x) ==> !x. p x`,
   REWRITE_TAC [GSYM WF_IND; is_proper_suffix_stream_wf]);;

export_thm is_proper_suffix_stream_induct;;

let is_proper_suffix_stream_induct = prove
  (`!(p: A stream-> bool).
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

logfile "parser-basic-def";;

let is_parser_def = new_definition
  `is_parser (p : A -> A stream -> (B # A stream) option) =
     !x xs. case_option
              T
              (\ (y,xs'). is_suffix_stream xs' xs)
              (p x xs)`;;

export_thm is_parser_def;;

let parser_exists = prove
  (`?(p : A -> A stream -> (B # A stream) option). is_parser p`,
   EXISTS_TAC `\(x:A) (s:A stream). (NONE : (B # A stream) option)` THEN
   REWRITE_TAC [is_parser_def; case_option_def]);;

let parser_tybij =
    new_type_definition "parser" ("mk_parser","dest_parser") parser_exists;;

export_thm parser_tybij;;

let parse_def = new_recursive_definition stream_recursion
  `(parse (p : (A,B) parser) Error = NONE) /\
   (parse p Eof = NONE) /\
   (parse p (Stream a s) = dest_parser p a s)`;;

export_thm parse_def;;

let parser_pair_def = new_definition
  `parser_pair (pb : (A,B) parser) (pc : (A,C) parser) a s =
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
  `parse_pair (pb : (A,B) parser) (pc : (A,C) parser) =
     mk_parser (parser_pair pb pc)`;;

export_thm parse_pair_def;;

let parser_option_def = new_definition
  `parser_option (f : A -> B option) a (s : A stream) =
      case_option NONE (\b. SOME (b,s)) (f a)`;;

export_thm parser_option_def;;

let parse_option_def = new_definition
  `parse_option (f : A -> B option) = mk_parser (parser_option f)`;;

export_thm parse_option_def;;

let parse_some_def = new_definition
  `parse_some (p : A -> bool) =
   parse_option (\a. if p a then SOME a else NONE)`;;

export_thm parse_some_def;;

let parse_inverse_def = new_definition
  `!p e.
     parse_inverse p e =
     !x s. parse p (append_stream (e x) s) = SOME (x,s)`;;

export_thm parse_inverse_def;;

logfile "parser-basic-thm";;

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

let is_parser_option = prove
  (`!f. is_parser (parser_option (f : A -> B option))`,
   REPEAT GEN_TAC THEN
   REWRITE_TAC [is_parser_def; parser_option_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (ISPECL [`(f : A -> B option) x`] option_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_option_def] THEN
   MATCH_ACCEPT_TAC is_suffix_stream_refl);;

export_thm is_parser_option;;

logfile "parser-rec";;

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

let parse_stream_def = new_specification ["parse_stream"]
  (REWRITE_RULE[SKOLEM_THM] parse_stream_exists);;

export_thm parse_stream_def;;

logfile_end ();;

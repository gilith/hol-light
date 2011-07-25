(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

let datatype_stream =
    CONJ (CONJ stream_induct stream_recursion) case_stream_def;;

export_thm datatype_stream;;

let value_length_stream = prove
  (`!(s : A stream).
       length_stream s =
         case_stream 0 0 (\a s. length_stream s + 1) s`,
   GEN_TAC THEN
   MP_TAC (SPEC `s : A stream` stream_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [length_stream_def; case_stream_def; ADD1]);;

export_thm value_length_stream;;

(***
let is_proper_suffix_streamH_def = new_definition
  `!s s'.
     is_proper_suffix_streamH (s : A streamH) s' <=>
     is_proper_suffix_stream (dest_streamH s) (dest_streamH s')`;;

export_thm is_proper_suffix_streamH_def;;

let is_suffix_streamH_def = new_definition
  `!s s'.
     is_suffix_streamH (s : A streamH) s' <=>
     is_suffix_stream (dest_streamH s) (dest_streamH s')`;;

export_thm is_suffix_streamH_def;;

let stream_to_listH_def = new_definition
  `!s.
     stream_to_listH (s : A streamH) =
     stream_to_list (dest_streamH s)`;;

export_thm stream_to_listH_def;;

let append_streamH_def = new_definition
  `!l s.
     append_streamH (l : A list) s =
     mk_streamH (append_stream l (dest_streamH s))`;;

export_thm append_streamH_def;;

let list_to_streamH_def = new_definition
  `!l. list_to_streamH (l : A list) = mk_streamH (list_to_stream l)`;;

export_thm list_to_streamH_def;;

let is_parserH_def = new_definition
  `!p.
     is_parserH (p : A -> A streamH -> (B # A streamH) option) =
     is_parser
       (\x xs.
          case_option
            NONE
            (\ (y,xs'). SOME (y, dest_streamH xs'))
            (p x (mk_streamH xs)))`;;

export_thm is_parserH_def;;

(***
let parserH_exists = prove
  (`?p. is_parserH (p : A -> A streamH -> (B # A streamH) option)`,
   REWRITE_TAC [is_parserH_def] THEN
   EXISTS_TAC
     `\x xs.
        case_option NONE (\ (y,xs'). SOME (y, mk_streamH xs'))
          (dest_parser (p : (A,B) parser) x (dest_streamH xs))` THEN
   REWRITE_TAC [streamH_tybij] THEN
   KNOW_TAC `is_parser (dest_parser (p : (A,B) parser))` THENL
   [REWRITE_TAC [parser_tybij];
    ALL_TAC] THEN

;;
***)

let parserH_exists = prove
  (`?p. (\x. T) (p : (A,B) parser)`,
   REWRITE_TAC []);;

let parserH_tybij =
    REWRITE_RULE []
    (new_type_definition "parserH"
       ("mk_parserH","dest_parserH") parserH_exists);;

export_thm parserH_tybij;;

(***
let mk_ParserH_def = new_definition
  `!p. ParserH p = mk_parserH (mk_parser p : (A,B) parser)`;;

let ParserH_def = new_definition
  `!p. ParserH p = mk_parserH (mk_parser p : (A,B) parser)`;;

export_thm ParserH_def;;

let unParserH_def = new_definition
  `!p. unParserH (p : (A,B) parserH) = dest_parser (dest_parserH p)`;;

export_thm unParserH_def;;
***)

logfile "haskell-parser-thm";;

let dest_streamH_inj = prove
  (`!s t. dest_streamH (s : A streamH) = dest_streamH t ==> s = t`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM streamH_tybij] THEN
   ASM_REWRITE_TAC []);;

export_thm dest_streamH_inj;;

let dest_streamH_inj_eq = prove
  (`!s t. dest_streamH (s : A streamH) = dest_streamH t <=> s = t`,
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [MATCH_ACCEPT_TAC dest_streamH_inj;
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm dest_streamH_inj_eq;;

(* Needed?
let case_streamH = prove
  (`(!e b f. case_streamH e b f (ErrorH : A streamH) = (e : B)) /\
    (!e b f. case_streamH e b f (EofH : A streamH) = (b : B)) /\
    (!e b f a s. case_streamH (e : B) b f (StreamH a s) = f (a : A) s)`,
   REWRITE_TAC
     [case_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
      case_stream_def]);;

export_thm case_streamH;;
*)

let streamH_induct = prove
  (`!P.
      P ErrorH /\ P EofH /\ (!h t. P t ==> P (StreamH (h : A) t)) ==>
      !s. P s`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM streamH_tybij] THEN
   SPEC_TAC (`dest_streamH (s : A streamH)`, `s : A stream`) THEN
   MATCH_MP_TAC stream_induct THEN
   REPEAT (POP_ASSUM MP_TAC) THEN
   REWRITE_TAC [ErrorH_def; EofH_def; StreamH_def] THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   DISCH_THEN (fun th -> REWRITE_TAC [th]) THEN
   REPEAT STRIP_TAC THEN
   CONV_TAC (RAND_CONV (RAND_CONV
     (RAND_CONV (ONCE_REWRITE_CONV [GSYM streamH_tybij])))) THEN
   FIRST_X_ASSUM MATCH_MP_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

let streamH_recursion = prove
  (`!f0 f1 f2. ?fn.
      fn ErrorH = (f0 : B) /\
      fn EofH = f1 /\
      (!h t. fn (StreamH (h : A) t) = f2 h t (fn t))`,
   REPEAT GEN_TAC THEN
   MP_TAC
     (ISPECL
        [`f0 : B`; `f1 : B`;
         `\a s x. (f2 : A -> A streamH -> B -> B) a (mk_streamH s) x`]
        stream_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `\s. (fn : A stream -> B) (dest_streamH s)` THEN
   ASM_REWRITE_TAC [ErrorH_def; EofH_def; StreamH_def; streamH_tybij]);;

let streamH_data = CONJ streamH_induct streamH_recursion;;

export_thm streamH_data;;

let length_streamH = prove
  (`(length_streamH (ErrorH : A streamH) = 0) /\
    (length_streamH (EofH : A streamH) = 0) /\
    (!h t. length_streamH (StreamH (h : A) t) = length_streamH t + 1)`,
   REWRITE_TAC
     [length_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
      length_stream_def; ADD1]);;

export_thm length_streamH;;

let is_proper_suffix_streamH = prove
  (`(!s. is_proper_suffix_streamH (s : A streamH) ErrorH = F) /\
    (!s. is_proper_suffix_streamH (s : A streamH) EofH = F) /\
    (!s h t.
       is_proper_suffix_streamH s (StreamH (h:A) t) =
       ((s = t) \/ is_proper_suffix_streamH s t))`,
   REWRITE_TAC
     [is_proper_suffix_streamH_def; ErrorH_def; EofH_def; StreamH_def;
      streamH_tybij; is_proper_suffix_stream_def; dest_streamH_inj_eq]);;

export_thm is_proper_suffix_streamH;;

let is_suffix_streamH = prove
  (`!s s'.
      is_suffix_streamH s s' =
      (((s : A streamH) = s') \/ is_proper_suffix_streamH s s')`,
   REWRITE_TAC
     [is_suffix_streamH_def; ErrorH_def; EofH_def; StreamH_def;
      is_suffix_stream_def; is_proper_suffix_streamH_def;
      dest_streamH_inj_eq]);;

export_thm is_suffix_streamH;;

let stream_to_listH = prove
  (`(stream_to_listH (ErrorH : A streamH) = NONE) /\
    (stream_to_listH (EofH : A streamH) = SOME []) /\
    (!h t.
       stream_to_listH (StreamH h t) =
       case_option
         NONE
         (\l. SOME (CONS (h:A) l))
         (stream_to_listH t))`,
   REWRITE_TAC
     [stream_to_listH_def; ErrorH_def; EofH_def; StreamH_def;
      streamH_tybij; stream_to_list_def]);;

export_thm stream_to_listH;;

let append_streamH = prove
  (`(!s. append_streamH [] (s : A streamH) = s) /\
    (!h t s.
       append_streamH (CONS h t) s =
       StreamH (h:A) (append_streamH t s))`,
   REWRITE_TAC
     [append_streamH_def; append_stream_def; StreamH_def;
      streamH_tybij]);;

export_thm append_streamH;;

let list_to_streamH = prove
  (`!l. list_to_streamH (l : A list) = append_streamH l EofH`,
   REWRITE_TAC
     [list_to_streamH_def; append_streamH_def; list_to_stream_def;
      EofH_def; streamH_tybij]);;

export_thm list_to_streamH;;

let parserH_newtype = prove
  (`(!p. ParserH (unParserH p) = (p : (A,B) parserH)) /\
    (!f. is_parserH f <=> unParserH (ParserH f : (A,B) parserH) = f)`,

      is_parserH (p : A -> A streamH -> (B # A streamH) option) =
      !x xs.
        case_option
          T
          (\ (y,xs'). is_suffix_streamH xs' xs)
          (p x xs)`,

(***
let is_parserH = prove
  (`!p.
      is_parserH (p : A -> A streamH -> (B # A streamH) option) =
      !x xs.
        case_option
          T
          (\ (y,xs'). is_suffix_streamH xs' xs)
          (p x xs)`,
   REWRITE_TAC [is_parserH_def; is_parser_def; is_suffix_streamH_def] THEN
   STRIP_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (fun th ->
      REPEAT GEN_TAC THEN
      MP_TAC (SPECL [`x : A`; `dest_streamH (xs : A streamH)`] th)) THEN
    REWRITE_TAC [streamH_tybij] THEN
    MP_TAC (ISPEC `(p : A -> A streamH -> (B # A streamH) option) x xs`
            option_cases) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [case_option_def];
     ASM_REWRITE_TAC [case_option_def] THEN
     MP_TAC (ISPEC `a : B # A streamH` PAIR_SURJECTIVE) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def]];
    DISCH_THEN (fun th ->
      REPEAT GEN_TAC THEN
      MP_TAC (SPECL [`x : A`; `mk_streamH (xs : A stream)`] th)) THEN
    REWRITE_TAC [streamH_tybij] THEN

    MP_TAC (ISPEC `(p : A -> A streamH -> (B # A streamH) option) x
                     (mk_streamH xs)` option_cases) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [case_option_def];
     ASM_REWRITE_TAC [case_option_def] THEN
     MP_TAC (ISPEC `a : B # A streamH` PAIR_SURJECTIVE) THEN
     STRIP_TAC THEN
     ASM_REWRITE_TAC [case_option_def]]]);;

export_thm is_parserH;;
***)

logfile "haskell-parser-test";;
***)

logfile_end ();;

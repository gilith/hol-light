(* ========================================================================= *)
(* STREAM PARSERS                                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for stream parsers.                                       *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation
  "opentheory/theories/haskell-parser/haskell-parser.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of stream parsers.                                             *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-def";;

(* Streams *)

let pstreamH_tybij = define_haskell_type
  `:A pstream`
  [("map_pstream",true,false)];;

export_thm pstreamH_tybij;;

let ErrorPstreamH_def = define_haskell_const
  `ErrorPstream : A pstream`;;

export_thm ErrorPstreamH_def;;

let EofPstreamH_def = define_haskell_const
  `EofPstream : A pstream`;;

export_thm EofPstreamH_def;;

let ConsPstreamH_def = define_haskell_const
  `ConsPstream : A -> A pstream -> A pstream`;;

export_thm ConsPstreamH_def;;

let case_pstreamH_def = define_haskell_const
  `case_pstream : B -> B -> (A -> A pstream -> B) -> A pstream -> B`;;

export_thm case_pstreamH_def;;

let length_pstreamH_def = define_haskell_const
  `length_pstream : A pstream -> num`;;

export_thm length_pstreamH_def;;

let pstream_to_listH_def = define_haskell_const
  `pstream_to_list : A pstream -> (A list) option`;;

export_thm pstream_to_listH_def;;

let append_pstreamH_def = define_haskell_const
  `append_pstream : A list -> A pstream -> A pstream`;;

export_thm append_pstreamH_def;;

let list_to_pstreamH_def = define_haskell_const
  `list_to_pstream : A list -> A pstream`;;

export_thm list_to_pstreamH_def;;

let rdecode_pstreamH_def = define_haskell_const
  `rdecode_pstream : (random -> A # random) -> random -> A pstream # random`;;

export_thm rdecode_pstreamH_def;;

(* Parsers *)

let parserH_tybij = define_haskell_type
  `:(A,B) parser`
  [("parse_map_token",true,true);
   ("parse_map",true,false)];;

export_thm parserH_tybij;;

let mk_parserH_def = define_haskell_const
  `mk_parser : (A -> A pstream -> (B # A pstream) option) -> (A,B) parser`;;

export_thm mk_parserH_def;;

let dest_parserH_def = define_haskell_const
  `dest_parser : (A,B) parser -> A -> A pstream -> (B # A pstream) option`;;

export_thm dest_parserH_def;;

let parseH_def = define_haskell_const
  `parse : (A,B) parser -> A pstream -> (B # A pstream) option`;;

export_thm parseH_def;;

let parser_noneH_def = define_haskell_const
  `parser_none : A -> A pstream -> (B # A pstream) option`;;

export_thm parser_noneH_def;;

let parse_noneH_def = define_haskell_const
  `parse_none : (A,B) parser`;;

export_thm parse_noneH_def;;

let parser_allH_def = define_haskell_const
  `parser_all : A -> A pstream -> (A # A pstream) option`;;

export_thm parser_allH_def;;

let parse_allH_def = define_haskell_const
  `parse_all : (A,A) parser`;;

export_thm parse_allH_def;;

let parser_partial_mapH_def = define_haskell_const
  `parser_partial_map :
   (B -> C option) -> (A,B) parser -> A -> A pstream ->
   (C # A pstream) option`;;

export_thm parser_partial_mapH_def;;

let parse_partial_mapH_def = define_haskell_const
  `parse_partial_map : (B -> C option) -> (A,B) parser -> (A,C) parser`;;

export_thm parse_partial_mapH_def;;

let parse_mapH_def = define_haskell_const
  `parse_map : (B -> C) -> (A,B) parser -> (A,C) parser`;;

export_thm parse_mapH_def;;

let parser_pairH_def = define_haskell_const
  `parser_pair :
   (A,B) parser -> (A,C) parser -> A -> A pstream ->
   ((B # C) # A pstream) option`;;

export_thm parser_pairH_def;;

let parse_pairH_def = define_haskell_const
  `parse_pair : (A,B) parser -> (A,C) parser -> (A, B # C) parser`;;

export_thm parse_pairH_def;;

let parse_optionH_def = define_haskell_const
  `parse_option : (A -> B option) -> (A,B) parser`;;

export_thm parse_optionH_def;;

let parse_someH_def = define_haskell_const
  `parse_some : (A -> bool) -> (A,A) parser`;;

export_thm parse_someH_def;;

let parse_pstreamH_def = define_haskell_const
  `parse_pstream : (A,B) parser -> A pstream -> B pstream`;;

export_thm parse_pstreamH_def;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for stream parsers.                                        *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

(* Streams *)

let () = (export_haskell_thm o prove)
 (`(!e b (f : A -> A pstreamH -> B). case_pstreamH e b f ErrorPstreamH = e) /\
   (!e b (f : A -> A pstreamH -> B). case_pstreamH e b f EofPstreamH = b) /\
   (!e b (f : A -> A pstreamH -> B) a s.
      case_pstreamH e b f (ConsPstreamH a s) = f a s)`,
  HASKELL_TAC [case_pstream_def]);;

let () = (export_haskell_thm o prove)
 (`length_pstreamH (ErrorPstreamH : A pstreamH) = 0 /\
   length_pstreamH (EofPstreamH : A pstreamH) = 0 /\
   (!(a:A) s. length_pstreamH (ConsPstreamH a s) = length_pstreamH s + 1)`,
  HASKELL_TAC [length_pstream_def; ADD1]);;

let () = (export_haskell_thm o prove)
 (`pstream_to_listH (ErrorPstreamH : A pstreamH) = NONE /\
   pstream_to_listH (EofPstreamH : A pstreamH) = SOME [] /\
   (!(a : A) s.
      pstream_to_listH (ConsPstreamH a s) =
      case_option NONE (\l. SOME (CONS a l)) (pstream_to_listH s))`,
  HASKELL_TAC [pstream_to_list_def]);;

let () = (export_haskell_thm o prove)
 (`(!(s : A pstreamH). append_pstreamH [] s = s) /\
   (!(h : A) t s.
      append_pstreamH (CONS h t) s = ConsPstreamH h (append_pstreamH t s))`,
  HASKELL_TAC [append_pstream_def]);;

let () = (export_haskell_thm o prove)
 (`!(l : A list). list_to_pstreamH l = append_pstreamH l EofPstreamH`,
  HASKELL_TAC [list_to_pstream_def]);;

let () = (export_haskell_thm o prove)
 (`!(d : random -> A # random) r.
     rdecode_pstreamH d r =
     let (l,r') = rdecode_listH d r in
     let (b,r'') = rbit r' in
     (append_pstreamH l (if b then ErrorPstreamH else EofPstreamH), r'')`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [LET_DEF; LET_END_DEF; rdecode_pstream_def] THEN
  PAIR_CASES_TAC `rdecode_list (d : random -> A # random) r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : A list` (X_CHOOSE_THEN `r' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  PAIR_CASES_TAC `rbit r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool` (X_CHOOSE_THEN `r'' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `b : bool` THEN
  HASKELL_TAC []);;

(* Parsers *)

let () = (export_haskell_thm o prove)
 (`!(p : (A,B) parserH).
     mk_parserH (dest_parserH p) = p`,
  HASKELL_TAC [parser_tybij]);;

let () = (export_haskell_thm o prove)
 (`(!(p : (A,B) parserH). parseH p ErrorPstreamH = NONE) /\
   (!(p : (A,B) parserH). parseH p EofPstreamH = NONE) /\
   (!(p : (A,B) parserH) a s.
      parseH p (ConsPstreamH a s) = dest_parserH p a s)`,
  HASKELL_TAC [parse_def; map_option_def]);;

let () = (export_haskell_thm o prove)
 (`!a s. parser_noneH a s = (NONE : (B # A pstreamH) option)`,
  HASKELL_TAC [parser_none_def; map_option_def]);;

let () = (export_haskell_thm o prove)
 (`(parse_noneH : (A,B) parserH) = mk_parserH parser_noneH`,
  HASKELL_TAC [parse_none_def]);;

let () = (export_haskell_thm o prove)
 (`!(a : A) s. parser_allH a s = SOME (a,s)`,
  HASKELL_TAC [parser_all_def; map_option_def]);;

let () = (export_haskell_thm o prove)
 (`(parse_allH : (A,A) parserH) = mk_parserH parser_allH`,
  HASKELL_TAC [parse_all_def]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C option) (p : (A,B) parserH) a s.
     parser_partial_mapH f p a s =
     case_option
       NONE
       (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
       (dest_parserH p a s)`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [parser_partial_map_def] THEN
  option_cases_tac
    `dest_parser (destH_parserH p : (A,B) parser) a (destH_pstreamH s)` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bs : B # A pstream` SUBST1_TAC) THEN
  PAIR_CASES_TAC `bs : B # A pstream` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : B`
      (X_CHOOSE_THEN `s' : A pstream` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_snd_def] THEN
  option_cases_tac `(f : B -> C option) b` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_snd_def]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C option) (p : (A,B) parserH).
     parse_partial_mapH f p = mk_parserH (parser_partial_mapH f p)`,
  HASKELL_TAC [parse_partial_map_def]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C) (p : (A,B) parserH).
     parse_mapH f p = parse_partial_mapH (\b. SOME (f b)) p`,
  HASKELL_TAC [parse_map_def]);;

let () = (export_haskell_thm o prove)
 (`!(pb : (A,B) parserH) (pc : (A,C) parserH) a s.
     parser_pairH pb pc a s =
     case_option
       NONE
       (\ (b,s').
          case_option
            NONE
            (\ (c,s''). SOME ((b,c),s''))
            (parseH pc s'))
       (dest_parserH pb a s)`,
  REPEAT GEN_TAC THEN
  HASKELL_TAC [parser_pair_def] THEN
  option_cases_tac
    `dest_parser (destH_parserH pb : (A,B) parser) a (destH_pstreamH s)` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bs : B # A pstream` SUBST1_TAC) THEN
  PAIR_CASES_TAC `bs : B # A pstream` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : B`
      (X_CHOOSE_THEN `s' : A pstream` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_snd_def] THEN
  HASKELL_TAC [] THEN
  option_cases_tac `parse (destH_parserH pc : (A,C) parser) s'` THENL
  [STRIP_TAC THEN
   ASM_REWRITE_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `cs : C # A pstream` SUBST1_TAC) THEN
  PAIR_CASES_TAC `cs : C # A pstream` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `c : C`
      (X_CHOOSE_THEN `s'' : A pstream` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_snd_def]);;

let () = (export_haskell_thm o prove)
 (`!(pb : (A,B) parserH) (pc : (A,C) parserH).
     parse_pairH pb pc = mk_parserH (parser_pairH pb pc)`,
  HASKELL_TAC [parse_pair_def]);;

let () = (export_haskell_thm o prove)
 (`!(f : A -> B option).
     parse_optionH f = parse_partial_mapH f parse_allH`,
  HASKELL_TAC [parse_option_def]);;

let () = (export_haskell_thm o prove)
 (`!(p : A -> bool).
     parse_someH p = parse_optionH (\a. if p a then SOME a else NONE)`,
  HASKELL_TAC [parse_some_def]);;

let () = (export_haskell_thm o prove)
 (`(!(p : (A,B) parserH). parse_pstreamH p ErrorPstreamH = ErrorPstreamH) /\
   (!(p : (A,B) parserH). parse_pstreamH p EofPstreamH = EofPstreamH) /\
   (!(p : (A,B) parserH) a s.
      parse_pstreamH p (ConsPstreamH a s) =
      case_option
        ErrorPstreamH
        (\ (b,s'). ConsPstreamH b (parse_pstreamH p s'))
        (dest_parserH p a s))`,
  REPEAT STRIP_TAC THEN
  HASKELL_TAC [parse_pstream_def] THEN
  option_cases_tac
    `dest_parser (destH_parserH p : (A,B) parser) a (destH_pstreamH s)` THENL
  [DISCH_THEN SUBST1_TAC THEN
   HASKELL_TAC [map_option_def; case_option_def];
   ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_THEN `bs : B # A pstream` SUBST1_TAC) THEN
  PAIR_CASES_TAC `bs : B # A pstream` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : B`
      (X_CHOOSE_THEN `s' : A pstream` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [map_option_def; case_option_def; map_snd_def] THEN
  HASKELL_TAC []);;

(* ------------------------------------------------------------------------- *)
(* QuickCheck tests for stream parsers.                                      *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-test";;

(* Streams *)

let () = (export_haskell_thm o prove)
 (`!r.
     let (l,r') = rdecode_listH rdecode_fibH r in
     equal_optionH (equal_listH (=))
       (pstream_to_listH (list_to_pstreamH l)) (SOME l)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : num list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [list_to_pstream_to_list]);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (l,r') = rdecode_listH rdecode_fibH r in
     let (s,r'') = rdecode_pstreamH rdecode_fibH r' in
     length_pstreamH (append_pstreamH l s) =
     lengthH l + length_pstreamH s`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : num list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_pstreamH rdecode_fibH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num pstreamH`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [append_pstream_length]);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (l,r') = rdecode_listH rdecode_fibH r in
     let (s,r'') = rdecode_pstreamH rdecode_fibH r' in
     equal_optionH (equal_listH (=))
       (pstream_to_listH (append_pstreamH l s))
       (case_option NONE (\ls. SOME (APPEND l ls)) (pstream_to_listH s))`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : num list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  PAIR_CASES_TAC `rdecode_pstreamH rdecode_fibH r'` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num pstreamH`
      (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MATCH_ACCEPT_TAC pstream_to_list_append);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (l,r') = rdecode_listH rdecode_fibH r in
     length_pstreamH (list_to_pstreamH l) = lengthH l`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : num list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MATCH_ACCEPT_TAC list_to_pstream_length);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (s,r') = rdecode_pstreamH rdecode_fibH r in
     case_option T (\l. lengthH l = length_pstreamH s) (pstream_to_listH s)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_pstreamH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num pstreamH`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  HASKELL_TAC [] THEN
  MATCH_ACCEPT_TAC pstream_to_list_length);;

(* Parsers *)

logfile_end ();;

(* ========================================================================= *)
(* SIMPLE STREAM PARSERS IN HASKELL                                          *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(***
type_invention_error := false;;
***)

(* ------------------------------------------------------------------------- *)
(* Definition.                                                               *)
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

(***
let (parserH_lift_drop,parserH_drop_lift) =
  let exists = prove (`?(p : (A,B) parser). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "parserH" ("lift_parserH","drop_parserH") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm parserH_lift_drop;;
export_thm parserH_drop_lift;;

let parserH_tybij = CONJ parserH_lift_drop parserH_drop_lift;;

let (lift_parser_resultH_none,lift_parser_resultH_some) =
  let def = new_definition
    `(lift_parser_resultH : (B # A pstream) option -> (B # A pstreamH) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, lift_pstreamH s'))` in
  let th_none = prove
    (`lift_parser_resultH (NONE : (B # A pstream) option) =
      (NONE : (B # A pstreamH) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A pstream).
         lift_parser_resultH (SOME (b,s)) = SOME (b, lift_pstreamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm lift_parser_resultH_none;;
export_thm lift_parser_resultH_some;;

let lift_parser_resultH_def =
    CONJ lift_parser_resultH_none lift_parser_resultH_some;;

let (drop_parser_resultH_none,drop_parser_resultH_some) =
  let def = new_definition
    `(drop_parser_resultH : (B # A pstreamH) option -> (B # A pstream) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, drop_pstreamH s'))` in
  let th_none = prove
    (`drop_parser_resultH (NONE : (B # A pstreamH) option) =
      (NONE : (B # A pstream) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A pstreamH).
         drop_parser_resultH (SOME (b,s)) = SOME (b, drop_pstreamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm drop_parser_resultH_none;;
export_thm drop_parser_resultH_some;;

let drop_parser_resultH_def =
    CONJ drop_parser_resultH_none drop_parser_resultH_some;;

let lift_parser_functionH_def = new_definition
  `!(p : A -> A pstream -> (B # A pstream) option).
     lift_parser_functionH p =
     \a s. lift_parser_resultH (p a (drop_pstreamH s))`;;

export_thm lift_parser_functionH_def;;

let drop_parser_functionH_def = new_definition
  `!(p : A -> A pstreamH -> (B # A pstreamH) option).
     drop_parser_functionH p =
     \a s. drop_parser_resultH (p a (lift_pstreamH s))`;;

export_thm drop_parser_functionH_def;;
***)

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
(* Properties.                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-thm";;

(* Parsers *)

(***
let parser_resultH_drop_lift = prove
 (`!(r : (B # A pstream) option).
     drop_parser_resultH (lift_parser_resultH r) = r`,
  GEN_TAC THEN
  MP_TAC (ISPEC `r : (B # A pstream) option` option_cases) THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [lift_parser_resultH_def; drop_parser_resultH_def];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (ISPEC `a : B # A pstream` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC
    [lift_parser_resultH_def; drop_parser_resultH_def; pstreamH_drop_lift]);;

export_thm parser_resultH_drop_lift;;

let parser_resultH_lift_drop = prove
 (`!(r : (B # A pstreamH) option).
     lift_parser_resultH (drop_parser_resultH r) = r`,
  GEN_TAC THEN
  MP_TAC (ISPEC `r : (B # A pstreamH) option` option_cases) THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [lift_parser_resultH_def; drop_parser_resultH_def];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (ISPEC `a : B # A pstreamH` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC
    [lift_parser_resultH_def; drop_parser_resultH_def; pstreamH_lift_drop]);;

export_thm parser_resultH_lift_drop;;

let parser_functionH_drop_lift = prove
 (`!(p : A -> A pstream -> (B # A pstream) option).
     drop_parser_functionH (lift_parser_functionH p) = p`,
  GEN_TAC THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `a : A` THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `s : A pstream` THEN
  REWRITE_TAC
    [lift_parser_functionH_def; drop_parser_functionH_def;
     pstreamH_drop_lift; parser_resultH_drop_lift]);;

export_thm parser_functionH_drop_lift;;

let parser_functionH_lift_drop = prove
 (`!(p : A -> A pstreamH -> (B # A pstreamH) option).
     lift_parser_functionH (drop_parser_functionH p) = p`,
  GEN_TAC THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `a : A` THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `s : A pstreamH` THEN
  REWRITE_TAC
    [lift_parser_functionH_def; drop_parser_functionH_def;
     pstreamH_lift_drop; parser_resultH_lift_drop]);;

export_thm parser_functionH_lift_drop;;
***)

(***
let parserH_mk_dest = prove
 (`!(p : (A,B) parserH).
     mk_parserH (dest_parserH p) = p`,
  HASKELL_TAC [] THEN
  REWRITE_TAC [o_rule map_range_o
);;

export_thm parserH_mk_dest;;
***)

(***
let dest_parserH_inj = prove
 (`!(p : (A,B) parserH) q.
     dest_parserH p = dest_parserH q ==> p = q`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM parserH_mk_dest] THEN
  ASM_REWRITE_TAC []);;

export_thm dest_parserH_inj;;
***)

(* ------------------------------------------------------------------------- *)
(* Source.                                                                   *)
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

(***
let () = export_haskell_thm parserH_mk_dest;;
***)

(***
let () = (export_haskell_thm o prove)
 (`(!(p : (A,B) parserH). parseH p ErrorPstreamH = NONE) /\
   (!(p : (A,B) parserH). parseH p EofPstreamH = NONE) /\
   (!(p : (A,B) parserH) a s.
      parseH p (ConsPstreamH a s) = dest_parserH p a s)`,
  REWRITE_TAC
    [parseH_def; ErrorPstreamH_def; EofPstreamH_def; ConsPstreamH_def;
     pstreamH_drop_lift; parse_def; lift_parser_resultH_def; dest_parserH_def;
     lift_parser_functionH_def]);;

let () = (export_haskell_thm o prove)
 (`!a s. parser_noneH a s = (NONE : (B # A pstreamH) option)`,
  REWRITE_TAC
    [parser_noneH_def; lift_parser_functionH_def; parser_none_def;
     lift_parser_resultH_def]);;

let () = (export_haskell_thm o prove)
 (`(parse_noneH : (A,B) parserH) = mk_parserH parser_noneH`,
  REWRITE_TAC
    [parse_noneH_def; parse_none_def; mk_parserH_def; parser_noneH_def;
     parser_functionH_drop_lift]);;

let () = (export_haskell_thm o prove)
 (`!(a : A) s. parser_allH a s = SOME (a,s)`,
  REWRITE_TAC
    [parser_allH_def; lift_parser_functionH_def; parser_all_def;
     lift_parser_resultH_def; pstreamH_lift_drop]);;

let () = (export_haskell_thm o prove)
 (`(parse_allH : (A,A) parserH) = mk_parserH parser_allH`,
  REWRITE_TAC
    [parse_allH_def; parse_all_def; mk_parserH_def; parser_allH_def;
     parser_functionH_drop_lift]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C option) (p : (A,B) parserH) a s.
     parser_partial_mapH f p a s =
     case_option
       NONE
       (\ (b,s'). case_option NONE (\c. SOME (c,s')) (f b))
       (dest_parserH p a s)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC
    [parser_partial_mapH_def; lift_parser_functionH_def; dest_parserH_def;
     parser_partial_map_def] THEN
  MP_TAC (ISPECL [`drop_parserH (p : (A,B) parserH)`; `a : A`;
                  `drop_pstreamH s : A pstream`] dest_parser_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def] THEN
  MP_TAC (ISPEC `(f : B -> C option) b` option_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C option) (p : (A,B) parserH).
     parse_partial_mapH f p = mk_parserH (parser_partial_mapH f p)`,
  REWRITE_TAC
    [parse_partial_mapH_def; parser_partial_mapH_def; mk_parserH_def;
     parse_partial_map_def; parser_functionH_drop_lift]);;

let () = (export_haskell_thm o prove)
 (`!(f : B -> C) (p : (A,B) parserH).
     parse_mapH f p = parse_partial_mapH (\b. SOME (f b)) p`,
  REWRITE_TAC
    [parse_mapH_def; parse_partial_mapH_def; parse_map_def]);;

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
  REWRITE_TAC
    [parser_pairH_def; lift_parser_functionH_def; dest_parserH_def;
     parser_pair_def] THEN
  MP_TAC (ISPECL [`drop_parserH (pb : (A,B) parserH)`; `a : A`;
                  `drop_pstreamH s : A pstream`] dest_parser_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def] THEN
  REWRITE_TAC [parseH_def; pstreamH_drop_lift] THEN
  MP_TAC (ISPECL [`drop_parserH (pc : (A,C) parserH)`;
                  `s' : A pstream`] parse_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def]);;

let () = (export_haskell_thm o prove)
 (`!(pb : (A,B) parserH) (pc : (A,C) parserH).
     parse_pairH pb pc = mk_parserH (parser_pairH pb pc)`,
  REWRITE_TAC
    [parse_pairH_def; parser_pairH_def; mk_parserH_def;
     parse_pair_def; parser_functionH_drop_lift]);;

let () = (export_haskell_thm o prove)
 (`!(f : A -> B option).
     parse_optionH f = parse_partial_mapH f parse_allH`,
  REWRITE_TAC
    [parse_optionH_def; parse_partial_mapH_def; parse_allH_def;
     parse_option_def; parserH_drop_lift]);;

let () = (export_haskell_thm o prove)
 (`!(p : A -> bool).
     parse_someH p = parse_optionH (\a. if p a then SOME a else NONE)`,
  REWRITE_TAC
    [parse_someH_def; parse_optionH_def; parse_some_def]);;

let () = (export_haskell_thm o prove)
 (`!(p : A -> bool).
     parse_someH p = parse_optionH (\a. if p a then SOME a else NONE)`,
  REWRITE_TAC
    [parse_someH_def; parse_optionH_def; parse_some_def]);;

let () = (export_haskell_thm o prove)
 (`(!(p : (A,B) parserH). parse_pstreamH p ErrorPstreamH = ErrorPstreamH) /\
   (!(p : (A,B) parserH). parse_pstreamH p EofPstreamH = EofPstreamH) /\
   (!(p : (A,B) parserH) a s.
      parse_pstreamH p (ConsPstreamH a s) =
      case_option
        ErrorPstreamH
        (\ (b,s'). ConsPstreamH b (parse_pstreamH p s'))
        (dest_parserH p a s))`,
  REWRITE_TAC
    [parse_pstreamH_def; ErrorPstreamH_def; EofPstreamH_def; ConsPstreamH_def;
     pstreamH_drop_lift; parse_pstream_def; dest_parserH_def;
     lift_parser_functionH_def] THEN
  REPEAT GEN_TAC THEN
  MP_TAC (ISPECL [`drop_parserH (p : (A,B) parserH)`; `a : A`;
                  `drop_pstreamH s : A pstream`] dest_parser_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def; pstreamH_drop_lift]);;

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
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
  REWRITE_TAC
    [equal_listH; equal_optionH;
     pstream_to_listH_def; list_to_pstreamH_def; pstreamH_drop_lift;
     list_to_pstream_to_list]);;

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
  REWRITE_TAC
    [length_pstreamH_def; append_pstreamH_def; pstreamH_drop_lift;
     append_pstream_length; lengthH_def]);;

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
  REWRITE_TAC
    [equal_listH; equal_optionH; pstream_to_listH_def;
     append_pstreamH_def; pstreamH_drop_lift] THEN
  MATCH_ACCEPT_TAC pstream_to_list_append);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (l,r') = rdecode_listH rdecode_fibH r in
     length_pstreamH (list_to_pstreamH l) = LENGTH l`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_listH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `l : num list`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC
    [length_pstreamH_def; list_to_pstreamH_def; pstreamH_drop_lift] THEN
  MATCH_ACCEPT_TAC list_to_pstream_length);;

let () = (export_haskell_thm o prove)
 (`!r.
     let (s,r') = rdecode_pstreamH rdecode_fibH r in
     case_option T (\l. LENGTH l = length_pstreamH s) (pstream_to_listH s)`,
  GEN_TAC THEN
  PAIR_CASES_TAC `rdecode_pstreamH rdecode_fibH r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `s : num pstreamH`
      (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  REWRITE_TAC
    [length_pstreamH_def; pstream_to_listH_def; pstreamH_drop_lift] THEN
  MATCH_ACCEPT_TAC pstream_to_list_length);;
***)

(* Parsers *)

logfile_end ();;

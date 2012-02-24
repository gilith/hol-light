(* ========================================================================= *)
(* SIMPLE STREAM PARSERS IN OPENTHEORY HASKELL                               *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of Haskell parsers and streams.                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-def";;

(* Streams *)

let (streamH_lift_drop,streamH_drop_lift) =
  let exists = prove (`?(s : A stream). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "streamH" ("lift_streamH","drop_streamH") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm streamH_lift_drop;;
export_thm streamH_drop_lift;;

let streamH_tybij = CONJ streamH_lift_drop streamH_drop_lift;;

let ErrorH_def = new_definition
  `(ErrorH : A streamH) = lift_streamH Error`;;

export_thm ErrorH_def;;

let EofH_def = new_definition
  `(EofH : A streamH) = lift_streamH Eof`;;

export_thm EofH_def;;

let StreamH_def = new_definition
  `!(a : A) s. StreamH a s = lift_streamH (Stream a (drop_streamH s))`;;

export_thm StreamH_def;;

let case_streamH_def = new_definition
  `!(e : B) b f (s : A streamH).
     case_streamH e b f s =
     case_stream e b (\a t. f a (lift_streamH t)) (drop_streamH s)`;;

export_thm case_streamH_def;;

let length_streamH_def = new_definition
  `!(s : A streamH). length_streamH s = length_stream (drop_streamH s)`;;

export_thm length_streamH_def;;

let stream_to_listH_def = new_definition
  `!(s : A streamH). stream_to_listH s = stream_to_list (drop_streamH s)`;;

export_thm stream_to_listH_def;;

let append_streamH_def = new_definition
  `!l (s : A streamH).
     append_streamH l s = lift_streamH (append_stream l (drop_streamH s))`;;

export_thm append_streamH_def;;

let list_to_streamH_def = new_definition
  `!(l : A list). list_to_streamH l = lift_streamH (list_to_stream l)`;;

export_thm list_to_streamH_def;;

(* Parsers *)

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
    `(lift_parser_resultH : (B # A stream) option ->  (B # A streamH) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, lift_streamH s'))` in
  let th_none = prove
    (`lift_parser_resultH (NONE : (B # A stream) option) =
      (NONE : (B # A streamH) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A stream).
         lift_parser_resultH (SOME (b,s)) = SOME (b, lift_streamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm lift_parser_resultH_none;;
export_thm lift_parser_resultH_some;;

let lift_parser_resultH_def =
    CONJ lift_parser_resultH_none lift_parser_resultH_some;;

let (drop_parser_resultH_none,drop_parser_resultH_some) =
  let def = new_definition
    `(drop_parser_resultH : (B # A streamH) option ->  (B # A stream) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, drop_streamH s'))` in
  let th_none = prove
    (`drop_parser_resultH (NONE : (B # A streamH) option) =
      (NONE : (B # A stream) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A streamH).
         drop_parser_resultH (SOME (b,s)) = SOME (b, drop_streamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm drop_parser_resultH_none;;
export_thm drop_parser_resultH_some;;

let drop_parser_resultH_def =
    CONJ drop_parser_resultH_none drop_parser_resultH_some;;

let lift_parser_functionH_def = new_definition
  `!(p : A -> A stream -> (B # A stream) option).
     lift_parser_functionH p =
     \a s. lift_parser_resultH (p a (drop_streamH s))`;;

export_thm lift_parser_functionH_def;;

let drop_parser_functionH_def = new_definition
  `!(p : A -> A streamH -> (B # A streamH) option).
     drop_parser_functionH p =
     \a s. drop_parser_resultH (p a (lift_streamH s))`;;

export_thm drop_parser_functionH_def;;

let mk_parserH_def = new_definition
  `!(p : A -> A streamH -> (B # A streamH) option).
     mk_parserH p = lift_parserH (mk_parser (drop_parser_functionH p))`;;

export_thm mk_parserH_def;;

let dest_parserH_def = new_definition
  `!(p : (A,B) parserH).
     dest_parserH p = lift_parser_functionH (dest_parser (drop_parserH p))`;;

export_thm dest_parserH_def;;

let parseH_def = new_definition
  `!(p : (A,B) parserH) s.
     parseH p s =
     lift_parser_resultH (parse (drop_parserH p) (drop_streamH s))`;;

export_thm parseH_def;;

let parser_noneH_def = new_definition
  `(parser_noneH : A -> A streamH -> (B # A streamH) option) =
   lift_parser_functionH parser_none`;;

export_thm parser_noneH_def;;

let parse_noneH_def = new_definition
  `(parse_noneH : (A,B) parserH) = lift_parserH parse_none`;;

export_thm parse_noneH_def;;

let parser_allH_def = new_definition
  `(parser_allH : A -> A streamH -> (A # A streamH) option) =
   lift_parser_functionH parser_all`;;

export_thm parser_allH_def;;

let parse_allH_def = new_definition
  `(parse_allH : (A,A) parserH) = lift_parserH parse_all`;;

export_thm parse_allH_def;;

let parser_partial_mapH_def = new_definition
  `!(f : B -> C option) (p : (A,B) parserH).
     parser_partial_mapH f p =
     lift_parser_functionH (parser_partial_map f (drop_parserH p))`;;

export_thm parser_partial_mapH_def;;

let parse_partial_mapH_def = new_definition
  `!(f : B -> C option) (p : (A,B) parserH).
     parse_partial_mapH f p =
     lift_parserH (parse_partial_map f (drop_parserH p))`;;

export_thm parse_partial_mapH_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of Haskell parsers and streams.                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-thm";;

(* Parsers *)

let parser_resultH_drop_lift = prove
 (`!(r : (B # A stream) option).
     drop_parser_resultH (lift_parser_resultH r) = r`,
  GEN_TAC THEN
  MP_TAC (ISPEC `r : (B # A stream) option` option_cases) THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [lift_parser_resultH_def; drop_parser_resultH_def];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (ISPEC `a : B # A stream` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC
    [lift_parser_resultH_def; drop_parser_resultH_def; streamH_drop_lift]);;

export_thm parser_resultH_drop_lift;;

let parser_resultH_lift_drop = prove
 (`!(r : (B # A streamH) option).
     lift_parser_resultH (drop_parser_resultH r) = r`,
  GEN_TAC THEN
  MP_TAC (ISPEC `r : (B # A streamH) option` option_cases) THEN
  STRIP_TAC THENL
  [FIRST_X_ASSUM SUBST_VAR_TAC THEN
   REWRITE_TAC [lift_parser_resultH_def; drop_parser_resultH_def];
   ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  MP_TAC (ISPEC `a : B # A streamH` PAIR_SURJECTIVE) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_VAR_TAC THEN
  REWRITE_TAC
    [lift_parser_resultH_def; drop_parser_resultH_def; streamH_lift_drop]);;

export_thm parser_resultH_lift_drop;;

let parser_functionH_drop_lift = prove
 (`!(p : A -> A stream -> (B # A stream) option).
     drop_parser_functionH (lift_parser_functionH p) = p`,
  GEN_TAC THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `a : A` THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `s : A stream` THEN
  REWRITE_TAC
    [lift_parser_functionH_def; drop_parser_functionH_def;
     streamH_drop_lift; parser_resultH_drop_lift]);;

export_thm parser_functionH_drop_lift;;

let parser_functionH_lift_drop = prove
 (`!(p : A -> A streamH -> (B # A streamH) option).
     lift_parser_functionH (drop_parser_functionH p) = p`,
  GEN_TAC THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `a : A` THEN
  CONV_TAC (REWR_CONV FUN_EQ_THM) THEN
  X_GEN_TAC `s : A streamH` THEN
  REWRITE_TAC
    [lift_parser_functionH_def; drop_parser_functionH_def;
     streamH_lift_drop; parser_resultH_lift_drop]);;

export_thm parser_functionH_lift_drop;;

let parserH_mk_dest = prove
 (`!(p : (A,B) parserH).
     mk_parserH (dest_parserH p) = p`,
  REWRITE_TAC
    [mk_parserH_def; dest_parserH_def; parser_functionH_drop_lift;
     parser_abs_rep; parserH_lift_drop]);;

export_thm parserH_mk_dest;;

let dest_parserH_inj = prove
 (`!(p : (A,B) parserH) q.
     dest_parserH p = dest_parserH q ==> p = q`,
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM parserH_mk_dest] THEN
  ASM_REWRITE_TAC []);;

export_thm dest_parserH_inj;;

(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

(* Streams *)

let () = (export_haskell_thm o prove)
 (`(!e b (f : A -> A streamH -> B). case_streamH e b f ErrorH = e) /\
   (!e b (f : A -> A streamH -> B). case_streamH e b f EofH = b) /\
   (!e b (f : A -> A streamH -> B) a s.
      case_streamH e b f (StreamH a s) = f a s)`,
  REWRITE_TAC
    [case_streamH_def; ErrorH_def; EofH_def; StreamH_def; case_stream_def;
     streamH_tybij]);;

let () = (export_haskell_thm o prove)
 (`length_streamH (ErrorH : A streamH) = 0 /\
   length_streamH (EofH : A streamH) = 0 /\
   (!(a:A) s. length_streamH (StreamH a s) = length_streamH s + 1)`,
  REWRITE_TAC
    [length_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
     length_stream_def; ADD1]);;

let () = (export_haskell_thm o prove)
 (`stream_to_listH (ErrorH : A streamH) = NONE /\
   stream_to_listH (EofH : A streamH) = SOME [] /\
   (!(a : A) s.
      stream_to_listH (StreamH a s) =
      case_option NONE (\l. SOME (CONS a l)) (stream_to_listH s))`,
  REWRITE_TAC
    [stream_to_listH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
     stream_to_list_def]);;

let () = (export_haskell_thm o prove)
 (`(!(s : A streamH). append_streamH [] s = s) /\
   (!(h : A) t s.
      append_streamH (CONS h t) s = StreamH h (append_streamH t s))`,
  REWRITE_TAC
    [append_streamH_def; streamH_tybij; StreamH_def; append_stream_def]);;

let () = (export_haskell_thm o prove)
 (`!(l : A list). list_to_streamH l = append_streamH l EofH`,
  REWRITE_TAC
    [list_to_streamH_def; streamH_tybij; EofH_def; list_to_stream_def;
     append_streamH_def]);;

(* Parsers *)

let () = export_haskell_thm parserH_mk_dest;;

let () = (export_haskell_thm o prove)
 (`(!(p : (A,B) parserH). parseH p ErrorH = NONE) /\
   (!(p : (A,B) parserH). parseH p EofH = NONE) /\
   (!(p : (A,B) parserH) a s. parseH p (StreamH a s) = dest_parserH p a s)`,
  REWRITE_TAC
    [parseH_def; ErrorH_def; EofH_def; StreamH_def; streamH_drop_lift;
     parse_def; lift_parser_resultH_def; dest_parserH_def;
     lift_parser_functionH_def]);;

let () = (export_haskell_thm o prove)
 (`!a s. parser_noneH a s = (NONE : (B # A streamH) option)`,
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
     lift_parser_resultH_def; streamH_lift_drop]);;

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
                  `drop_streamH s : A stream`] dest_parser_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def] THEN
  MP_TAC (ISPEC `(f : B -> C option) b` option_cases) THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  REWRITE_TAC [lift_parser_resultH_def; case_option_def]);;

(***
export_haskell_thm parse_partial_map_def;;

export_haskell_thm parse_map_def;;

export_haskell_thm parser_pair_def;;

export_haskell_thm parse_pair_def;;

export_haskell_thm parse_option_def;;

export_haskell_thm parse_some_def;;

export_haskell_thm (REWRITE_RULE [FORALL_AND_THM] parse_stream_def);;
***)

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-test";;

(* Streams *)

let () = (export_haskell_thm o prove)
 (`!(l : A list) s.
     length_streamH (append_streamH l s) = LENGTH l + length_streamH s`,
  REWRITE_TAC
    [length_streamH_def; append_streamH_def; streamH_drop_lift;
     append_stream_length]);;

(***
export_haskell_thm append_stream_assoc;;

export_haskell_thm list_to_stream_to_list;;

export_haskell_thm stream_to_list_append;;

export_haskell_thm list_to_stream_length;;

export_haskell_thm stream_to_list_length;;

(* Parsers *)
***)

logfile_end ();;

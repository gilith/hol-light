(* ========================================================================= *)
(* SIMPLE STREAM PARSERS IN OPENTHEORY HASKELL                               *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Defining Haskell parsers and streams.                                     *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-def";;

(* Streams *)

let is_streamH_def =
  let def = new_definition
    `!(s : A stream). is_streamH s <=> T` in
  REWRITE_RULE [] def;;

let streamH_exists = prove
  (`?(s : A stream). is_streamH s`,
   EXISTS_TAC `s : A stream` THEN
   REWRITE_TAC [is_streamH_def]);;

let (streamH_abs_rep,streamH_rep_abs) =
  let tybij =
    new_type_definition
      "streamH" ("mk_streamH","dest_streamH") streamH_exists in
  CONJ_PAIR (REWRITE_RULE [is_streamH_def] tybij);;

export_thm streamH_abs_rep;;
export_thm streamH_rep_abs;;

let streamH_tybij = CONJ streamH_abs_rep streamH_rep_abs;;

let ErrorH_def = new_definition
  `(ErrorH : A streamH) = mk_streamH Error`;;

export_thm ErrorH_def;;

let EofH_def = new_definition
  `(EofH : A streamH) = mk_streamH Eof`;;

export_thm EofH_def;;

let StreamH_def = new_definition
  `!(a : A) s. StreamH a s = mk_streamH (Stream a (dest_streamH s))`;;

export_thm StreamH_def;;

let case_streamH_def = new_definition
  `!(e : B) b f (s : A streamH).
     case_streamH e b f s =
     case_stream e b (\a t. f a (mk_streamH t)) (dest_streamH s)`;;

export_thm case_streamH_def;;

let length_streamH_def = new_definition
  `!(s : A streamH). length_streamH s = length_stream (dest_streamH s)`;;

export_thm length_streamH_def;;

let stream_to_listH_def = new_definition
  `!(s : A streamH). stream_to_listH s = stream_to_list (dest_streamH s)`;;

export_thm stream_to_listH_def;;

let append_streamH_def = new_definition
  `!l (s : A streamH).
     append_streamH l s = mk_streamH (append_stream l (dest_streamH s))`;;

export_thm append_streamH_def;;

let list_to_streamH_def = new_definition
  `!(l : A list). list_to_streamH l = mk_streamH (list_to_stream l)`;;

export_thm list_to_streamH_def;;

(* Parsers *)

let is_parserH_def =
  let def = new_definition
    `!(p : (A,B) parser). is_parserH p <=> T` in
  REWRITE_RULE [] def;;

let parserH_exists = prove
  (`?(p : (A,B) parser). is_parserH p`,
   EXISTS_TAC `p : (A,B) parser` THEN
   REWRITE_TAC [is_parserH_def]);;

let (parserH_abs_rep,parserH_rep_abs) =
  let tybij =
    new_type_definition
      "parserH" ("mk_parserH","dest_parserH") parserH_exists in
  CONJ_PAIR (REWRITE_RULE [is_parserH_def] tybij);;

export_thm parserH_abs_rep;;
export_thm parserH_rep_abs;;

let parserH_tybij = CONJ parserH_abs_rep parserH_rep_abs;;

let (mk_parser_resultH_none,mk_parser_resultH_some) =
  let def = new_definition
    `(mk_parser_resultH : (B # A stream) option ->  (B # A streamH) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, mk_streamH s'))` in
  let th_none = prove
    (`mk_parser_resultH (NONE : (B # A stream) option) =
      (NONE : (B # A streamH) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A stream).
         mk_parser_resultH (SOME (b,s)) = SOME (b, mk_streamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm mk_parser_resultH_none;;
export_thm mk_parser_resultH_some;;

let mk_parser_resultH_def =
    CONJ mk_parser_resultH_none mk_parser_resultH_some;;

let (dest_parser_resultH_none,dest_parser_resultH_some) =
  let def = new_definition
    `(dest_parser_resultH : (B # A streamH) option ->  (B # A stream) option) =
       case_option
         NONE
         (\ (b,s'). SOME (b, dest_streamH s'))` in
  let th_none = prove
    (`dest_parser_resultH (NONE : (B # A streamH) option) =
      (NONE : (B # A stream) option)`,
     REWRITE_TAC [def; case_option_def])
  and th_some = prove
    (`!(b : B) (s : A streamH).
         dest_parser_resultH (SOME (b,s)) = SOME (b, dest_streamH s)`,
     REWRITE_TAC [def; case_option_def]) in
  (th_none,th_some);;

export_thm dest_parser_resultH_none;;
export_thm dest_parser_resultH_some;;

let dest_parser_resultH_def =
    CONJ dest_parser_resultH_none dest_parser_resultH_some;;

let mk_parseH_def = new_definition
  `!(p : A -> A stream -> (B # A stream) option).
     mk_parseH p a s = mk_parser_resultH (p a (dest_streamH s))`;;

export_thm mk_parseH_def;;

let dest_parseH_def = new_definition
  `!(p : A -> A streamH -> (B # A streamH) option).
     dest_parseH p a s = dest_parser_resultH (p a (mk_streamH s))`;;

export_thm dest_parseH_def;;

let abs_parserH_def = new_definition
  `!(p : A -> A streamH -> (B # A streamH) option).
     abs_parserH p = mk_parserH (mk_parser (dest_parseH p))`;;

export_thm abs_parserH_def;;

let rep_parserH_def = new_definition
  `!(p : (A,B) parserH).
     rep_parserH p = mk_parseH (dest_parser (dest_parserH p))`;;

export_thm rep_parserH_def;;

(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

(* Streams *)

let case_streamH_src = prove
 (`(!e b (f : A -> A streamH -> B). case_streamH e b f ErrorH = e) /\
   (!e b (f : A -> A streamH -> B). case_streamH e b f EofH = b) /\
   (!e b (f : A -> A streamH -> B) a s.
      case_streamH e b f (StreamH a s) = f a s)`,
  REWRITE_TAC
    [case_streamH_def; ErrorH_def; EofH_def; StreamH_def; case_stream_def;
     streamH_tybij]);;

export_haskell_thm case_streamH_src;;

let length_streamH_src = prove
 (`length_streamH (ErrorH : A streamH) = 0 /\
   length_streamH (EofH : A streamH) = 0 /\
   (!(a:A) s. length_streamH (StreamH a s) = length_streamH s + 1)`,
  REWRITE_TAC
    [length_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
     length_stream_def; ADD1]);;

export_haskell_thm length_streamH_src;;

let stream_to_listH_src = prove
 (`stream_to_listH (ErrorH : A streamH) = NONE /\
   stream_to_listH (EofH : A streamH) = SOME [] /\
   (!(a : A) s.
      stream_to_listH (StreamH a s) =
      case_option NONE (\l. SOME (CONS a l)) (stream_to_listH s))`,
  REWRITE_TAC
    [stream_to_listH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
     stream_to_list_def]);;

export_haskell_thm stream_to_listH_src;;

let append_streamH_src = prove
 (`(!(s : A streamH). append_streamH [] s = s) /\
   (!(h : A) t s.
      append_streamH (CONS h t) s = StreamH h (append_streamH t s))`,
  REWRITE_TAC
    [append_streamH_def; streamH_tybij; StreamH_def; append_stream_def]);;

export_haskell_thm append_streamH_src;;

let list_to_streamH_src = prove
 (`!(l : A list). list_to_streamH l = append_streamH l EofH`,
  REWRITE_TAC
    [list_to_streamH_def; streamH_tybij; EofH_def; list_to_stream_def;
     append_streamH_def]);;

export_haskell_thm list_to_streamH_src;;

(* Parsers *)

(***
export_haskell_thm (CONJUNCT1 parser_tybij);;

export_haskell_thm parse_def;;

export_haskell_thm parser_none_def;;

export_haskell_thm parse_none_def;;

export_haskell_thm parser_all_def;;

export_haskell_thm parse_all_def;;

export_haskell_thm parser_partial_map_def;;

export_haskell_thm parse_partial_map_def;;

export_haskell_thm parse_map_def;;

export_haskell_thm parser_pair_def;;

export_haskell_thm parse_pair_def;;

export_haskell_thm parse_option_def;;

export_haskell_thm parse_some_def;;

export_haskell_thm (REWRITE_RULE [FORALL_AND_THM] parse_stream_def);;

(* ------------------------------------------------------------------------- *)
(* Testing.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-test";;

(* Streams *)

export_haskell_thm append_stream_assoc;;

export_haskell_thm list_to_stream_to_list;;

export_haskell_thm stream_to_list_append;;

export_haskell_thm append_stream_length;;

export_haskell_thm list_to_stream_length;;

export_haskell_thm stream_to_list_length;;

(* Parsers *)
***)

logfile_end ();;

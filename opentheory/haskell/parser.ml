(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-def";;

let is_streamH_def = new_definition
  `!s. is_streamH (s : A stream) = T`;;

let streamH_exists = prove
  (`?s. is_streamH (s : A stream)`,
   REWRITE_TAC [is_streamH_def]);;

let streamH_tybij =
    REWRITE_RULE [is_streamH_def]
    (new_type_definition "streamH"
       ("mk_streamH","dest_streamH") streamH_exists);;

export_thm streamH_tybij;;

let ErrorH_def = new_definition
  `ErrorH = mk_streamH (Error : A stream)`;;

export_thm ErrorH_def;;

let EofH_def = new_definition
  `EofH = mk_streamH (Eof : A stream)`;;

export_thm EofH_def;;

let StreamH_def = new_definition
  `!a s. StreamH a s = mk_streamH (Stream (a : A) (dest_streamH s))`;;

export_thm StreamH_def;;

let case_streamH_def = new_definition
  `!e b f s.
     case_streamH (e : B) b f (s : A streamH) =
     case_stream e b (\h t. f h (mk_streamH t)) (dest_streamH s)`;;

export_thm case_streamH_def;;

let length_streamH_def = new_definition
  `!s. length_streamH (s : A streamH) = length_stream (dest_streamH s)`;;

export_thm length_streamH_def;;

logfile "haskell-parser-export";;

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

let case_streamH = prove
  (`(!e b f. case_streamH e b f ErrorH = (e:B)) /\
    (!e b f. case_streamH e b f EofH = b) /\
    (!e b f a s. case_streamH e b f (StreamH a s) = f (a:A) s)`,
   REWRITE_TAC
     [case_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
      case_stream_def]);;

export_thm case_streamH;;

let length_streamH = prove
  (`(length_streamH (ErrorH : A streamH) = 0) /\
    (length_streamH (EofH : A streamH) = 0) /\
    (!h t. length_streamH (StreamH (h : A) t) = length_streamH t + 1)`,
   REWRITE_TAC
     [length_streamH_def; ErrorH_def; EofH_def; StreamH_def; streamH_tybij;
      length_stream_def; ADD1]);;

export_thm length_streamH;;

(***
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
***)

logfile "haskell-parser-thm";;

logfile_end ();;

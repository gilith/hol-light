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

let ErrorH_def = new_definition
  `ErrorH = mk_streamH (Error : A stream)`;;

let EofH_def = new_definition
  `EofH = mk_streamH (Eof : A stream)`;;

let StreamH_def = new_definition
  `!a s. StreamH a s = mk_streamH (Stream (a : A) (dest_streamH s))`;;

let streamH_induct = prove
  (`!P.
      P ErrorH /\ P EofH /\ (!a s. P s ==> P (StreamH (a : A) s)) ==>
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

export_thm streamH_induct;;

let streamH_recursion = prove
  (`!f0 f1 f2. ?fn.
      fn ErrorH = (f0 : B) /\
      fn EofH = f1 /\
      (!a s. fn (StreamH (a : A) s) = f2 a s (fn s))`,
   REPEAT GEN_TAC THEN
   MP_TAC
     (ISPECL
        [`f0 : B`; `f1 : B`;
         `\a s x. (f2 : A -> A streamH -> B -> B) a (mk_streamH s) x`]
        stream_recursion) THEN
   STRIP_TAC THEN
   EXISTS_TAC `\s. (fn : A stream -> B) (dest_streamH s)` THEN
   ASM_REWRITE_TAC [ErrorH_def; EofH_def; StreamH_def; streamH_tybij]);;

export_thm streamH_recursion;;

logfile "haskell-parser-thm";;

logfile_end ();;

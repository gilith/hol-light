(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

(* Streams *)

export_haskell_thm
  (CONJ stream_induct (CONJ stream_recursion case_stream_def));;

export_haskell_thm length_stream_def;;

export_haskell_thm stream_to_list_def;;

export_haskell_thm append_stream_def;;

export_haskell_thm list_to_stream_def;;

(* Parsers *)

export_haskell_thm parser_tybij;;

export_haskell_thm parse_def;;

logfile "haskell-parser-test";;

(* Streams *)

export_haskell_thm append_stream_assoc;;

export_haskell_thm list_to_stream_to_list;;

export_haskell_thm stream_to_list_append;;

export_haskell_thm append_stream_length;;

export_haskell_thm list_to_stream_length;;

export_haskell_thm stream_to_list_length;;

(* Parsers *)

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* A type of Haskell parsers.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-parser-src";;

(* Streams *)

export_haskell_thm case_stream_def;;

export_haskell_thm length_stream_def;;

export_haskell_thm stream_to_list_def;;

export_haskell_thm append_stream_def;;

export_haskell_thm list_to_stream_def;;

(* Parsers *)

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

logfile_end ();;

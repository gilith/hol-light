(* ------------------------------------------------------------------------- *)
(* Streams.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "stream-def";;

let (stream_abs_rep,stream_rep_abs) =
  let exists = prove (`?(s : num -> A). T`, REWRITE_TAC []) in
  let tybij =
    new_type_definition
      "stream" ("mk_stream","dest_stream") exists in
  CONJ_PAIR (REWRITE_RULE [] tybij);;

export_thm stream_abs_rep;;
export_thm stream_rep_abs;;

let stream_tybij = CONJ stream_abs_rep stream_rep_abs;;

logfile_end ();;

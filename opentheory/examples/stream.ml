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

let shd_def = new_definition
  `!s : A stream. shd s = dest_stream s 0`;;

export_thm shd_def;;

let stl_def = new_definition
  `!s : A stream. stl s = mk_stream (\n. dest_stream s (SUC n))`;;

export_thm stl_def;;

logfile_end ();;

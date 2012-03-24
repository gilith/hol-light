(* ------------------------------------------------------------------------- *)
(* Streams.                                                                  *)
(* ------------------------------------------------------------------------- *)

logfile "stream-def";;

let (snth_stream,stream_snth) =
  let exists = prove (`?(s : num -> A). T`, REWRITE_TAC []) in
  let tybij =
      REWRITE_RULE []
        (new_type_definition "stream" ("stream","snth") exists) in
  let th1 = prove
    (`!(s : A stream). stream (snth s) = s`, REWRITE_TAC [tybij])
  and th2 = prove
    (`!(f : num -> A). snth (stream f) = f`, REWRITE_TAC [tybij]) in
  (th1,th2);;

export_thm snth_stream;;
export_thm stream_snth;;

let shd_def = new_definition
  `!s : A stream. shd s = snth s 0`;;

export_thm shd_def;;

let sdrop_def = new_definition
  `!(s : A stream) n. sdrop s n = stream (\m. snth s (m + n))`;;

export_thm sdrop_def;;

let stl_def = new_definition
  `!s : A stream. stl s = sdrop s 1`;;

export_thm stl_def;;

let scons_def = new_definition
  `!h (t : A stream).
     scons h t = stream (\n. if n = 0 then h else snth t (n - 1))`;;

export_thm scons_def;;

let ssplit_def = new_definition
  `!s : A stream.
     ssplit s =
     (stream (\n. snth s (2 * n)),
      stream (\n. snth s (2 * n + 1)))`;;

export_thm ssplit_def;;

logfile_end ();;

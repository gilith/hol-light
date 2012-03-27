(* ------------------------------------------------------------------------- *)
(* Probability.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "probability-def";;

let (mk_dest_random,dest_mk_random) =
  let exists = prove (`?(s : bool stream). T`, REWRITE_TAC []) in
  let tybij =
      REWRITE_RULE []
        (new_type_definition "random" ("mk_random","dest_random") exists) in
  let th1 = prove
    (`!s. dest_random (mk_random s) = s`, REWRITE_TAC [tybij])
  and th2 = prove
    (`!r. mk_random (dest_random r) = r`, REWRITE_TAC [tybij]) in
  (th1,th2);;

export_thm mk_dest_random;;
export_thm dest_mk_random;;

let rbit_def = new_definition
  `!r. rbit r = (shd (dest_random r), mk_random (stl (dest_random r)))`;;

export_thm rbit_def;;

let rsplit_def = new_definition
  `!r.
     rsplit r =
     let (s1,s2) = ssplit (dest_random r) in
     (mk_random s1, mk_random s2)`;;

export_thm rsplit_def;;

logfile_end ();;

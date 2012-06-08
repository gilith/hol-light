(* ------------------------------------------------------------------------- *)
(* Probability.                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "probability-def";;

let (mk_dest_random,dest_mk_random) =
  CONJ_PAIR (define_newtype ("r","random") ("s",`:bool stream`));;

export_thm mk_dest_random;;
export_thm dest_mk_random;;

let random_tybij = CONJ mk_dest_random dest_mk_random;;

let rbit_def = new_definition
  `!r. rbit r = (shd (dest_random r), mk_random (stl (dest_random r)))`;;

export_thm rbit_def;;

let rsplit_def = new_definition
  `!r.
     rsplit r =
     let (s1,s2) = ssplit (dest_random r) in
     (mk_random s1, mk_random s2)`;;

export_thm rsplit_def;;

let (rbits_zero,rbits_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!r. rbits 0 r = ([],r)) /\
     (!r n.
        rbits (SUC n) r =
        let (b,r') = rbit r in
        let (l,r'') = rbits n r' in
        (CONS b l, r''))` in
  CONJ_PAIR def;;

export_thm rbits_zero;;
export_thm rbits_suc;;

let rbits_def = CONJ rbits_zero rbits_suc;;

logfile_end ();;

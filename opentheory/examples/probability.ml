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

let rdecode_list_dest_exists = prove
 (`!d. ?dest. !(l : A list) r.
     dest l r =
       let (b,r') = rbit r in
       if b then l else
       let (x,r'') = d r' in
       dest (CONS x l) r''`,
  GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ ((l : A list), (r : random)).
          let (b,r') = rbit r in
          ~b`;
       `\ ((l : A list), (r : random)).
          let (b,r') = rbit r in
          let (x,r'') = (d : random -> A # random) r' in
          (CONS x l, r'')`;
       `\ ((l : A list), (r : random)).
          l`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `dest : A list # random -> A list`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
    `\ (l : A list) (r : random).
       ((dest (l,r)) : A list)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `rbit r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool` (X_CHOOSE_THEN `r' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `b : bool` THENL
  [REWRITE_TAC [];
   REWRITE_TAC [] THEN
   PAIR_CASES_TAC `(d : random -> A # random) r'` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `x : A` (X_CHOOSE_THEN `r'' : random` SUBST1_TAC)) THEN
   REWRITE_TAC []]);;

let rdecode_list_dest_def =
  new_specification ["rdecode_list_dest"]
    (ONCE_REWRITE_RULE [SKOLEM_THM] rdecode_list_dest_exists);;

export_thm rdecode_list_dest_def;;

let rdecode_list_def = new_definition
  `!d r.
     rdecode_list (d : random -> A # random) r =
     let (r1,r2) = rsplit r in
     (rdecode_list_dest d [] r1, r2)`;;

export_thm rdecode_list_def;;

let (rdecode_uniform_dest_zero,rdecode_uniform_dest_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!r. rdecode_uniform_dest 0 r = (0,r)) /\
     (!r w.
        rdecode_uniform_dest (SUC w) r =
        let (b,r') = rbit r in
        let (m,r'') = rdecode_uniform_dest w r' in
        ((if b then 2 * m + 1 else 2 * m), r''))` in
  CONJ_PAIR def;;

export_thm rdecode_uniform_dest_zero;;
export_thm rdecode_uniform_dest_suc;;

let rdecode_uniform_dest_def = CONJ rdecode_uniform_dest_zero rbits_suc;;

let rdecode_uniform_loop_exists = prove
 (`!n w. ?loop. !r.
     loop r =
     let (m,r') = rdecode_uniform_dest w r in
     if m < n then m else
     loop r'`,
  REPEAT GEN_TAC THEN
  MP_TAC
   (ISPECL
      [`\ (r : random).
          let (m,r') = rdecode_uniform_dest w r in
          ~(m < n)`;
       `\ (r : random).
          let (m,r') = rdecode_uniform_dest w r in
          r'`;
       `\ (r : random).
          let (m,r') = rdecode_uniform_dest w r in
          m`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `loop : random -> num`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `loop : random -> num` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `rdecode_uniform_dest w r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `m : num` (X_CHOOSE_THEN `r' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `m < (n : num)` THEN
  REWRITE_TAC []);;

let rdecode_uniform_loop_def =
  new_specification ["rdecode_uniform_loop"]
    (ONCE_REWRITE_RULE [SKOLEM_THM]
      (ONCE_REWRITE_RULE [SKOLEM_THM]
        rdecode_uniform_loop_exists));;

export_thm rdecode_uniform_loop_def;;

(***
let rdecode_uniform_def = new_definition
  `!n r.
     rdecode_uniform n r =
     if n = 1 then (0,r) else
     let w = log 2 n + 1 in
     let (r1,r2) = rsplit r in
     (rdecode_uniform_loop n w r1 MOD n, r2)`;;

export_thm rdecode_uniform_def;;
***)

logfile_end ();;

(* ========================================================================= *)
(* PROBABILITY                                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Interpretations for probability.                                          *)
(* ------------------------------------------------------------------------- *)

extend_the_interpretation "opentheory/theories/probability/probability.int";;

(* ------------------------------------------------------------------------- *)
(* Definition of probability.                                                *)
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

let (rdecode_vector_zero,rdecode_vector_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(d : random -> A # random) r. rdecode_vector d 0 r = ([],r)) /\
     (!d r n.
        rdecode_vector d (SUC n) r =
        let (h,r') = d r in
        let (t,r'') = rdecode_vector d n r' in
        (CONS h t, r''))` in
  CONJ_PAIR def;;

export_thm rdecode_vector_zero;;
export_thm rdecode_vector_suc;;

let rdecode_vector_def = CONJ rdecode_vector_zero rdecode_vector_suc;;

let rbits_def = new_definition
  `rbits = rdecode_vector rbit`;;

export_thm rbits_def;;

let rdecode_geometric_loop_exists = prove
 (`?loop. !n r.
     loop n r =
       let (b,r') = rbit r in
       if b then n else
       loop (SUC n) r'`,
  MP_TAC
   (ISPECL
      [`\ ((n : num), (r : random)).
          let (b,r') = rbit r in
          ~b`;
       `\ ((n : num), (r : random)).
          let (b,r') = rbit r in
          (SUC n, r')`;
       `\ ((n : num), (r : random)).
          n`] WF_REC_TAIL) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `loop : num # random -> num`
     STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
    `\ (n : num) (r : random).
       ((loop (n,r)) : num)` THEN
  REPEAT GEN_TAC THEN
  REWRITE_TAC [] THEN
  FIRST_X_ASSUM (fun th -> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  PAIR_CASES_TAC `rbit r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `b : bool` (X_CHOOSE_THEN `r' : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `b : bool` THEN
  REWRITE_TAC []);;

let rdecode_geometric_loop_def =
  new_specification ["rdecode_geometric_loop"]
    rdecode_geometric_loop_exists;;

export_thm rdecode_geometric_loop_def;;

let rdecode_geometric_def = new_definition
  `!r.
     rdecode_geometric r =
     let (r1,r2) = rsplit r in
     (rdecode_geometric_loop 0 r1, r2)`;;

export_thm rdecode_geometric_def;;

let rdecode_list_def = new_definition
  `!d r.
     rdecode_list (d : random -> A # random) r =
     let (n,r') = rdecode_geometric r in
     rdecode_vector d n r'`;;

export_thm rdecode_list_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of probability.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "probability-thm";;

let length_rdecode_vector = prove
 (`!(d : random -> A # random) n r. LENGTH (FST (rdecode_vector d n r)) = n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [rdecode_vector_def; LENGTH];
   GEN_TAC THEN
   PAIR_CASES_TAC `(d : random -> A # random) r` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `h : A`
       (X_CHOOSE_THEN `r' : random` STRIP_ASSUME_TAC)) THEN
   PAIR_CASES_TAC `rdecode_vector (d : random -> A # random) n r'` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `t : A list`
       (X_CHOOSE_THEN `r'' : random` STRIP_ASSUME_TAC)) THEN
   FIRST_X_ASSUM (MP_TAC o SPEC `r' : random`) THEN
   ASM_REWRITE_TAC
     [rdecode_vector_def; LENGTH; LET_DEF; LET_END_DEF; SUC_INJ]]);;

export_thm length_rdecode_vector;;

let length_rbits = prove
 (`!n r. LENGTH (FST (rbits n r)) = n`,
  REWRITE_TAC [rbits_def; length_rdecode_vector]);;

export_thm length_rbits;;

logfile_end ();;

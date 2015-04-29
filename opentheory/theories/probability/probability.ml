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

let random_bit_def = new_definition
  `!r. random_bit r = shd (dest_random r)`;;

export_thm random_bit_def;;

let split_random_def = new_definition
  `!r.
     split_random r =
     let (s1,s2) = ssplit (dest_random r) in
     (mk_random s1, mk_random s2)`;;

export_thm split_random_def;;

let (random_vector_zero,random_vector_suc) =
  let def = new_recursive_definition num_RECURSION
    `(!(f : random -> A) r. random_vector f 0 r = []) /\
     (!f r n.
        random_vector f (SUC n) r =
        let (r1,r2) = split_random r in
        CONS (f r1) (random_vector f n r2))` in
  CONJ_PAIR def;;

export_thm random_vector_zero;;
export_thm random_vector_suc;;

let random_vector_def = CONJ random_vector_zero random_vector_suc;;

let random_bits_def = new_definition
  `random_bits = random_vector random_bit`;;

export_thm random_bits_def;;

let random_geometric_loop_exists = prove
 (`?loop. !n r.
     loop n r =
       let (r1,r2) = split_random r in
       if random_bit r1 then n else
       loop (SUC n) r2`,
  MP_TAC
   (ISPECL
      [`\ ((n : num), (r : random)).
          let (r1,r2) = split_random r in
          ~random_bit r1`;
       `\ ((n : num), (r : random)).
          let (r1,r2) = split_random r in
          (SUC n, r2)`;
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
  PAIR_CASES_TAC `split_random r` THEN
  DISCH_THEN
    (X_CHOOSE_THEN `r1 : random` (X_CHOOSE_THEN `r2 : random` SUBST1_TAC)) THEN
  REWRITE_TAC [] THEN
  BOOL_CASES_TAC `random_bit r1` THEN
  REWRITE_TAC []);;

let random_geometric_loop_def =
  new_specification ["random_geometric_loop"]
    random_geometric_loop_exists;;

export_thm random_geometric_loop_def;;

let random_geometric_def = new_definition
  `random_geometric = random_geometric_loop 0`;;

export_thm random_geometric_def;;

let random_geometric_list_def = new_definition
  `!f r.
     random_geometric_list (f : random -> A) r =
     let (r1,r2) = split_random r in
     random_vector f (random_geometric r1) r2`;;

export_thm random_geometric_list_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of probability.                                                *)
(* ------------------------------------------------------------------------- *)

logfile "probability-thm";;

let random_bit_surj = prove
 (`!b. ?r. random_bit r = b`,
  GEN_TAC THEN
  EXISTS_TAC `mk_random (sreplicate b)` THEN
  REWRITE_TAC [random_bit_def; random_tybij; shd_def; snth_sreplicate]);;

export_thm random_bit_surj;;

let split_random_surj = prove
 (`!r1 r2. ?r. split_random r = (r1,r2)`,
  REPEAT GEN_TAC THEN
  EXISTS_TAC `mk_random (sinterleave (dest_random r1) (dest_random r2))` THEN
  REWRITE_TAC
    [split_random_def; random_tybij; ssplit_sinterleave; LET_DEF;
     LET_END_DEF]);;

export_thm split_random_surj;;

let length_random_vector = prove
 (`!(f : random -> A) n r. LENGTH (random_vector f n r) = n`,
  GEN_TAC THEN
  INDUCT_TAC THENL
  [REWRITE_TAC [random_vector_def; LENGTH];
   GEN_TAC THEN
   REWRITE_TAC [random_vector_def] THEN
   PAIR_CASES_TAC `split_random r` THEN
   DISCH_THEN
     (X_CHOOSE_THEN `r1 : random`
       (X_CHOOSE_THEN `r2 : random` STRIP_ASSUME_TAC)) THEN
   ASM_REWRITE_TAC [LENGTH; LET_DEF; LET_END_DEF]]);;

export_thm length_random_vector;;

let random_vector_src = prove
 (`!(f : random -> A) n r.
     random_vector f n r =
     if n = 0 then [] else
     let (r1,r2) = split_random r in
     CONS (f r1) (random_vector f (n - 1) r2)`,
  REPEAT GEN_TAC THEN
  MP_TAC (SPEC `n : num` num_CASES) THEN
  DISCH_THEN
    (DISJ_CASES_THEN2
       SUBST_VAR_TAC
       (X_CHOOSE_THEN `m : num` SUBST_VAR_TAC)) THEN
  REWRITE_TAC [random_vector_def; SUC_SUB1; NOT_SUC]);;

export_thm random_vector_src;;

let random_vector_surj = prove
 (`!f n (l : A list). ONTO f /\ LENGTH l = n ==> ?r. random_vector f n r = l`,
  REPEAT STRIP_TAC THEN
  POP_ASSUM (SUBST_VAR_TAC o SYM) THEN
  SPEC_TAC (`l : A list`, `l : A list`) THEN
  LIST_INDUCT_TAC THENL
  [REWRITE_TAC [LENGTH; random_vector_def];
   ALL_TAC] THEN
  REWRITE_TAC [LENGTH; random_vector_def] THEN
  POP_ASSUM (X_CHOOSE_THEN `r2 : random` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM
    (X_CHOOSE_THEN `r1 : random` SUBST_VAR_TAC o
     SPEC `h : A` o
     REWRITE_RULE [ONTO]) THEN
  MP_TAC (SPECL [`r1 : random`; `r2 : random`] split_random_surj) THEN
  DISCH_THEN (X_CHOOSE_THEN `r : random` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r : random` THEN
  ASM_REWRITE_TAC [LET_DEF; LET_END_DEF]);;

export_thm random_vector_surj;;

let length_random_bits = prove
 (`!n r. LENGTH (random_bits n r) = n`,
  REWRITE_TAC [random_bits_def; length_random_vector]);;

export_thm length_random_bits;;

let random_bits_surj = prove
 (`!n l. LENGTH l = n ==> ?r. random_bits n r = l`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC [random_bits_def] THEN
  MATCH_MP_TAC random_vector_surj THEN
  ASM_REWRITE_TAC [ONTO; ONCE_REWRITE_RULE [EQ_SYM_EQ] random_bit_surj]);;

export_thm random_bits_surj;;

let random_geometric_loop_src =
    REWRITE_RULE [ADD1] random_geometric_loop_def;;

export_thm random_geometric_loop_src;;

(* ------------------------------------------------------------------------- *)
(* Haskell source for probability.                                           *)
(* ------------------------------------------------------------------------- *)

logfile "probability-haskell-src";;

export_thm random_vector_src;;  (* Haskell *)
export_thm random_bits_def;;  (* Haskell *)
export_thm random_geometric_loop_src;;  (* Haskell *)
export_thm random_geometric_def;;  (* Haskell *)
export_thm random_geometric_list_def;;  (* Haskell *)

logfile_end ();;

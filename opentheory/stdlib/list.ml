(* ------------------------------------------------------------------------- *)
(* Additions to the standard list theory.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-thm";;

let list_cases = prove_cases_thm list_INDUCT;;

export_thm list_cases;;

logfile "list-case";;

let case_list_def = new_recursive_definition list_RECURSION
  `(!b f. case_list b f [] = (b:B)) /\
   (!b f h t. case_list b f (CONS h t) = f (h:A) t)`;;

export_thm case_list_def;;

logfile "list-dest-thm";;

let NULL_EQ_NIL = prove
 (`!l. NULL (l : A list) <=> l = []`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [NULL; NOT_CONS_NIL]);;

export_thm NULL_EQ_NIL;;

logfile "list-append-thm";;

let NULL_APPEND = prove
 (`!l m. NULL (APPEND (l : A list) m) <=> NULL l /\ NULL m`,
  ASM_REWRITE_TAC [NULL_EQ_NIL; APPEND_EQ_NIL]);;

export_thm NULL_APPEND;;

logfile_end ();;

logfile "list-concat-def";;

let concat_def = new_recursive_definition list_RECURSION
  `(concat [] = ([] : A list)) /\
   (!h t. concat (CONS h t) = APPEND h (concat t))`;;

export_thm concat_def;;

logfile "list-concat-thm";;

let null_concat = prove
  (`!l. NULL (concat l) <=> ALL NULL l`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [concat_def; ALL; NULL; NULL_APPEND]);;

export_thm null_concat;;

logfile "list-interval-def";;

let interval_def = new_recursive_definition num_RECURSION
  `(!m. interval m 0 = []) /\
   (!m n. interval m (SUC n) = CONS m (interval (SUC m) n))`;;

export_thm interval_def;;

logfile "list-interval-thm";;

let length_interval = prove
  (`!m n. LENGTH (interval m n) = n`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   SIMP_TAC [LENGTH; interval_def; SUC_INJ]);;

export_thm length_interval;;

logfile "list-zipwith-def";;

let zipwith_raw_def = new_recursive_definition list_RECURSION
  `(!f l. zipwith f [] l = []) /\
   (!f h t l.
      zipwith f (CONS h t) l =
      CONS (f h (HD l)) (zipwith f t (TL l)))`;;

let zipwith_def = prove
   (`(!f. zipwith (f : A -> B -> C) [] [] = []) /\
     (!f h1 h2 t1 t2.
        zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
        CONS (f h1 h2) (zipwith f t1 t2))`,
    REWRITE_TAC [zipwith_raw_def; HD; TL]);;

export_thm zipwith_def;;

logfile "list-zipwith-thm";;

let length_zipwith = prove
  (`!(f : A -> B -> C) l1 l2 n.
      LENGTH l1 = n /\ LENGTH l2 = n ==> LENGTH (zipwith f l1 l2) = n`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [LENGTH; zipwith_def] THEN
   GEN_TAC THEN
   MP_TAC (SPEC `n:num` num_CASES) THEN
   STRIP_TAC THEN
   ASM_SIMP_TAC [NOT_SUC; SUC_INJ] THEN
   FIRST_ASSUM MATCH_ACCEPT_TAC);;

export_thm length_zipwith;;

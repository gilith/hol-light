(* ------------------------------------------------------------------------- *)
(* Additions to the standard list theory.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "list-thm";;

let list_cases = prove_cases_thm list_INDUCT;;

export_thm list_cases;;

logfile "list-dest-def";;

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

let case_list_id = prove
  (`!(l : A list). case_list [] CONS l = l`,
   GEN_TAC THEN
   MP_TAC (ISPEC `l : A list` list_cases) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [case_list_def]);;

export_thm case_list_id;;

logfile "list-append-thm";;

let NULL_APPEND = prove
 (`!l m. NULL (APPEND (l : A list) m) <=> NULL l /\ NULL m`,
  ASM_REWRITE_TAC [NULL_EQ_NIL; APPEND_EQ_NIL]);;

export_thm NULL_APPEND;;

logfile_end ();;

logfile "list-nth-thm";;

let nth_eq = prove
  (`!l (m : A list).
      LENGTH l = LENGTH m /\
      (!i. i < LENGTH l ==> EL i l = EL i m) ==>
      l = m`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LENGTH_EQ_NIL] THEN
    REPEAT STRIP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; SUC_INJ; CONS_11] THEN
     REPEAT STRIP_TAC THENL
     [FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `0` th)) THEN
      REWRITE_TAC [LT_0; EL; HD];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `SUC i` th)) THEN
      ASM_REWRITE_TAC [LT_SUC; EL; TL]]]]);;

export_thm nth_eq;;

let nth_map = prove
  (`!f l i. i < LENGTH l ==> EL i (MAP (f : A -> B) l) = f (EL i l)`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT];
    REWRITE_TAC [LENGTH; MAP] THEN
    MATCH_MP_TAC num_INDUCTION THEN
    REWRITE_TAC [EL; HD; LT_SUC; TL] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    FIRST_X_ASSUM ACCEPT_TAC]);;

export_thm nth_map;;

logfile "list-replicate-thm";;

let nth_replicate = prove
  (`!n x i. i < n ==> EL i (REPLICATE n (x : A)) = x`,
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT];
    GEN_TAC THEN
    STRIP_TAC THEN
    REPEAT GEN_TAC THEN
    MP_TAC (SPEC `i : num` num_CASES) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [EL; HD; REPLICATE];
     ASM_REWRITE_TAC [EL; TL; REPLICATE; LT_SUC]]]);;

export_thm nth_replicate;;

logfile "list-concat-def";;

let concat_def = new_recursive_definition list_RECURSION
  `(concat [] = ([] : A list)) /\
   (!h t. concat (CONS h t) = APPEND h (concat t))`;;

export_thm concat_def;;

logfile "list-concat-thm";;

let null_concat = prove
  (`!l. NULL (concat l) <=> ALL NULL (l : (A list) list)`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [concat_def; ALL; NULL; NULL_APPEND]);;

export_thm null_concat;;

logfile "list-take-drop-def";;

let take_raw_def = new_recursive_definition num_RECURSION
  `(!l. take 0 (l : A list) = []) /\
   (!n l. take (SUC n) (l : A list) = CONS (HD l) (take n (TL l)))`;;

let take_def = prove
  (`(!l. take 0 (l : A list) = []) /\
    (!n h t. take (SUC n) (CONS h t) = CONS (h : A) (take n t))`,
   REWRITE_TAC [take_raw_def; HD; TL]);;

export_thm take_def;;

let drop_raw_def = new_recursive_definition num_RECURSION
  `(!l. drop 0 (l : A list) = l) /\
   (!n l. drop (SUC n) (l : A list) = drop n (TL l))`;;

let drop_def = prove
  (`(!l. drop 0 (l : A list) = l) /\
    (!n h t. drop (SUC n) (CONS (h : A) t) = drop n t)`,
   REWRITE_TAC [drop_raw_def; TL]);;

export_thm drop_def;;

logfile "list-take-drop-thm";;

let take_drop = prove
  (`!n (l : A list). n <= LENGTH l ==> APPEND (take n l) (drop n l) = l`,
   MATCH_MP_TAC num_INDUCTION THEN
   REWRITE_TAC [LENGTH; take_def; drop_def; SUC_INJ; APPEND] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   GEN_TAC THEN
   MP_TAC (SPEC `l : A list` list_cases) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [LENGTH; LE; NOT_SUC];
    ASM_REWRITE_TAC [LENGTH; take_def; drop_def; APPEND; LE_SUC; CONS_11]]);;

export_thm take_drop;;

let length_take = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (take n l) = n`,
   MATCH_MP_TAC num_INDUCTION THEN
   REWRITE_TAC [LENGTH; take_def] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LE; NOT_SUC];
    ASM_REWRITE_TAC [LENGTH; LE_SUC; take_def; SUC_INJ]]);;

export_thm length_take;;

let length_drop = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (drop n l) = LENGTH l - n`,
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LENGTH; drop_def; SUB];
    GEN_TAC THEN
    STRIP_TAC THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     ASM_REWRITE_TAC [LENGTH; LE_SUC; drop_def; SUB_SUC]]]);;

export_thm length_drop;;

let nth_take = prove
  (`!n l i. n <= LENGTH (l : A list) /\ i < n ==> EL i (take n l) = EL i l`,
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT];
    GEN_TAC THEN
    STRIP_TAC THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     REWRITE_TAC [LENGTH; LE_SUC; take_def] THEN
     GEN_TAC THEN
     MP_TAC (SPEC `i : num` num_CASES) THEN
     STRIP_TAC THENL
     [ASM_REWRITE_TAC [EL; HD];
      ASM_REWRITE_TAC [EL; TL; LT_SUC]]]]);;

export_thm nth_take;;

let nth_drop = prove
  (`!n l i.
       n <= LENGTH (l : A list) /\ i < LENGTH l - n ==>
       EL i (drop n l) = EL (n + i) l`,
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [ADD; drop_def];
    GEN_TAC THEN
    STRIP_TAC THEN
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC; drop_def; SUB_SUC; ADD; EL; TL] THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC]]);;

export_thm nth_drop;;

let take_length = prove
  (`!l. take (LENGTH l) (l : A list) = l`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [LENGTH; take_def]);;

export_thm take_length;;

let drop_length = prove
  (`!l. drop (LENGTH l) (l : A list) = []`,
   LIST_INDUCT_TAC THEN
   ASM_REWRITE_TAC [LENGTH; drop_def]);;

export_thm drop_length;;

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

let nth_interval = prove
  (`!m n i. i < n ==> EL i (interval m n) = m + i`,
   ONCE_REWRITE_TAC [SWAP_FORALL_THM] THEN
   MATCH_MP_TAC num_INDUCTION THEN
   CONJ_TAC THENL
   [REWRITE_TAC [LT];
    ALL_TAC] THEN
   GEN_TAC THEN
   STRIP_TAC THEN
   REWRITE_TAC [interval_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `i : num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [EL; HD; ADD_0];
    ASM_REWRITE_TAC [EL; TL; ADD_SUC; LT_SUC; GSYM (CONJUNCT2 ADD)]]);;

export_thm nth_interval;;

logfile "list-zipwith-def";;

let zipwith_raw_def = new_recursive_definition list_RECURSION
  `(!f l. zipwith (f : A -> B -> C) [] l = []) /\
   (!f h t l.
      zipwith (f : A -> B -> C) (CONS h t) l =
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

(* Conversions for bit blasting *)

let append_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 APPEND) in
    let cons_conv = REWR_CONV (CONJUNCT2 APPEND) in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let length_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 LENGTH) in
    let cons_conv = REWR_CONV (CONJUNCT2 LENGTH) in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv THENC
    NUM_REDUCE_CONV;;

let replicate_conv =
    let zero_conv = REWR_CONV (CONJUNCT1 REPLICATE) in
    let suc_conv = REWR_CONV (CONJUNCT2 REPLICATE) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let el_conv =
    let zero_conv = REWR_CONV (CONJUNCT1 EL) in
    let suc_conv = REWR_CONV (CONJUNCT2 EL) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let take_conv =
    let zero_conv = REWR_CONV (CONJUNCT1 take_def) in
    let suc_conv = REWR_CONV (CONJUNCT2 take_def) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let drop_conv =
    let zero_conv = REWR_CONV (CONJUNCT1 drop_def) in
    let suc_conv = REWR_CONV (CONJUNCT2 drop_def) in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let zipwith_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 zipwith_def) in
    let cons_conv = REWR_CONV (CONJUNCT2 zipwith_def) in
    fun c ->
      let rec rewr_conv tm =
          (nil_conv ORELSEC
           (cons_conv THENC
            RATOR_CONV (RAND_CONV c) THENC
            RAND_CONV rewr_conv)) tm in
      rewr_conv;;

let list_eq_conv =
    let nil_conv = REWR_CONV (EQT_INTRO (ISPEC `[] : A list` EQ_REFL)) in
    let cons_conv = REWR_CONV CONS_11 in
    fun c ->
      let rec rewr_conv tm =
          (nil_conv ORELSEC
           (cons_conv THENC
            RATOR_CONV (RAND_CONV c) THENC
            RAND_CONV rewr_conv THENC
            TRY_CONV and_simp_conv)) tm in
      rewr_conv;;

let list_bit_conv =
    append_conv ORELSEC
    length_conv ORELSEC
    replicate_conv ORELSEC
    el_conv ORELSEC
    take_conv ORELSEC
    drop_conv ORELSEC
    zipwith_conv ALL_CONV ORELSEC
    list_eq_conv ALL_CONV;;

let bit_blast_subterm_conv = list_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;
let bit_blast_tac = CONV_TAC bit_blast_conv;;

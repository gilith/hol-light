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

logfile "list-reverse-thm";;

let LENGTH_REVERSE = prove
 (`!l. LENGTH (REVERSE (l : A list)) = LENGTH l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE; LENGTH_APPEND; LENGTH] THEN
  ONCE_REWRITE_TAC [ADD_SYM] THEN
  REWRITE_TAC [ADD]);;

export_thm LENGTH_REVERSE;;

logfile "list-member-thm";;

let MEM_REVERSE = prove
 (`!l x. MEM (x : A) (REVERSE l) <=> MEM x l`,
  LIST_INDUCT_TAC THEN
  ASM_REWRITE_TAC [REVERSE] THEN
  REWRITE_TAC [MEM_APPEND] THEN
  ONCE_REWRITE_TAC [DISJ_SYM] THEN
  REWRITE_TAC [GSYM MEM_APPEND] THEN
  ASM_REWRITE_TAC [APPEND; MEM]);;

export_thm MEM_REVERSE;;

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
      REWRITE_TAC [LT_0; EL_0];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC [] THEN
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM (fun th -> MP_TAC (SPEC `SUC i` th)) THEN
      ASM_REWRITE_TAC [LT_SUC] THEN
      SUBGOAL_THEN
        `!(a:A) b c d. (a = c) /\ (b = d) ==> ((a = b) ==> (c = d))`
        MATCH_MP_TAC THENL
      [POP_ASSUM_LIST (K ALL_TAC) THEN
       REPEAT STRIP_TAC THEN
       REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
       REFL_TAC;
       CONJ_TAC THENL
       [MATCH_MP_TAC EL_SUC THEN
        ASM_REWRITE_TAC [];
        MATCH_MP_TAC EL_SUC THEN
        FIRST_ASSUM ACCEPT_TAC]]]]]);;

export_thm nth_eq;;

let nth_map = prove
  (`!f l i. i < LENGTH l ==> EL i (MAP (f : A -> B) l) = f (EL i l)`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; LT];
    REWRITE_TAC [LENGTH; MAP] THEN
    INDUCT_TAC THENL
    [REWRITE_TAC [EL_0];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LT_SUC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPEC `i:num`) THEN
     ASM_REWRITE_TAC [] THEN
     SUBGOAL_THEN
       `!(a:B) b c d. (c = a) /\ (d = b) ==> ((a = b) ==> (c = d))`
       MATCH_MP_TAC THENL
     [POP_ASSUM_LIST (K ALL_TAC) THEN
      REPEAT STRIP_TAC THEN
      REPEAT (FIRST_X_ASSUM SUBST_VAR_TAC) THEN
      REFL_TAC;
      CONJ_TAC THENL
      [MATCH_MP_TAC EL_SUC THEN
       ASM_REWRITE_TAC [LENGTH_MAP];
       AP_TERM_TAC THEN
       MATCH_MP_TAC EL_SUC THEN
       FIRST_ASSUM ACCEPT_TAC]]]]);;

export_thm nth_map;;

logfile "list-replicate-thm";;

let nth_replicate = prove
  (`!n x i. i < n ==> EL i (REPLICATE n (x : A)) = x`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    REPEAT GEN_TAC THEN
    MP_TAC (SPEC `i : num` num_CASES) THEN
    STRIP_TAC THENL
    [ASM_REWRITE_TAC [EL_0; REPLICATE];
     POP_ASSUM SUBST_VAR_TAC THEN
     ASM_REWRITE_TAC [REPLICATE; LT_SUC] THEN
     STRIP_TAC THEN
     FIRST_X_ASSUM (MP_TAC o SPECL [`x:A`; `n':num`]) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) THEN
     MATCH_MP_TAC EL_SUC THEN
     ASM_REWRITE_TAC [LENGTH_REPLICATE]]]);;

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

let take_def =
  let def = new_recursive_definition num_RECURSION
    `(!l. take 0 (l : A list) = []) /\
     (!n l. take (SUC n) (l : A list) = CONS (HD l) (take n (TL l)))` in
  prove
  (`(!l. take 0 (l : A list) = []) /\
    (!n h t.
       n <= LENGTH t ==>
       take (SUC n) (CONS h t) = CONS (h : A) (take n t))`,
   REWRITE_TAC [def; HD; TL]);;

export_thm take_def;;

let drop_def =
  let def = new_recursive_definition num_RECURSION
    `(!l. drop 0 (l : A list) = l) /\
     (!n l. drop (SUC n) (l : A list) = drop n (TL l))` in
  prove
  (`(!l. drop 0 (l : A list) = l) /\
    (!n h t.
       n <= LENGTH t ==>
       drop (SUC n) (CONS (h : A) t) = drop n t)`,
   REWRITE_TAC [def; TL]);;

export_thm drop_def;;

logfile "list-take-drop-thm";;

let take_0 = prove
  (`!l. take 0 (l : A list) = []`,
   ACCEPT_TAC (CONJUNCT1 take_def));;

export_thm take_0;;

let take_suc = prove
  (`!n h t.
      n <= LENGTH t ==>
      take (SUC n) (CONS h t) = CONS (h : A) (take n t)`,
   ACCEPT_TAC (CONJUNCT2 take_def));;

export_thm take_suc;;

let drop_0 = prove
  (`!l. drop 0 (l : A list) = l`,
   ACCEPT_TAC (CONJUNCT1 drop_def));;

export_thm drop_0;;

let drop_suc = prove
  (`!n h t.
      n <= LENGTH t ==>
      drop (SUC n) (CONS (h : A) t) = drop n t`,
   ACCEPT_TAC (CONJUNCT2 drop_def));;

export_thm drop_suc;;

let take_drop = prove
  (`!n (l : A list). n <= LENGTH l ==> APPEND (take n l) (drop n l) = l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [take_0; drop_0; APPEND];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC] THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] drop_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [APPEND; CONS_11] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm take_drop;;

let length_take = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (take n l) = n`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LENGTH; take_def];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC] THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC [LENGTH; SUC_INJ] THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN
     FIRST_ASSUM ACCEPT_TAC]]);;

export_thm length_take;;

let length_drop = prove
  (`!n l. n <= LENGTH (l : A list) ==> LENGTH (drop n l) = LENGTH l - n`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n:num`; `l:A list`] take_drop) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [SYM th]))) THEN
   REWRITE_TAC [LENGTH_APPEND] THEN
   MP_TAC (SPECL [`n:num`; `l:A list`] length_take) THEN
   ASM_REWRITE_TAC [] THEN
   DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC [ADD_SUB2]);;

export_thm length_drop;;

let nth_take = prove
  (`!n l i. n <= LENGTH (l : A list) /\ i < n ==> EL i (take n l) = EL i l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC; take_def] THEN
     INDUCT_TAC THENL
     [STRIP_TAC THEN
      MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC [EL_0];
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [LT_SUC] THEN
      STRIP_TAC THEN
      MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] take_suc) THEN
      ASM_REWRITE_TAC [] THEN
      DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `i < LENGTH (t : A list)` ASSUME_TAC THENL
      [MATCH_MP_TAC LTE_TRANS THEN
       EXISTS_TAC `n : num` THEN
       ASM_REWRITE_TAC [];
       MP_TAC (SPECL [`h:A`; `t:A list`; `i:num`] EL_SUC) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       MP_TAC (SPECL [`h:A`; `take n (t:A list)`; `i:num`] EL_SUC) THEN
       MP_TAC (SPECL [`n:num`; `t:A list`] length_take) THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       ASM_REWRITE_TAC [] THEN
       DISCH_THEN SUBST1_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
       ASM_REWRITE_TAC []]]]]);;

export_thm nth_take;;

let nth_drop = prove
  (`!n l i.
       n <= LENGTH (l : A list) /\ i < LENGTH l - n ==>
       EL i (drop n l) = EL (n + i) l`,
   INDUCT_TAC THENL
   [REWRITE_TAC [ADD; drop_def];
    LIST_INDUCT_TAC THENL
    [REWRITE_TAC [LENGTH; LE; NOT_SUC];
     POP_ASSUM (K ALL_TAC) THEN
     REWRITE_TAC [LENGTH; LE_SUC; ADD] THEN
     REPEAT STRIP_TAC THEN
     POP_ASSUM MP_TAC THEN
     MP_TAC (SPECL [`LENGTH (t : A list)`; `n : num`] SUB_SUC) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     STRIP_TAC THEN
     MP_TAC (SPECL [`n:num`; `h:A`; `t:A list`] drop_suc) THEN
     ASM_REWRITE_TAC [] THEN
     DISCH_THEN SUBST1_TAC THEN
     MP_TAC (SPECL [`h:A`; `t:A list`; `n + i : num`] EL_SUC) THEN
     SUBGOAL_THEN `n + i < LENGTH (t : A list)`
       (fun th -> REWRITE_TAC [th]) THENL
     [POP_ASSUM MP_TAC THEN
      POP_ASSUM MP_TAC THEN
      POP_ASSUM (K ALL_TAC) THEN
      REWRITE_TAC [LE_EXISTS] THEN
      STRIP_TAC THEN
      POP_ASSUM (fun th -> REWRITE_TAC [th]) THEN
      REWRITE_TAC [ADD_SUB2; LT_ADD_LCANCEL];
      DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC []]]]);;

export_thm nth_drop;;

let drop_length = prove
  (`!l. drop (LENGTH l) (l : A list) = []`,
   GEN_TAC THEN
   REWRITE_TAC [GSYM LENGTH_EQ_NIL] THEN
   MP_TAC (SPECL [`LENGTH (l : A list)`; `l : A list`] length_drop) THEN
   REWRITE_TAC [LE_REFL; SUB_REFL]);;

export_thm drop_length;;

let take_length = prove
  (`!l. take (LENGTH l) (l : A list) = l`,
   GEN_TAC THEN
   MP_TAC (SPECL [`LENGTH (l : A list)`; `l : A list`] take_drop) THEN
   REWRITE_TAC [LE_REFL] THEN
   DISCH_THEN (fun th -> CONV_TAC (RAND_CONV (REWR_CONV (SYM th)))) THEN
   REWRITE_TAC [drop_length; APPEND_NIL]);;

export_thm take_length;;

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
   INDUCT_TAC THENL
   [REWRITE_TAC [LT];
    ALL_TAC] THEN
   REWRITE_TAC [interval_def] THEN
   REPEAT GEN_TAC THEN
   MP_TAC (SPEC `i : num` num_CASES) THEN
   STRIP_TAC THENL
   [ASM_REWRITE_TAC [EL_0; ADD_0];
    POP_ASSUM SUBST_VAR_TAC THEN
    REWRITE_TAC [LT_SUC; ADD_SUC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM (MP_TAC o SPECL [`SUC m`; `n' : num`]) THEN
    ASM_REWRITE_TAC [ADD] THEN
    DISCH_THEN (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC EL_SUC THEN
    ASM_REWRITE_TAC [length_interval]]);;

export_thm nth_interval;;

logfile "list-zipwith-def";;

let zipwith_def =
  let def = new_recursive_definition list_RECURSION
    `(!f l. zipwith (f : A -> B -> C) [] l = []) /\
     (!f h t l.
        zipwith (f : A -> B -> C) (CONS h t) l =
        CONS (f h (HD l)) (zipwith f t (TL l)))` in
  prove
  (`(!f. zipwith (f : A -> B -> C) [] [] = []) /\
    (!f h1 h2 t1 t2.
       LENGTH t1 = LENGTH t2 ==>
       zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
       CONS (f h1 h2) (zipwith f t1 t2))`,
   REWRITE_TAC [def; HD; TL]);;

export_thm zipwith_def;;

logfile "list-zipwith-thm";;

let zipwith_nil = prove
  (`!f. zipwith (f : A -> B -> C) [] [] = []`,
   ACCEPT_TAC (CONJUNCT1 zipwith_def));;

export_thm zipwith_nil;;

let zipwith_cons = prove
  (`!f h1 h2 t1 t2.
      LENGTH t1 = LENGTH t2 ==>
      zipwith (f : A -> B -> C) (CONS h1 t1) (CONS h2 t2) =
      CONS (f h1 h2) (zipwith f t1 t2)`,
   ACCEPT_TAC (CONJUNCT2 zipwith_def));;

export_thm zipwith_cons;;

let length_zipwith = prove
  (`!(f : A -> B -> C) l1 l2 n.
      LENGTH l1 = n /\ LENGTH l2 = n ==> LENGTH (zipwith f l1 l2) = n`,
   GEN_TAC THEN
   LIST_INDUCT_TAC THEN
   LIST_INDUCT_TAC THEN
   INDUCT_TAC THEN
   REWRITE_TAC [NOT_SUC; LENGTH] THENL
   [REWRITE_TAC [zipwith_nil; LENGTH];
    POP_ASSUM (K ALL_TAC) THEN
    POP_ASSUM (K ALL_TAC) THEN
    REWRITE_TAC [SUC_INJ] THEN
    STRIP_TAC THEN
    MP_TAC (SPECL [`f : A -> B -> C`; `h : A`; `h' : B`;
                   `t : A list`; `t' : B list`] zipwith_cons) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC [LENGTH; SUC_INJ] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC []]);;

export_thm length_zipwith;;

logfile "list-nub-def";;

let setify_def = new_recursive_definition list_RECURSION
  `(setify ([] : A list) = []) /\
   (!h t.
      setify (CONS h t) =
      if MEM h t then setify t else CONS h (setify t))`;;

export_thm setify_def;;

let nub_def = new_definition
  `!l. nub (l : A list) = REVERSE (setify (REVERSE l))`;;

export_thm nub_def;;

logfile "list-nub-thm";;

let length_setify = prove
  (`!l. LENGTH (setify (l : A list)) <= LENGTH l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [LENGTH; setify_def; LE_REFL] THEN
   BOOL_CASES_TAC `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [LE];
    ASM_REWRITE_TAC [LE_SUC; LENGTH]]);;

export_thm length_setify;;

let mem_setify = prove
  (`!l x. MEM (x : A) (setify l) <=> MEM x l`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [MEM; setify_def] THEN
   GEN_TAC THEN
   bool_cases_tac `(x : A) = h` THENL
   [ASM_REWRITE_TAC [] THEN
    bool_cases_tac `MEM (h : A) t` THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [MEM]];
    ASM_REWRITE_TAC [] THEN
    BOOL_CASES_TAC `MEM (h : A) t` THENL
    [ASM_REWRITE_TAC [];
     ASM_REWRITE_TAC [MEM]]]);;

export_thm mem_setify;;

let setify_idempotent = prove
  (`!l. setify (setify l) = setify (l : A list)`,
   LIST_INDUCT_TAC THEN
   ASM_SIMP_TAC [MEM; setify_def] THEN
   bool_cases_tac `MEM (h : A) t` THENL
   [ASM_REWRITE_TAC [];
    ASM_REWRITE_TAC [setify_def; mem_setify]]);;

export_thm setify_idempotent;;

let length_nub = prove
  (`!l. LENGTH (nub (l : A list)) <= LENGTH l`,
   GEN_TAC THEN
   REWRITE_TAC [nub_def; LENGTH_REVERSE] THEN
   CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM LENGTH_REVERSE])) THEN
   MATCH_ACCEPT_TAC length_setify);;

export_thm length_nub;;

let mem_nub = prove
  (`!l x. MEM (x : A) (nub l) <=> MEM x l`,
   REWRITE_TAC [nub_def; MEM_REVERSE; mem_setify]);;

export_thm mem_nub;;

let nub_idempotent = prove
  (`!l. nub (nub l) = nub (l : A list)`,
   REWRITE_TAC [nub_def; REVERSE_REVERSE; setify_idempotent]);;

export_thm nub_idempotent;;

(* Conversions for bit blasting *)

let append_conv =
    let nil_conv = REWR_CONV (CONJUNCT1 APPEND) in
    let cons_conv = REWR_CONV (CONJUNCT2 APPEND) in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let length_convs =
    let nil_conv = REWR_CONV (CONJUNCT1 LENGTH) in
    let cons_conv = REWR_CONV (CONJUNCT2 LENGTH) in
    let rec rewr_convs tm =
        try (nil_conv tm, [])
        with Failure _ ->
          let th = cons_conv tm in
          let tm' = rand (rand (concl th)) in
          let (th',ths) = rewr_convs tm' in
          let c = RAND_CONV (REWR_CONV th') THENC NUM_SUC_CONV in
          (CONV_RULE (RAND_CONV c) th, th' :: ths) in
    rewr_convs;;

let length_conv tm =
    let (th,_) = length_convs tm in
    th;;

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
    let zero_conv = REWR_CONV EL_0 in
    let side_conv = RAND_CONV length_conv THENC NUM_LT_CONV in
    let suc_th = SPEC_ALL EL_SUC in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let take_conv =
    let zero_conv = REWR_CONV take_0 in
    let side_conv = RAND_CONV length_conv THENC NUM_LE_CONV in
    let suc_th = SPEC_ALL take_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let drop_conv =
    let zero_conv = REWR_CONV drop_0 in
    let side_conv = RAND_CONV length_conv THENC NUM_LE_CONV in
    let suc_th = SPEC_ALL drop_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RATOR_CONV (RAND_CONV num_CONV) THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let zipwith_conv =
    let nil_conv = REWR_CONV zipwith_nil in
    let side_conv =
        LAND_CONV length_conv THENC
        RAND_CONV length_conv THENC
        NUM_EQ_CONV in
    let cons_th = SPEC_ALL zipwith_cons in
    let cons_conv tm =
        let th = PART_MATCH (lhs o rand) cons_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
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

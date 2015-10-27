(* ========================================================================= *)
(* PROOF TOOLS FOR THE ADDITIONAL THEORIES                                   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

let TAUT_TAC : tactic = fun (asl,w) -> ACCEPT_TAC (TAUT w) (asl,w);;

let ASM_TAUT_TAC = REPEAT (POP_ASSUM MP_TAC) THEN TAUT_TAC;;

let not_simp_conv =
    let ths = CONJUNCTS (SPEC_ALL NOT_CLAUSES) in
    FIRST_CONV (map REWR_CONV ths);;

let and_simp_conv =
    let th1 = ITAUT `t /\ ~t <=> F` in
    let th2 = ITAUT `~t /\ t <=> F` in
    let ths = CONJUNCTS (SPEC_ALL AND_CLAUSES) in
    FIRST_CONV (map REWR_CONV (th1 :: th2 :: ths));;

let or_simp_conv =
    let pth = SPEC_ALL EXCLUDED_MIDDLE in
    let th1 = EQT_INTRO pth in
    let th2 = EQT_INTRO (CONV_RULE (REWR_CONV DISJ_SYM) pth) in
    let ths = CONJUNCTS (SPEC_ALL OR_CLAUSES) in
    FIRST_CONV (map REWR_CONV (th1 :: th2 :: ths));;

let iff_simp_conv =
    let th1 = ISPEC `t:bool` REFL_CLAUSE in
    let th2 = ITAUT `(t <=> ~t) <=> F` in
    let th3 = ITAUT `(~t <=> t) <=> F` in
    let ths = CONJUNCTS (SPEC_ALL EQ_CLAUSES) in
    FIRST_CONV (map REWR_CONV (th1 :: th2 :: th3 :: ths));;

let cond_simp_conv =
    let pth = SPEC_ALL COND_CLAUSES in
    REWR_CONV (CONJUNCT1 pth) ORELSEC
    REWR_CONV (CONJUNCT2 pth);;

let bool_simp_conv =
    not_simp_conv ORELSEC
    and_simp_conv ORELSEC
    or_simp_conv ORELSEC
    iff_simp_conv ORELSEC
    cond_simp_conv;;

let bit_blast_subterm_conv = bool_simp_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;
let bit_blast_tac = CONV_TAC bit_blast_conv;;

let cond_conv =
    let pth = SPEC_ALL COND_CLAUSES in
    let ac = REWR_CONV (CONJUNCT1 pth) in
    let bc = REWR_CONV (CONJUNCT2 pth) in
    fun c a b ->
      (RATOR_CONV o RATOR_CONV o RAND_CONV) c THENC
      ((ac THENC a) ORELSEC
       (bc THENC b));;

let andalso_conv =
    let tth = ITAUT `T /\ t <=> t` in
    let fth = ITAUT `F /\ t <=> F` in
    fun c a ->
      (RATOR_CONV o RAND_CONV) c THENC
      (REWR_CONV fth ORELSEC
       (REWR_CONV tth THENC a));;

let orelse_conv =
    let tth = ITAUT `T \/ t <=> T` in
    let fth = ITAUT `F \/ t <=> t` in
    fun c a ->
      (RATOR_CONV o RAND_CONV) c THENC
      (REWR_CONV tth ORELSEC
       (REWR_CONV fth THENC a));;

(* Pretty useless without also making THEN1 infix... *)
let (THEN1) = fun tac1 tac2 -> tac1 THENL [tac2; ALL_TAC];;

let PAT_ASSUM pat =
    let is_pat th = can (term_match [] pat) (concl th) in
    FIRST_X_ASSUM (fun th -> if is_pat th then MP_TAC th else NO_TAC);;

let BOOL_CASES_TAC' =
    let pth = ONCE_REWRITE_RULE [DISJ_SYM] BOOL_CASES_AX in
    fun p -> STRUCT_CASES_TAC (SPEC p pth);;

let bool_cases_tac tm =
    MP_TAC (SPEC tm EXCLUDED_MIDDLE) THEN
    STRIP_TAC;;

let bool_cases_tac' =
    let th = ONCE_REWRITE_RULE [DISJ_SYM] EXCLUDED_MIDDLE in
    fun tm ->
      MP_TAC (SPEC tm th) THEN
      STRIP_TAC;;

let KNOW_TAC =
    let th = ITAUT `!x y. x /\ (x ==> y) ==> y` in
    fun tm ->
      MATCH_MP_TAC th THEN
      EXISTS_TAC tm THEN
      CONJ_TAC;;

let SUFF_TAC =
    let th = ITAUT `!x y. (x ==> y) /\ x ==> y` in
    fun tm ->
      MATCH_MP_TAC th THEN
      EXISTS_TAC tm THEN
      CONJ_TAC;;

let COND_TAC =
    let th = ITAUT `!x y z. x /\ (y ==> z) ==> ((x ==> y) ==> z)` in
    MATCH_MP_TAC th THEN
    CONJ_TAC;;

let rec N_TAC n tac =
    if n == 0 then ALL_TAC else tac THEN N_TAC (n - 1) tac;;

let rec N_CONV n conv =
    if n == 0 then ALL_CONV else conv THENC N_CONV (n - 1) conv;;

let define_newtype' (mk,dest) (a,n) (r,ty) =
  let exists =
      let pth = EQ_MP (SYM (SPEC `T` EXISTS_SIMP)) TRUTH in
      INST_TYPE [(ty,aty)] pth in
  let alph1 v tm =
      let (v1,t1) = dest_forall tm in
      let (_,ty1) = dest_var v1 in
      let (t2,_) = dest_eq t1 in
      let (t3,t4) = dest_comb t2 in
      let (t5,_) = dest_comb t4 in
      let v1' = mk_var (v,ty1) in
      let t4' = mk_comb (t5,v1') in
      let t2' = mk_comb (t3,t4') in
      let t1' = mk_eq (t2',v1') in
      mk_forall (v1',t1') in
  let alph2 th =
      let tm = concl th in
      let (md,dm) = dest_conj tm in
      let md' = alph1 a md in
      let dm' = alph1 r dm in
      let tm' = mk_conj (md',dm') in
      EQ_MP (ALPHA tm tm') th in
  (alph2 o REWRITE_RULE [])
     (new_type_definition n (mk n, dest n) exists);;

let define_newtype =
  let mk n = "mk_" ^ n in
  let dest n = "dest_" ^ n in
  define_newtype' (mk,dest);;

let prove_newtype_inj =
    let th = prove
      (`!(f : B -> A) (g : A -> B).
           (!a. f (g a) = a) ==>
           !a1 a2. a1 = a2 <=> g a1 = g a2`,
       REPEAT STRIP_TAC THEN
       EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN
        REFL_TAC;
        FIRST_X_ASSUM
          (fun th -> CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) THEN
        DISCH_THEN SUBST1_TAC THEN
        REFL_TAC]) in
    MATCH_MP th o CONJUNCT1;;

let prove_newtype_o =
    let th = prove
      (`!(f : B -> A) (g : A -> B).
           (!a. f (g a) = a) ==>
           f o g = I`,
       REPEAT STRIP_TAC THEN
       ASM_REWRITE_TAC [FUN_EQ_THM; o_THM; I_THM]) in
    let rule = MATCH_MP th in
    fun tybij ->
      let (md,dm) = CONJ_PAIR tybij in
      CONJ (rule md) (rule dm);;

(* ------------------------------------------------------------------------- *)
(* Proof tools for list types.                                               *)
(* ------------------------------------------------------------------------- *)

let append_conv =
    let nil_conv = REWR_CONV NIL_APPEND in
    let cons_conv = REWR_CONV CONS_APPEND in
    let rec rewr_conv tm =
        (nil_conv ORELSEC
         (cons_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let length_convs =
    let nil_conv = REWR_CONV LENGTH_NIL in
    let cons_conv = REWR_CONV LENGTH_CONS in
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
    let zero_conv = REWR_CONV REPLICATE_0 in
    let suc_conv = REWR_CONV REPLICATE_SUC in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_CONV THENC
          suc_conv THENC
          RAND_CONV rewr_conv)) tm in
    rewr_conv;;

let nth_conv =
    let zero_conv = REWR_CONV nth_zero in
    let side_conv = RAND_CONV length_conv THENC NUM_LT_CONV in
    let suc_th = SPEC_ALL nth_suc in
    let suc_conv tm =
        let th = PART_MATCH (lhs o rand) suc_th tm in
        let th' = side_conv (lhand (concl th)) in
        MP th (EQT_ELIM th') in
    let rec rewr_conv tm =
        (zero_conv ORELSEC
         (RAND_CONV num_CONV THENC
          suc_conv THENC
          rewr_conv)) tm in
    rewr_conv;;

let take_conv =
    let zero_conv = REWR_CONV take_zero in
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
    let zero_conv = REWR_CONV drop_zero in
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
            LAND_CONV c THENC
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
    nth_conv ORELSEC
    take_conv ORELSEC
    drop_conv ORELSEC
    zipwith_conv ALL_CONV ORELSEC
    list_eq_conv ALL_CONV;;

let bit_blast_subterm_conv = list_bit_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* list *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* list *)

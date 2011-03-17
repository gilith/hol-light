(* ------------------------------------------------------------------------- *)
(* Additional tactics to support the OpenTheory standard library             *)
(* ------------------------------------------------------------------------- *)

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

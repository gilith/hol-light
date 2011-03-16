(* ------------------------------------------------------------------------- *)
(* Additional tactics to support the OpenTheory standard library             *)
(* ------------------------------------------------------------------------- *)

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

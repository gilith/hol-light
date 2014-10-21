(* ========================================================================= *)
(* A collection of tiny theories to test the opentheory tool.                *)
(*                                                                           *)
(* To use this, comment out everything after loads "equal.ml";; in hol.ml,   *)
(* then launch ocaml and type #use "hol.ml";; #use "opentheory/tiny.ml";;    *)
(* ========================================================================= *)

Export.debug_export_thm_enable := true;;
start_logging ();;

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-true-def";;

export_thm T_DEF;;

logfile "bool-true-thm";;

export_thm TRUTH;;

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

logfile "bool-forall-def";;

export_thm FORALL_DEF;;

logfile "bool-forall-thm";;

let FORALL_T = GEN `x:A` TRUTH;;

export_thm FORALL_T;;

(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

logfile "bool-and-def";;

export_thm AND_DEF;;

logfile "bool-and-thm";;

let AND_REFL =
    let th0 = CONJ (ASSUME `x:bool`) (ASSUME `x:bool`) in
    let th1 = CONJUNCT1 (ASSUME `x /\ x`) in
    GEN `x:bool` (DEDUCT_ANTISYM_RULE th0 th1);;

export_thm AND_REFL;;

let AND_RID =
    let th0 = CONJ (ASSUME `x:bool`) TRUTH in
    let th1 = CONJUNCT1 (ASSUME `x /\ T`) in
    GEN `x:bool` (DEDUCT_ANTISYM_RULE th0 th1);;

export_thm AND_RID;;

logfile "bool-and-thm-new";;

let AND_REFL' =
    let th0 = CONJ (ASSUME `x:bool`) (ASSUME `x:bool`) in
    let th1 = CONJUNCT1 (ASSUME `x /\ x`) in
    GEN `x:bool` (DEDUCT_ANTISYM_RULE th0 th1);;

export_thm AND_REFL';;

let AND_COMM' =
    let th0 = ASSUME `x /\ y` in
    let th1 = CONJ (CONJUNCT2 th0) (CONJUNCT1 th0) in
    let th2 = ASSUME `y /\ x` in
    let th3 = CONJ (CONJUNCT2 th2) (CONJUNCT1 th2) in
    GEN `x:bool` (GEN `y:bool` (DEDUCT_ANTISYM_RULE th1 th3));;

export_thm AND_COMM';;

let AND_LID' =
    let th0 = CONJ TRUTH (ASSUME `x:bool`) in
    let th1 = CONJUNCT2 (ASSUME `T /\ x`) in
    GEN `x:bool` (DEDUCT_ANTISYM_RULE th0 th1);;

export_thm AND_LID';;

(* ------------------------------------------------------------------------- *)
(* Rules for ==>                                                             *)
(* ------------------------------------------------------------------------- *)

logfile "bool-implies-def";;

export_thm IMP_DEF;;

logfile "bool-implies-thm";;

let IMP_REFL =
    let th0 = AP_THM (AP_THM IMP_DEF `x:bool`) `x:bool` in
    let th1 = BETAS_CONV `(\p q. p /\ q <=> p) x x` in
    GEN `x:bool` (EQ_MP (SYM (TRANS th0 th1)) (SPEC `x:bool` AND_REFL));;

export_thm IMP_REFL;;

let IMP_T =
    let th0 = AP_THM (AP_THM IMP_DEF `x:bool`) `T` in
    let th1 = BETAS_CONV `(\p q. p /\ q <=> p) x T` in
    GEN `x:bool` (EQ_MP (SYM (TRANS th0 th1)) (SPEC `x:bool` AND_RID));;

export_thm IMP_T;;

logfile "bool-implies-thm-new";;

let IMP_REFL' =
    let th0 = AP_THM (AP_THM IMP_DEF `x:bool`) `x:bool` in
    let th1 = BETAS_CONV `(\p q. p /\ q <=> p) x x` in
    GEN `x:bool` (EQ_MP (SYM (TRANS th0 th1)) (SPEC `x:bool` AND_REFL'));;

export_thm IMP_REFL';;

let IMP_T' =
    let th0 = AP_THM (AP_THM IMP_DEF `x:bool`) `T` in
    let th1 = BETAS_CONV `(\p q. p /\ q <=> p) x T` in
    let th2 = SPEC `x:bool` (SPEC `T` AND_COMM') in
    let th3 = SPEC `x:bool` AND_LID' in
    GEN `x:bool` (EQ_MP (SYM (TRANS th0 th1)) (TRANS th2 th3));;

export_thm IMP_T';;

logfile_end ();;

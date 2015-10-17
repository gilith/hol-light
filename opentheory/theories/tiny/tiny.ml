(* ========================================================================= *)
(* A COLLECTION OF TINY THEORIES TO TEST THE OPENTHEORY TOOL                 *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Start exporting.                                                          *)
(* ------------------------------------------------------------------------- *)

Export.debug_export_thm_enable := true;;
export_begin ();;

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "bool-true-def";;

export_thm T_DEF;;

export_theory "bool-true-thm";;

export_thm TRUTH;;

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

export_theory "bool-forall-def";;

export_thm FORALL_DEF;;

export_theory "bool-forall-thm";;

let FORALL_T = GEN `x:A` TRUTH;;

export_thm FORALL_T;;

(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "bool-and-def";;

export_thm AND_DEF;;

export_theory "bool-and-thm";;

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

export_theory "bool-and-thm-new";;

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

export_theory "bool-implies-def";;

export_thm IMP_DEF;;

export_theory "bool-implies-thm";;

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

export_theory "bool-implies-thm-new";;

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

(* ------------------------------------------------------------------------- *)
(* Stop exporting (and generate theory files).                               *)
(* ------------------------------------------------------------------------- *)

export_end ();;

(* ========================================================================= *)
(* THE STANDARD THEORY LIBRARY IN HASKELL                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Haskell source.                                                           *)
(* ------------------------------------------------------------------------- *)

export_theory "base-haskell-src";;

(* Lists *)

let () = (export_thm o prove)
 (`(LENGTH ([] : A list) = 0) /\
   (!(h : A) t. LENGTH (CONS h t) = LENGTH t + 1)`,
  REWRITE_TAC [LENGTH_NIL; LENGTH_CONS; ADD1]);;

(* Natural numbers *)

let () = (export_thm o prove)
 (`!n. EVEN n <=> n MOD 2 = 0`,
  ACCEPT_TAC EVEN_MOD);;

let () = (export_thm o prove)
 (`!n. ODD n <=> ~EVEN n`,
  REWRITE_TAC [NOT_EVEN]);;

(* ------------------------------------------------------------------------- *)
(* Haskell tests.                                                            *)
(* ------------------------------------------------------------------------- *)

export_theory "base-haskell-test";;

let () = (export_thm o prove)
 (`!x : A option. ~(is_some x <=> is_none x)`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A option` option_cases) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [is_some_def; is_none_def]);;

export_thm sum_distinct;;  (* Haskell *)

(* isLeft and isRight are only supported in Haskell base >= 4.7.0.0
let () = (export_thm o prove)
 (`!x : A + B. ~(ISL x <=> ISR x)`,
  GEN_TAC THEN
  MP_TAC (SPEC `x : A + B` sum_CASES) THEN
  STRIP_TAC THEN
  ASM_REWRITE_TAC [ISL_def; ISR_def]);;
*)

let () = (export_thm o prove)
 (`!l : (A # B) list. (let (x,y) = unzip l in zip x y) = l`,
  GEN_TAC THEN
  REWRITE_TAC [LET_DEF; LET_END_DEF] THEN
  MP_TAC (ISPEC `unzip l : A list # B list ` PAIR_SURJECTIVE) THEN
  DISCH_THEN
    (X_CHOOSE_THEN `xs : A list`
       (X_CHOOSE_THEN `ys : B list` STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC [] THEN
  POP_ASSUM (STRIP_ASSUME_TAC o REWRITE_RULE [zip_unzip]) THEN
  ASM_REWRITE_TAC []);;

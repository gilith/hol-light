(* ------------------------------------------------------------------------- *)
(* OpenTheory test theory.                                                   *)
(* ------------------------------------------------------------------------- *)

start_logging ();;

(* ------------------------------------------------------------------------- *)
(* Setup.                                                                    *)
(* ------------------------------------------------------------------------- *)

new_constant ("a", `:bool`);;

new_constant ("b", `:bool`);;

new_constant ("c", `:bool`);;

let test_ab_ax = new_axiom `a = b`;;

let test_bc_ax = new_axiom `b = c`;;

let opentheory_unwanted_id_def =
  let th = new_basic_definition `unwanted_id = \z. (z : bool)` in
  let () = delete_const_definition ["unwanted_id"] in
  let () = delete_proof th in
  th;;

let unwanted_id_def = prove
  (`!(z : bool). unwanted_id z = z`,
   REWRITE_TAC [opentheory_unwanted_id_def]);;

(* ------------------------------------------------------------------------- *)
(* Testing the argument order of the eqMp command                            *)
(* ------------------------------------------------------------------------- *)

logfile "example4";;

let test_ax = new_axiom `a`;;

let test_th = EQ_MP test_ab_ax test_ax;;

export_thm test_th;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Testing the QBF cloud tactic                                              *)
(* ------------------------------------------------------------------------- *)

logfile "qbf";;

let qbf_query = new_axiom `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

export_thm qbf_query;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Testing removal of Unwanted.id constants                                  *)
(* ------------------------------------------------------------------------- *)

(* Clean removal of appTerm *)

logfile "example5";;

let test_th = REFL `unwanted_id a`;;

export_thm test_th;;

logfile_end ();;

(* Clean removal of appThm *)

logfile "example6";;

let test_th =
    TRANS
      (MK_COMB (REFL `unwanted_id`, test_ab_ax))
      (MK_COMB (REFL `unwanted_id`, test_bc_ax));;

export_thm test_th;;

logfile_end ();;

(* Unclean removal using basic definition *)

logfile "example7";;

let test_th =
  let conv = RATOR_CONV (K opentheory_unwanted_id_def) THENC BETA_CONV in
  TRANS
    (TRANS
      (conv `unwanted_id a`)
      test_ab_ax)
    (TRANS
      test_bc_ax
      (SYM (conv `unwanted_id c`)));;

export_thm test_th;;

logfile_end ();;

(* Unclean removal when unwanted_id is air-dropped in using betaConv *)

logfile "example8";;

let test_th =
    let conv th = RATOR_CONV (ABS_CONV (RAND_CONV (K th))) in
    let atm = `(\f. f a) unwanted_id` in
    let ctm = `(\f. f c) unwanted_id` in
    TRANS
      (TRANS
        (SYM (BETA_CONV atm))
        (conv test_ab_ax atm))
      (TRANS
        (SYM (conv (SYM test_bc_ax) ctm))
        (BETA_CONV ctm));;

export_thm test_th;;

logfile_end ();;

(* Unclean removal when unwanted_id is air-dropped in using subst *)

logfile "example9";;

let test_th =
    let f = `f : bool -> bool` in
    let th10 = ASSUME (mk_comb (f,`a`)) in
    let th11 = AP_TERM f test_ab_ax in
    let th12 = EQ_MP th11 th10 in
    let th13 = AP_TERM f test_bc_ax in
    let th14 = EQ_MP th13 th12 in
    let th15 = INST [(`unwanted_id`,f)] th14 in
    let th20 = ASSUME (mk_comb (f,`c`)) in
    let th21 = AP_TERM f (SYM test_bc_ax) in
    let th22 = EQ_MP th21 th20 in
    let th23 = AP_TERM f (SYM test_ab_ax) in
    let th24 = EQ_MP th23 th22 in
    let th25 = INST [(`unwanted_id`,f)] th24 in
    DEDUCT_ANTISYM_RULE th25 th15;;

export_thm test_th;;

logfile_end ();;

(* ------------------------------------------------------------------------- *)
(* Testing generation of theory theorems.                                    *)
(* ------------------------------------------------------------------------- *)

logfile "example10";;

let def1 = new_basic_definition `c1 = \f x. (f : A -> B) x`;;

export_thm def1;;

let (abs_rep1,rep_abs1) =
    let th = prove
      (`(\l. LENGTH (l : A list) = 0) []`,
       REWRITE_TAC [LENGTH]) in
    new_basic_type_definition "t1" ("a1","r1") th;;

export_thm abs_rep1;;
export_thm rep_abs1;;

let (abs_rep2,rep_abs2) =
    let th = prove
      (`(\l. LENGTH (l : A list) = LENGTH ([] : B list)) []`,
       REWRITE_TAC [LENGTH]) in
    new_basic_type_definition "t2" ("a2","r2") th;;

export_thm abs_rep2;;
export_thm rep_abs2;;

logfile_end ();;

stop_logging ();;

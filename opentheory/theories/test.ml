(* ========================================================================= *)
(* OPENTHEORY TEST THEORY                                                    *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Start exporting.                                                          *)
(* ------------------------------------------------------------------------- *)

export_begin ();;

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

export_theory "example4";;

let test_ax = new_axiom `a`;;

let test_th = EQ_MP test_ab_ax test_ax;;

export_thm test_th;;

(* ------------------------------------------------------------------------- *)
(* Testing removal of Unwanted.id constants                                  *)
(* ------------------------------------------------------------------------- *)

(* Clean removal of appTerm *)

export_theory "example5";;

let test_th = REFL `unwanted_id a`;;

export_thm test_th;;

(* Clean removal of appThm *)

export_theory "example6";;

let test_th =
    TRANS
      (MK_COMB (REFL `unwanted_id`, test_ab_ax))
      (MK_COMB (REFL `unwanted_id`, test_bc_ax));;

export_thm test_th;;

(* Unclean removal using basic definition *)

export_theory "example7";;

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

(* Unclean removal when unwanted_id is air-dropped in using betaConv *)

export_theory "example8";;

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

(* Unclean removal when unwanted_id is air-dropped in using subst *)

export_theory "example9";;

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

(* ------------------------------------------------------------------------- *)
(* Simple example exporting a theorem with hypotheses                        *)
(* ------------------------------------------------------------------------- *)

export_theory "example11";;

let test_th =
    ASSUME `a`;;

export_thm test_th;;

(* ------------------------------------------------------------------------- *)
(* Same constant name in assumption and theorem                              *)
(* ------------------------------------------------------------------------- *)

export_theory "example12";;

new_constant ("asm_name", `:bool`);;

let same_name_ax = new_axiom `asm_name`;;

let same_name_def = new_basic_definition `thm_name = asm_name`;;

let same_name_th = EQ_MP (SYM same_name_def) same_name_ax;;

export_thm same_name_th;;

(* ------------------------------------------------------------------------- *)
(* Testing constant and type definitions.                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "example13";;

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

(* ------------------------------------------------------------------------- *)
(* Testing large numerals                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "example14";;

let fermat7 = NUM_REDUCE_CONV `2 EXP (2 EXP 7) + 1`;;

let fermat7_factorization =
    let th = NUM_REDUCE_CONV `59649589127497217 * 5704689200685129054721` in
    TRANS fermat7 (SYM th);;

let fermat7_axiom = new_axiom (concl fermat7_factorization);;

export_thm fermat7_axiom;;

(* ------------------------------------------------------------------------- *)
(* Testing large numerals                                                    *)
(* ------------------------------------------------------------------------- *)

export_theory "example15";;

let expand_power_of_two n =
    let th = SPEC `2` EXP_0 in
    let rewr = prove
      (`!n m. 2 EXP n = m <=> 2 EXP SUC n = m + m`,
       REPEAT GEN_TAC THEN
       REWRITE_TAC [GSYM MULT_2; EXP; EQ_MULT_LCANCEL] THEN
       REWRITE_TAC [TWO; NOT_SUC]) in
    let conv = REWR_CONV rewr THENC LAND_CONV (RAND_CONV NUM_SUC_CONV) in
    funpow n (CONV_RULE conv) th;;

(***export_thm (new_axiom (concl (expand_power_of_two 20)));;***)
export_thm (expand_power_of_two 20);;

(* ------------------------------------------------------------------------- *)
(* Testing the QBF cloud tactic                                              *)
(* ------------------------------------------------------------------------- *)

export_theory "qbf1";;

let qbf_query = new_axiom `?x. !y. ?z. (~x \/ ~y) /\ (~z \/ ~y)`;;

export_thm qbf_query;;

(* ------------------------------------------------------------------------- *)
(* Stop exporting (and generate theory files).                               *)
(* ------------------------------------------------------------------------- *)

export_end ();;

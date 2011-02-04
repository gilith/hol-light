(* ------------------------------------------------------------------------- *)
(* A functor theory of modular arithmetic.                                   *)
(* ------------------------------------------------------------------------- *)

new_constant ("mod_N", `:num`);;

let mod_N_positive = new_axiom `~(mod_N = 0)`;;

logfile "modular-mod";;

let lt_mod = prove
  (`!n. n < mod_N ==> n MOD mod_N = n`,
   REPEAT STRIP_TAC THEN
   MP_TAC (SPECL [`n:num`; `mod_N:num`] MOD_LT) THEN
   ASM_REWRITE_TAC []);;

export_thm lt_mod;;

let mod_lt = prove
  (`!n. n MOD mod_N < mod_N`,
   GEN_TAC THEN
   MP_TAC (SPECL [`n:num`; `mod_N:num`] DIVISION) THEN
   MATCH_MP_TAC (TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [mod_N_positive];
    DISCH_THEN (ACCEPT_TAC o CONJUNCT2)]);;

export_thm mod_lt;;

let mod_mod = prove
  (`!n. n MOD mod_N MOD mod_N = n MOD mod_N`,
   GEN_TAC THEN
   MP_TAC (SPECL [`n:num`; `mod_N:num`] MOD_MOD_REFL) THEN
   MATCH_MP_TAC (TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [mod_N_positive];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_mod;;

let mod_add = prove
  (`!m n. (m MOD mod_N + n MOD mod_N) MOD mod_N = (m + n) MOD mod_N`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m:num`; `n:num`; `mod_N:num`] MOD_ADD_MOD) THEN
   MATCH_MP_TAC (TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [mod_N_positive];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_add;;

let mod_mult = prove
  (`!m n. (m MOD mod_N * n MOD mod_N) MOD mod_N = (m * n) MOD mod_N`,
   REPEAT GEN_TAC THEN
   MP_TAC (SPECL [`m:num`; `mod_N:num`; `n:num`] MOD_MULT_MOD2) THEN
   MATCH_MP_TAC (TAUT `a /\ (b ==> c) ==> (a ==> b) ==> c`) THEN
   CONJ_TAC THENL
   [REWRITE_TAC [mod_N_positive];
    DISCH_THEN ACCEPT_TAC]);;

export_thm mod_mult;;

logfile "modular-equiv-def";;

let mod_equiv_def = new_definition
  `!x y. mod_equiv x y = x MOD mod_N = y MOD mod_N`;;

export_thm mod_equiv_def;;

logfile "modular-equiv-thm";;

let mod_equiv_refl = prove
  (`!x. mod_equiv x x`,
   REWRITE_TAC [mod_equiv_def]);;

export_thm mod_equiv_refl;;

let mod_equiv_trans = prove
  (`!x y z. mod_equiv x y /\ mod_equiv y z ==> mod_equiv x z`,
   REWRITE_TAC [mod_equiv_def] THEN
   SIMP_TAC []);;

export_thm mod_equiv_trans;;

let mod_equiv_eq = prove
  (`!x y. mod_equiv x = mod_equiv y <=> x MOD mod_N = y MOD mod_N`,
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   REWRITE_TAC [mod_equiv_def] THEN
   REPEAT STRIP_TAC THEN
   EQ_TAC THENL
   [DISCH_THEN (MP_TAC o SPEC `y:num`) THEN
    REWRITE_TAC [];
    DISCH_THEN (fun th -> REWRITE_TAC [th])]);;

export_thm mod_equiv_eq;;

let mod_equiv_inj = prove
  (`!x y. x < mod_N /\ y < mod_N /\ mod_equiv x = mod_equiv y ==> x = y`,
   REWRITE_TAC [mod_equiv_eq] THEN
   REPEAT STRIP_TAC THEN
   POP_ASSUM MP_TAC THEN
   ASM_SIMP_TAC [lt_mod]);;

export_thm mod_equiv_inj;;

let mod_equiv_add = prove
  (`!x1 x2 y1 y2.
      mod_equiv x1 x2 /\ mod_equiv y1 y2 ==> mod_equiv (x1 + y1) (x2 + y2)`,
   REWRITE_TAC [mod_equiv_def] THEN
   ONCE_REWRITE_TAC [GSYM mod_add] THEN
   SIMP_TAC []);;

export_thm mod_equiv_add;;

let mod_equiv_mult = prove
  (`!x1 x2 y1 y2.
      mod_equiv x1 x2 /\ mod_equiv y1 y2 ==> mod_equiv (x1 * y1) (x2 * y2)`,
   REWRITE_TAC [mod_equiv_def] THEN
   ONCE_REWRITE_TAC [GSYM mod_mult] THEN
   SIMP_TAC []);;

export_thm mod_equiv_mult;;

logfile "modular-def";;

let (mod_abs_rep,mod_rep_abs) = define_quotient_type
  "mod" ("mod_from_class","mod_to_class") `mod_equiv`;;

let num_to_mod_def = new_definition
  `!x. num_to_mod x = mod_from_class (mod_equiv x)`;;

let mod_rep_abs_surj = prove
  (`!x. (?y. mod_to_class x = mod_equiv y)`,
   GEN_TAC THEN
   REWRITE_TAC [mod_rep_abs; mod_abs_rep]);;

let mod_rep_abs_triv = prove
  (`!x. mod_to_class (mod_from_class (mod_equiv x)) = mod_equiv x`,
   GEN_TAC THEN
   REWRITE_TAC [GSYM mod_rep_abs] THEN
   EXISTS_TAC `x:num` THEN
   REFL_TAC);;

let mod_from_class_inj = prove
  (`!x y.
      mod_from_class (mod_equiv x) = mod_from_class (mod_equiv y) ==>
      mod_equiv x = mod_equiv y`,
   REPEAT STRIP_TAC THEN
   ONCE_REWRITE_TAC [GSYM mod_rep_abs_triv] THEN
   ASM_REWRITE_TAC []);;

let mod_to_num_exists = prove
  (`!x. ?y. y < mod_N /\ num_to_mod y = x`,
   GEN_TAC THEN
   ONCE_REWRITE_TAC [GSYM mod_abs_rep] THEN
   REWRITE_TAC [num_to_mod_def] THEN
   MP_TAC (SPEC `x:mod` mod_rep_abs_surj) THEN
   STRIP_TAC THEN
   ASM_REWRITE_TAC [] THEN
   EXISTS_TAC `y MOD mod_N` THEN
   REWRITE_TAC [mod_lt; mod_abs_rep] THEN
   AP_TERM_TAC THEN
   ONCE_REWRITE_TAC [FUN_EQ_THM] THEN
   GEN_TAC THEN
   REWRITE_TAC [mod_equiv_def; mod_mod]);;

let mod_to_num_def = new_specification ["mod_to_num"]
  (REWRITE_RULE [SKOLEM_THM] mod_to_num_exists);;

let mod_to_num_from_num = prove
  (`!x. num_to_mod (mod_to_num x) = x`,
   REWRITE_TAC [mod_to_num_def]);;

export_thm mod_to_num_from_num;;

let num_to_mod_inj = prove
  (`!x y. x < mod_N /\ y < mod_N /\ num_to_mod x = num_to_mod y ==> x = y`,
   REWRITE_TAC [num_to_mod_def] THEN
   REPEAT STRIP_TAC THEN
   MATCH_MP_TAC mod_equiv_inj THEN
   ASM_REWRITE_TAC [] THEN
   MATCH_MP_TAC mod_from_class_inj THEN
   ASM_REWRITE_TAC []);;

export_thm num_to_mod_inj;;

let num_to_mod_to_num = prove
  (`!x. mod_to_num (num_to_mod x) = x MOD mod_N`,
   GEN_TAC THEN
   MATCH_MP_TAC num_to_mod_inj THEN
   SIMP_TAC [mod_to_num_def; mod_to_num_from_num; mod_lt] THEN
   REWRITE_TAC [num_to_mod_def] THEN
   AP_TERM_TAC THEN
   SIMP_TAC [mod_equiv_eq; mod_mod]);;

export_thm num_to_mod_to_num;;

let (mod_add_def,mod_add_lift) = lift_function
  mod_rep_abs (mod_equiv_refl,mod_equiv_trans)
  "mod_add" mod_equiv_add;;

let num_to_mod_add =
  GEN_ALL (REWRITE_RULE [GSYM num_to_mod_def] mod_add_lift);;

export_thm num_to_mod_add;;

let (mod_mult_def,mod_mult_lift) = lift_function
  mod_rep_abs (mod_equiv_refl,mod_equiv_trans)
  "mod_mult" mod_equiv_mult;;

let num_to_mod_mult =
  GEN_ALL (REWRITE_RULE [GSYM num_to_mod_def] mod_mult_lift);;

export_thm num_to_mod_mult;;

let mod_neg_def = new_definition
  `!x. mod_neg x = num_to_mod (mod_N - mod_to_num x)`;;

export_thm mod_neg_def;;

let mod_sub_def = new_definition
  `!x y. mod_sub x y = mod_add x (mod_neg y)`;;

export_thm mod_sub_def;;

let mod_le_def = new_definition
  `!x y. mod_le x y = mod_to_num x <= mod_to_num y`;;

export_thm mod_le_def;;

let mod_lt_def = new_definition
  `!x y. mod_lt x y = ~(mod_le y x)`;;

export_thm mod_lt_def;;

logfile_end ();;

(* ========================================================================= *)
(* MONOID MULTIPLICATION                                                     *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of monoid multiplication.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-mult-def";;

let (monoid_mult_right_zero,monoid_mult_right_suc) =
    let def = new_recursive_definition num_RECURSION
          `(!(x : monoid). monoid_mult x 0 = monoid_zero) /\
           (!(x : monoid) n.
              monoid_mult x (SUC n) = monoid_add x (monoid_mult x n))` in
    CONJ_PAIR def;;

(*PARAMETRIC
new_constant ("monoid_mult", `:monoid -> num -> monoid`);;
*)

export_thm monoid_mult_right_zero;;
export_thm monoid_mult_right_suc;;

(*PARAMETRIC
let monoid_mult_right_zero = new_axiom
  `!x. monoid_mult x 0 = monoid_zero`;;

let monoid_mult_right_suc = new_axiom
  `!x n. monoid_mult x (SUC n) = monoid_add x (monoid_mult x n)`;;
*)

(*BEGIN-PARAMETRIC*)
let monoid_mult_def = CONJ monoid_mult_right_zero monoid_mult_right_suc;;
(*END-PARAMETRIC*)

(* ------------------------------------------------------------------------- *)
(* Properties of monoid multiplication.                                      *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-mult-thm";;

let monoid_mult_left_zero = prove
  (`!n. monoid_mult monoid_zero n = monoid_zero`,
   INDUCT_TAC THENL
   [REWRITE_TAC [monoid_mult_right_zero];
    ASM_REWRITE_TAC [monoid_mult_right_suc; monoid_add_right_zero]]);;

export_thm monoid_mult_left_zero;;

(*PARAMETRIC
let monoid_mult_left_zero = new_axiom
   `!n. monoid_mult monoid_zero n = monoid_zero`;;
*)

let monoid_mult_right_one = prove
  (`!x. monoid_mult x 1 = x`,
   REWRITE_TAC [ONE; monoid_mult_def; monoid_add_right_zero]);;

export_thm monoid_mult_right_one;;

(*PARAMETRIC
let monoid_mult_right_one = new_axiom
   `!x. monoid_mult x 1 = x`;;
*)

let monoid_mult_right_two = prove
  (`!x. monoid_mult x 2 = monoid_add x x`,
   REWRITE_TAC [TWO; monoid_mult_right_suc; monoid_mult_right_one]);;

export_thm monoid_mult_right_two;;

(*PARAMETRIC
let monoid_mult_right_two = new_axiom
   `!x. monoid_mult x 2 = monoid_add x x`;;
*)

let monoid_mult_right_add = prove
  (`!x m n.
      monoid_mult x (m + n) = monoid_add (monoid_mult x m) (monoid_mult x n)`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`m : num`, `m : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [monoid_mult_right_zero; ZERO_ADD; monoid_add_left_zero];
    ASM_REWRITE_TAC [monoid_mult_right_suc; monoid_add_assoc; SUC_ADD]]);;

export_thm monoid_mult_right_add;;

(*PARAMETRIC
let monoid_mult_right_add = new_axiom
   `!x m n.
      monoid_mult x (m + n) = monoid_add (monoid_mult x m) (monoid_mult x n)`;;
*)

let monoid_mult_right_suc' = prove
  (`!x n. monoid_mult x (SUC n) = monoid_add (monoid_mult x n) x`,
   REWRITE_TAC [ADD1; monoid_mult_right_add; monoid_mult_right_one]);;

export_thm monoid_mult_right_suc';;

(*PARAMETRIC
let monoid_mult_right_suc' = new_axiom
   `!x n. monoid_mult x (SUC n) = monoid_add (monoid_mult x n) x`;;
*)

let monoid_mult_right_mult = prove
  (`!x m n. monoid_mult x (m * n) = monoid_mult (monoid_mult x m) n`,
   GEN_TAC THEN
   GEN_TAC THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [monoid_mult_right_zero; MULT_0];
    ASM_REWRITE_TAC [monoid_mult_right_suc; MULT_SUC; monoid_mult_right_add]]);;

export_thm monoid_mult_right_mult;;

(*PARAMETRIC
let monoid_mult_right_mult = new_axiom
   `!x m n. monoid_mult x (m * n) = monoid_mult (monoid_mult x m) n`;;
*)

let monoid_comm_left_mult = prove
  (`!x n y.
      monoid_add x y = monoid_add y x ==>
      monoid_add (monoid_mult x n) y = monoid_add y (monoid_mult x n)`,
   REPEAT STRIP_TAC THEN
   SPEC_TAC (`n : num`, `n : num`) THEN
   INDUCT_TAC THENL
   [REWRITE_TAC [monoid_mult_right_zero; monoid_comm_left_zero];
    REWRITE_TAC [monoid_mult_right_suc] THEN
    MATCH_MP_TAC monoid_comm_left_add THEN
    ASM_REWRITE_TAC []]);;

export_thm monoid_comm_left_mult;;

(*PARAMETRIC
let monoid_comm_left_mult = new_axiom
   `!x n y.
      monoid_add x y = monoid_add y x ==>
      monoid_add (monoid_mult x n) y = monoid_add y (monoid_mult x n)`;;
*)

let monoid_comm_right_mult = prove
  (`!x n y.
      monoid_add y x = monoid_add x y ==>
      monoid_add y (monoid_mult x n) = monoid_add (monoid_mult x n) y`,
   REPEAT GEN_TAC THEN
   ONCE_REWRITE_TAC [EQ_SYM_EQ] THEN
   MATCH_ACCEPT_TAC monoid_comm_left_mult);;

export_thm monoid_comm_right_mult;;

(*PARAMETRIC
let monoid_comm_right_mult = new_axiom
   `!x n y.
      monoid_add y x = monoid_add x y ==>
      monoid_add y (monoid_mult x n) = monoid_add (monoid_mult x n) y`;;
*)

(* ------------------------------------------------------------------------- *)
(* Definition of monoid multiplication by repeated addition.                 *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-mult-add-def";;

let (monoid_mult_add_nil,monoid_mult_add_cons) =
  let def = new_recursive_definition list_RECURSION
    `(!z x. monoid_mult_add z x [] = z) /\
     (!z x h t.
        monoid_mult_add z x (CONS h t) =
        monoid_mult_add (if h then monoid_add z x else z)
          (monoid_add x x) t)` in
  CONJ_PAIR def;;

(*PARAMETRIC
new_constant ("monoid_mult_add", `:monoid -> monoid -> bool list -> monoid`);;
*)

export_thm monoid_mult_add_nil;;
export_thm monoid_mult_add_cons;;

(*PARAMETRIC
let monoid_mult_add_nil = new_axiom
    `!z x. monoid_mult_add z x [] = z`;;

let monoid_mult_add_cons = new_axiom
     `!z x h t.
        monoid_mult_add z x (CONS h t) =
        monoid_mult_add (if h then monoid_add z x else z)
          (monoid_add x x) t`;;
*)

(*BEGIN-PARAMETRIC*)
let monoid_mult_add_def = CONJ monoid_mult_add_nil monoid_mult_add_cons;;
(*END-PARAMETRIC*)

(* ------------------------------------------------------------------------- *)
(* Correctness of monoid multiplication by repeated addition.                *)
(* ------------------------------------------------------------------------- *)

export_theory "monoid-mult-add-thm";;

let monoid_mult_add_invariant = prove
  (`!z x l.
      monoid_mult_add z x l =
      monoid_add z (monoid_mult x (bits_to_num l))`,
   REPEAT GEN_TAC THEN
   SPEC_TAC (`x : monoid`, `x : monoid`) THEN
   SPEC_TAC (`z : monoid`, `z : monoid`) THEN
   SPEC_TAC (`l : bool list`, `l : bool list`) THEN
   LIST_INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC
      [bits_to_num_nil; monoid_mult_add_def; monoid_mult_def;
       monoid_add_right_zero];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN
   REWRITE_TAC [monoid_mult_add_def; bits_to_num_cons] THEN
   FIRST_X_ASSUM (CONV_TAC o LAND_CONV o REWR_CONV) THEN
   REWRITE_TAC
     [bit_cons_def; monoid_mult_right_add; monoid_mult_right_mult;
      monoid_mult_right_two; GSYM monoid_add_assoc] THEN
   AP_THM_TAC THEN
   AP_TERM_TAC THEN
   BOOL_CASES_TAC `h : bool` THEN
   REWRITE_TAC
     [bit_to_num_def; monoid_mult_right_one; monoid_mult_right_zero;
      monoid_add_right_zero]);;

export_thm monoid_mult_add_invariant;;

(*PARAMETRIC
let monoid_mult_add_invariant = new_axiom
   `!z x l.
      monoid_mult_add z x l =
      monoid_add z (monoid_mult x (bits_to_num l))`;;
*)

let monoid_mult_add_correct = prove
  (`!x n.
      monoid_mult_add monoid_zero x (num_to_bits n) =
      monoid_mult x n`,
   REWRITE_TAC
     [monoid_mult_add_invariant; monoid_add_left_zero; num_to_bits_to_num]);;

export_thm monoid_mult_add_correct;;

(*PARAMETRIC
let monoid_mult_add_correct = new_axiom
   `!x n.
      monoid_mult_add monoid_zero x (num_to_bits n) =
      monoid_mult x n`;;
*)

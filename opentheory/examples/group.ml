(* ------------------------------------------------------------------------- *)
(* A parametric theory of groups.                                            *)
(* ------------------------------------------------------------------------- *)

(*PARAMETRIC
(* group *)
*)

(* The theory parameters *)

logfile "group-witness";;

let (group_add_left_zero,group_add_left_neg,group_add_assoc) =
  let tybij = define_newtype ("x","group") ("u",`:1`) in
  let _ = new_definition `group_zero = mk_group one` in
  let _ = new_definition
    `!(x : group) (y : group). group_add x y = group_zero` in
  let _ = new_definition `!x : group. group_neg x = group_zero` in
  let th = prove
    (`!x : group. x = group_zero`,
     GEN_TAC THEN
     ONCE_REWRITE_TAC [GSYM (CONJUNCT1 tybij)] THEN
     ONCE_REWRITE_TAC [one] THEN
     REFL_TAC) in
  let prove_eq tm =
    prove (tm, REPEAT GEN_TAC THEN ONCE_REWRITE_TAC [th] THEN REFL_TAC) in
  let th1 = prove_eq `!x. group_add group_zero x = x` in
  let th2 = prove_eq `!x. group_add (group_neg x) x = group_zero` in
  let th3 = prove_eq
    `!x y z. group_add (group_add x y) z = group_add x (group_add y z)` in
  (th1,th2,th3);;

let group_sub_def = new_definition
  `!(x : group) (y : group).
     group_sub x y = group_add x (group_neg y)`;;

let (group_mult_zero,group_mult_suc) =
    let def = new_recursive_definition num_RECURSION
          `(!(x : group). group_mult x 0 = group_zero) /\
           (!(x : group) n.
              group_mult x (SUC n) = group_add x (group_mult x n))` in
    CONJ_PAIR def;;

let group_mult_def = CONJ group_mult_zero group_mult_suc;;

logfile "group-thm";;

(*PARAMETRIC
(* group-thm *)
*)



logfile_end ();;

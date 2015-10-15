(* ========================================================================= *)
(* THE CHARACTERISTIC OF THE RING                                            *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of ring characteristic.                                        *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-char-def";;

let (num_to_ring_zero,num_to_ring_suc) =
    let def = new_recursive_definition num_RECURSION
          `(num_to_ring 0 = ring_zero) /\
           (!n. num_to_ring (SUC n) = ring_add ring_one (num_to_ring n))` in
    CONJ_PAIR def;;

(*PARAMETRIC
new_constant ("num_to_ring", `:num -> ring`);;
*)

export_thm num_to_ring_zero;;
export_thm num_to_ring_suc;;

(*PARAMETRIC
let num_to_ring_zero = new_axiom
  `num_to_ring 0 = ring_zero`;;

let num_to_ring_suc = new_axiom
  `!n. num_to_ring (SUC n) = ring_add ring_one (num_to_ring n)`;;
*)

(*BEGIN-PARAMETRIC*)
let num_to_ring_def = CONJ num_to_ring_zero num_to_ring_suc;;
(*END-PARAMETRIC*)

let ring_char_def = new_definition
  `ring_char =
   if (?n. ~(n = 0) /\ num_to_ring n = ring_zero) then
     (minimal n. ~(n = 0) /\ num_to_ring n = ring_zero)
   else 0`;;

export_thm ring_char_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of ring characteristic.                                        *)
(* ------------------------------------------------------------------------- *)

export_theory "ring-char-thm";;

let num_to_ring_char = prove
  (`num_to_ring ring_char = ring_zero`,
   REWRITE_TAC [ring_char_def] THEN
   COND_CASES_TAC THENL
   [POP_ASSUM (MP_TAC o REWRITE_RULE [MINIMAL]) THEN
    SPEC_TAC
      (`minimal n. ~(n = 0) /\ num_to_ring n = ring_zero`, `n : num`) THEN
    REPEAT STRIP_TAC;
    ACCEPT_TAC num_to_ring_zero]);;

export_thm num_to_ring_char;;

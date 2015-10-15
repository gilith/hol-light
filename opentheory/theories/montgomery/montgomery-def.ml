(* ========================================================================= *)
(* DEFINITION OF MONTGOMERY MULTIPLICATION                                   *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "montgomery-def";;

(* ------------------------------------------------------------------------- *)
(* Definition of Montgomery multiplication [1].                              *)
(*                                                                           *)
(* 1. http://en.wikipedia.org/wiki/Montgomery_reduction                      *)
(* ------------------------------------------------------------------------- *)

let montgomery_reduce_def = new_definition
  `!n r k a.
     montgomery_reduce n r k a =
     (a + ((a * k) MOD r) * n) DIV r`;;

export_thm montgomery_reduce_def;;

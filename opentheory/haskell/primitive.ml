(* ========================================================================= *)
(* OPENTHEORY HASKELL PRIMITIVES                                             *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of the Haskell primitives.                                     *)
(* ------------------------------------------------------------------------- *)

logfile "haskell-primitive";;

(* Numbers *)

let equal_numH_def = new_definition
  `(equal_numH : num -> num -> bool) = (=)`;;

export_thm equal_numH_def;;

logfile_end ();;

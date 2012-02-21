(* ========================================================================= *)
(* ADDITIONS TO THE HOL LIGHT STANDARD THEORY LIBRARY                        *)
(* Joe Hurd                                                                  *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Useful tactics.                                                           *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/stdlib/tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Options.                                                                  *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/stdlib/option.ml";;

(* ------------------------------------------------------------------------- *)
(* Lists.                                                                    *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/stdlib/list.ml";;

(* ------------------------------------------------------------------------- *)
(* Stop proof logging.                                                       *)
(* ------------------------------------------------------------------------- *)

stop_logging ();;

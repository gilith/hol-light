(* ------------------------------------------------------------------------- *)
(* OpenTheory example theories.                                              *)
(* ------------------------------------------------------------------------- *)

start_logging ();;

(* Natural number division *)
loads "opentheory/examples/divides.ml";;
loads "opentheory/examples/gcd.ml";;
loads "opentheory/examples/prime.ml";;

(* Modular arithmetic *)
loads "opentheory/examples/modular.ml";;

(* Finite fields GF(p) *)
loads "opentheory/examples/gfp.ml";;

(* Bit-vectors *)
loads "opentheory/examples/word.ml";;
loads "opentheory/examples/byte.ml";;
loads "opentheory/examples/word10.ml";;
loads "opentheory/examples/word12.ml";;
loads "opentheory/examples/word16.ml";;

(* Simple stream parsers *)
loads "opentheory/examples/parser.ml";;
loads "opentheory/examples/char.ml";;

(* Memory safety for the H interface *)
loads "opentheory/examples/h.ml";;

stop_logging ();;

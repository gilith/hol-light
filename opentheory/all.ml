(* ========================================================================= *)
(* LOAD REGULAR AND OPENTHEORY THEORIES                                      *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* The HOL Light implementation of the standard theory library.              *)
(* ------------------------------------------------------------------------- *)

#use "hol.ml";;

(* ------------------------------------------------------------------------- *)
(* Additional OpenTheory theories.                                           *)
(* ------------------------------------------------------------------------- *)

loads "opentheory/theories/all.ml";;

(* ------------------------------------------------------------------------- *)
(* Update the theorem database.                                              *)
(* ------------------------------------------------------------------------- *)

update_database ();;

(* ------------------------------------------------------------------------- *)
(* Output the loaded files.                                                  *)
(* ------------------------------------------------------------------------- *)

let () =
    let h = open_out ("opentheory/files") in
    let output_filename f = output_string h (f ^ "\n") in
    let () = List.iter output_filename (rev (!loaded_filenames)) in
    let () = close_out h in
    ();;

(* ------------------------------------------------------------------------- *)
(* Test theory.                                                              *)
(* ------------------------------------------------------------------------- *)

(*
#use "opentheory/test.ml";;
*)

(* ------------------------------------------------------------------------- *)
(* Testing article import.                                                   *)
(* ------------------------------------------------------------------------- *)

(*
logfile "test-import-1";

extend_the_interpretation
  "opentheory/theories/natural-divides/natural-divides.int";;
import_article "natural-divides.art";;

extend_the_interpretation
  "opentheory/theories/stream/stream.int";;
import_article "stream.art";;

extend_the_interpretation
  "opentheory/theories/natural-prime/natural-prime.int";;
import_article "natural-prime.art";;
*)

(*
logfile "test-import-2";

extend_the_interpretation
  "opentheory/theories/stream/stream.int";;
import_article "stream.art";;

extend_the_interpretation
  "opentheory/theories/probability/probability.int";;
import_article "probability.art";;

extend_the_interpretation
  "opentheory/theories/natural-bits/natural-bits.int";;
import_article "natural-bits.art";;

extend_the_interpretation
  "opentheory/theories/natural-divides/natural-divides.int";;
import_article "natural-divides.art";;

extend_the_interpretation
  "opentheory/theories/modular/modular.int";;
extend_the_interpretation
  "opentheory/theories/word/word.int";;
extend_the_interpretation
  "opentheory/theories/word10/word10.int";;
import_article "word10.art";;
*)

(* ------------------------------------------------------------------------- *)
(* Stop proof logging (and emit theories).                                   *)
(* ------------------------------------------------------------------------- *)

stop_logging ();;

start_logging ();;

(* ------------------------------------------------------------------------- *)
(* A type of bytes.                                                          *)
(* ------------------------------------------------------------------------- *)

logfile "byte";;

let byte_INDUCT,byte_RECURSION = define_type
 "byte = BYTE bool bool bool bool bool bool bool bool";;

export_thm byte_INDUCT;;
export_thm byte_RECURSION;;

logfile_end ();;

stop_logging ();;

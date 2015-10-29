(* ========================================================================= *)
(* PROOF TOOLS FOR 16-BIT WORDS                                              *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Requirements.                                                             *)
(* ------------------------------------------------------------------------- *)

needs "opentheory/theories/tools.ml";;
needs "opentheory/theories/byte/byte-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Instantiated parametric proof tools from the word theory                  *)
(* ------------------------------------------------------------------------- *)

needs "opentheory/theories/word16/word16-word-tools.ml";;

(* ------------------------------------------------------------------------- *)
(* Proof tools for 16-bit word to byte pair conversions.                     *)
(* ------------------------------------------------------------------------- *)

let bytes_to_word16_list_conv =
    let th = SYM (SPECL [`list_to_byte l0`; `list_to_byte l1`]
                    bytes_to_word16_list) in
    REWR_CONV th THENC
    RAND_CONV
      (LAND_CONV list_to_byte_to_list_conv THENC
       RAND_CONV list_to_byte_to_list_conv THENC
       append_conv);;

let word16_to_bytes_list_conv =
    let th = SYM (SPEC `list_to_word16 l` word16_to_bytes_list) in
    REWR_CONV th THENC
    (LAND_CONV o RAND_CONV)
      (RAND_CONV list_to_word16_to_list_conv THENC
       take_conv) THENC
    (RAND_CONV o RAND_CONV)
      (RAND_CONV list_to_word16_to_list_conv THENC
       drop_conv);;

let word16_bytes_conv =
    bytes_to_word16_list_conv ORELSEC
    word16_to_bytes_list_conv;;

let bit_blast_subterm_conv = word16_bytes_conv ORELSEC bit_blast_subterm_conv;;
let bit_blast_conv = DEPTH_CONV bit_blast_subterm_conv;;  (* word16-bytes *)
let bit_blast_tac = CONV_TAC bit_blast_conv;;  (* word16-bytes *)

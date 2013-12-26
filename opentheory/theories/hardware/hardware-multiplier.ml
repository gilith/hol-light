(* ========================================================================= *)
(* HARDWARE MULTIPLIER DEVICES                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-def";;

(***
let sum_carry_mult_def = new_definition
  `!ld w xs xc ys yc.
     sum_carry_mult ld w xs xc ys yc <=>
     ?r sp sq sr cp cq cr s0 s1 sq0 sq1 sq2 sq3 cp0 cp1 cq0 cq1.
       width s = r + 1 /\
       width c = r + 1 /\
       width sp = r /\
       width sq = r + 1 /\
       width sr = r /\
       width cp = r + 1 /\
       width cq = r + 1 /\
       width cr = r + 1
       /\
       wire s 0 s0 /\
       bsub s 1 r s1 /\
       wire sq 0 sq0 /\
       bsub sq 0 r sq1 /\
       bsub sq 1 r sq2 /\
       wire sq r sq3 /\
       bsub cp 0 r cp0 /\
       wire cp r cp1 /\
       bsub cq 0 r cq0 /\
       wire cq r cq1
       /\
       badder2 sp cp0 sq1 cq0 /\
       connect cp1 sq3 /\
       connect ground cq1 /\
       case1 ld s0 sq0 w /\
       bcase1 ld s1 sq2 sr /\
       bcase1 ld c cq cr /\
       bdelay sr sp /\
       bdelay cr cp`;;

export_thm sum_carry_bit_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-thm";;


logfile_end ();;

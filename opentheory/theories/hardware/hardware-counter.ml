(* ========================================================================= *)
(* COUNTER DEVICES                                                           *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of counter devices.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-counter-def";;

let icounter_def = new_definition
  `!ld nb inc dn.
      icounter ld nb inc dn <=>
      ?r sp sp0 sp1 cp cp0 cp1 cp2 sq sq0 sq1 cq cq0 cq1 sr cr dp dq.
         width nb = r + 1 /\
         width sp = r + 1 /\
         width cp = r + 1 /\
         width sq = r + 1 /\
         width cq = r + 1 /\
         width sr = r + 1 /\
         width cr = r + 1
         /\
         wire sp 0 sp0 /\
         bsub sp 1 r sp1 /\
         wire sq 0 sq0 /\
         bsub sq 1 r sq1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1
         /\
         xor2 inc sp0 sq0 /\
         and2 inc sp0 cq0 /\
         badder2 sp1 cp1 sq1 cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb sq sr /\
         bcase1 ld (bground (r + 1)) cq cr /\
         case1 ld ground dq dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn dp`;;

export_thm icounter_def;;

let counter_def = new_definition
  `!ld nb dn.
      counter ld nb dn <=>
      ?r nb0 nb1 sp cp cp0 cp1 cp2 sq cq cq0 cq1 sr cr cr0 cr1 dp dq.
         width nb = r + 1 /\
         width sp = r /\
         width cp = r + 1 /\
         width sq = r /\
         width cq = r + 1 /\
         width sr = r /\
         width cr = r + 1
         /\
         wire nb 0 nb0 /\
         bsub nb 1 r nb1 /\
         wire cp 0 cp0 /\
         bsub cp 0 r cp1 /\
         wire cp r cp2 /\
         wire cq 0 cq0 /\
         bsub cq 1 r cq1 /\
         wire cr 0 cr0 /\
         bsub cr 1 r cr1
         /\
         not cp0 cq0 /\
         badder2 sp cp1 sq cq1 /\
         or2 dp cp2 dq
         /\
         bcase1 ld nb1 sq sr /\
         case1 ld nb0 cq0 cr0 /\
         bcase1 ld (bground r) cq1 cr1 /\
         case1 ld ground dq dn
         /\
         bdelay sr sp /\
         bdelay cr cp /\
         delay dn dp`;;

export_thm counter_def;;

(* ------------------------------------------------------------------------- *)
(* Properties of counter devices.                                            *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-counter-thm";;


logfile_end ();;

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
  `!ld w xs xc sa ca sb cb.
     sum_carry_mult ld w xs xc sa ca sb cb <=>
     ?r sap cap sbp cbp xos xoc sbq cbq
      sa0 sa1 ca0 ca1 sb1 cap0 cap1 cbp0 cbp1
      xos0 xos1 xoc0 xoc1 sbq0 sbq1 cbq0 cbq1.
       width xs = r + 1 /\
       width xc = r + 1 /\
       width sa = r + 1 /\
       width ca = r + 1 /\
       width sb = r + 1 /\
       width cb = r + 1 /\
       width sap = r /\
       width cap = r + 1 /\
       width sbp = r /\
       width cbp = r + 1 /\
       width xos = r + 1 /\
       width xoc = r + 1 /\
       width sbq = r + 1 /\
       width cbq = r + 1
       /\
       wire sa 0 sa0 /\
       bsub sa 1 r sa1 /\
       wire ca 0 ca0 /\
       bsub ca 1 r ca1 /\
       bsub sb 1 r sb1 /\
       wire cap 0 cap0 /\
       bsub cap 1 r cap1 /\
       bsub cbp 0 r cbp0 /\
       wire cbp r cbp1 /\
       wire xos 0 xos0 /\
       bsub xos 1 r xos1 /\
       bsub xoc 0 r xoc0 /\
       wire xoc r xoc1 /\
       bsub sbq 0 r sbq0 /\
       wire sbq r sbq1 /\
       bsub cbq 0 r cbq0 /\
       wire cbq r cbq1
       /\
       bcase1 w xs (bground (r + 1)) xos /\
       bcase1 w xc (bground (r + 1)) xoc /\
       adder2 xos0 cap0 sa0 ca0 /\
       badder3 xos1 xoc0 cap1 sa1 ca1 /\
       badder3 sap sbp cbp0 sbq0 cbq0 /\
       connect xoc1 cbq1 /\
       connect cbp1 sbq1 /\
       bcase1 ld (bground (r + 1)) sbq sb /\
       bcase1 ld (bground (r + 1)) cbq cb /\
       bdelay sa1 sap /\
       bdelay ca cap /\
       bdelay sb1 sbp /\
       bdelay cb cbp`;;

export_thm sum_carry_mult_def;;
***)

(* ------------------------------------------------------------------------- *)
(* Properties of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-thm";;

(***
let sum_carry_mult_zero = prove
 (`!ld w xs xc sa ca sb cb t.
     ~signal w t /\
     ~signal w (t + 1) /\
     sum_carry_mult ld w xs xc sa ca sb cb ==>
     bsignal sa (t + 1) = 
     (!i. i <= k ==> (signal ld (t + i) <=> i = 0)) /\
     bits_to_num (bsignal s t) + 2 * bits_to_num (bsignal c t) = n /\
     sum_carry_bit ld s c w ==>
     signal w (t + k) = bit_nth n k`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC [sum_carry_bit_def] THEN
***)

logfile_end ();;

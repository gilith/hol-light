(* ========================================================================= *)
(* HARDWARE MULTIPLIER DEVICES                                               *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Definition of hardware multiplier devices.                                *)
(* ------------------------------------------------------------------------- *)

logfile "hardware-multiplier-def";;

(* -------------------------------------- *)
(*       r+2 r+1  r  r-1  ...  2   1   0  *)
(* -------------------------------------- *)
(*  xs =  -   -   p   p   ...  p   p   op *)
(*  xc =  -   o   o   o   ...  o   o   -  *)
(*  sp =  -   -   p   p   ...  p   p   op *)
(*  cp =  -   o   p   p   ...  p   p   -  *)
(* -------------------------------------- *)
(*  ps =  -   -   o   o   ...  o   o   -  *)
(*  pc =  -   o   o   o   ...  o   o   -  *)
(* -------------------------------------- *)
(*  s  =  -   X   X   X   ...  X   X   X  *)
(*  c  =  X   X   X   X   ...  X   -   -  *)
(* -------------------------------------- *)

(***
let sum_carry_mult_def = new_definition
  `!ld w xs xc s c.
     sum_carry_mult ld w xs xc s c <=>
     ?r sp cp xos xoc ps pc sq cq
      s0 sp0 sp1 cp0 cp1 xos0 xos1 xoc0 xoc1 pc0 pc1 pc2 pc3 sq0 sq1 sq2 cq0 cq1.
       width xs = r + 1 /\
       width xc = r + 1 /\
       width s = r + 2 /\
       width c = r + 1 /\
       width sp = r + 1 /\
       width cp = r + 1 /\
       width xos = r + 1 /\
       width xoc = r + 1 /\
       width ps = r /\
       width pc = r + 1 /\
       width sq = r + 2 /\
       width cq = r + 1
       /\
       bsub s 1 (r + 1) s0 /\
       wire sp 0 sp0 /\
       bsub sp 1 r sp1 /\
       bsub cp 0 r cp0 /\
       wire cp r cp1 /\
       wire xos 0 xos0 /\
       bsub xos 1 r xos1 /\
       bsub xoc 0 r xoc0 /\
       wire xoc r xoc1 /\
       wire pc 0 pc0 /\
       bsub pc 0 r pc1 /\
       bsub pc 1 r pc2 /\
       wire pc r pc3 /\
       wire sq 0 sq0 /\
       bsub sq 1 r sq1 /\
       wire sq (r + 1) sq2 /\
       bsub cq 0 r cq0 /\
       wire cq r cq1
       /\
       bcase1 w xs (bground (r + 1)) xos /\
       bcase1 w xc (bground (r + 1)) xoc /\
       adder2 sp0 xos0 sq0 pc0 /\
       badder3 sp1 cp0 xos1 ps pc2 /\
       badder3 xoc0 ps pc1 sq1 cq0 /\
       adder3 xoc1 cp1 pc3 sq2 cq1 /\
       bcase1 ld (bground (r + 2)) sq s /\
       bcase1 ld (bground (r + 1)) cq c /\
       bdelay s0 sp /\
       bdelay c cp`;;

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

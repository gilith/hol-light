(* ========================================================================= *)
(* DEFINITION OF A MONTGOMERY MULTIPLICATION CIRCUIT                         *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

export_theory "montgomery-hardware-def";;

(* -------------------------------------------------------------- *)
(* Montgomery multiplication modulo 2^(r+2), where d = d1 + d2    *)
(* -------------------------------------------------------------- *)
(*        r+3 r+2 r+1  r  r-1 r-2 ... d+1  d  d-1 ...  2   1   0  *)
(* -------------------------------------------------------------- *)
(*  xs  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  xc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ys  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(*  yc  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ks  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  kc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(*  ns  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  nc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  pb  =  -   -   -   -   -   -  ...  -   -   X  ...  X   X   X  *)
(*  ps  =  -   -   X   X   X   X  ...  X   X   -  ...  -   -   -  *)
(*  pc  =  -   -   X   X   X   X  ...  X   -   -  ...  -   -   -  *)
(* -------------------------------------------------------------- *)
(*  vs  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  vc  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  vt  =  -   -   -   -   -   -  ...  -   -   -  ...  -   -   X  *)
(* -------------------------------------------------------------- *)
(*  sa  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  sb  =  -   -   X   X   X   X  ...  X   -   -  ...  -   -   -  *)
(*  sc  =  -   -   -   -   -   X  ...  X   X   X  ...  X   X   X  *)
(*  sd  =  -   -   -   -   X   X  ...  X   X   X  ...  X   X   X  *)
(* -------------------------------------------------------------- *)
(*  ms  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  mc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)
(*  zs  =  -   -   -   X   X   X  ...  X   X   X  ...  X   X   X  *)
(*  zc  =  -   -   X   X   X   X  ...  X   X   X  ...  X   X   -  *)
(* -------------------------------------------------------------- *)

let montgomery_mult_reduce_def = new_definition
  `!ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc.
     montgomery_mult_reduce ld xs xc d0 ys yc d1 ks kc d2 ns nc zs zc <=>
     ?r pb ps pc pbp qb qs qc vb vs vc vt sa sb sc sd ms mc
      ld1 ld2 zs0 zs1 zs2 zc0 zc1 zc2 zc3 ps0 pc0 pb1 pbp0 pbp1 qb2
      sa0 sa1 sa2 sa3 sa4 sa5 sb0 sb1 sb2 sd0 sd1 sd2 sd3
      ms0 ms1 ms2 ms3 ms4 mc0 mc1 mc2 mc3 mc4 mw.
       width xs = d1 + d2 + r + 2 /\
       width xc = d1 + d2 + r + 2 /\
       width ys = d1 + d2 + r + 2 /\
       width yc = d1 + d2 + r + 2 /\
       width ks = d1 + d2 + r + 3 /\
       width kc = d1 + d2 + r + 3 /\
       width ns = d1 + d2 + r + 1 /\
       width nc = d1 + d2 + r + 1 /\
       width zs = d1 + d2 + r + 3 /\
       width zc = d1 + d2 + r + 3 /\
       width ps = d1 + d2 + r + 2 /\
       width pc = d1 + d2 + r + 2 /\
       width pbp = d1 + d2 + 1 /\
       width qs = d1 + d2 + r + 3 /\
       width qc = d1 + d2 + r + 3 /\
       width vs = d1 + d2 + r + 1 /\
       width vc = d1 + d2 + r + 1 /\
       width sa = d1 + d2 + r + 4 /\
       width sb = r + 3 /\
       width sc = d1 + d2 + r + 1 /\
       width sd = d1 + d2 + r + 2 /\
       width ms = d1 + d2 + r + 3 /\
       width mc = d1 + d2 + r + 3
       /\
       bsub zs 0 (d1 + d2 + 1) zs0 /\
       bsub zs (d1 + d2 + 1) (r + 1) zs1 /\
       wire zs (d1 + d2 + r + 2)  zs2 /\
       bsub zc 0 (d1 + d2) zc0 /\
       wire zc (d1 + d2) zc1 /\
       bsub zc (d1 + d2 + 1) (r + 1) zc2 /\
       wire zc (d1 + d2 + r + 2) zc3 /\
       bsub ps 0 (r + 4) ps0 /\
       bsub pc 0 (r + 3) pc0 /\
       wire pbp d1 pb1 /\
       bsub pbp 1 (d1 + d2) pbp0 /\
       brev pbp0 pbp1 /\
       bsub sa 0 (d1 + d2) sa0 /\
       bsub sa 0 (d1 + d2 + r + 1) sa1 /\
       bsub sa (d1 + d2) (r + 4) sa2 /\
       wire sa (d1 + d2 + r + 1) sa3 /\
       wire sa (d1 + d2 + r + 2) sa4 /\
       wire sa (d1 + d2 + r + 3) sa5 /\
       bsub sb 0 (r + 1) sb0 /\
       wire sb (r + 1) sb1 /\
       wire sb (r + 2) sb2 /\
       wire sd 0 sd0 /\
       bsub sd 0 (d1 + d2 + r + 1) sd1 /\
       bsub sd 1 (d1 + d2 + r + 1) sd2 /\
       wire sd (d1 + d2 + r + 1) sd3 /\
       bsub ms 0 (d1 + d2 + 1) ms0 /\
       bsub ms 0 (d1 + d2 + r + 1) ms1 /\
       bsub ms (d1 + d2 + 1) (r + 1) ms4 /\
       wire ms (d1 + d2 + r + 1) ms2 /\
       wire ms (d1 + d2 + r + 2) ms3 /\
       bsub mc 0 (d1 + d2) mc0 /\
       bsub mc 0 (d1 + d2 + r + 1) mc1 /\
       bsub mc (d1 + d2) (r + 1) mc2 /\
       wire mc (d1 + d2 + r + 1) mc3 /\
       wire mc (d1 + d2 + r + 2) mc4
       /\
       scmult ld xs xc d0 ys yc pb ps pc /\
       pipe ld (d0 + d1) ld1 /\
       bpipe pb pbp /\
       bmult ld1 pb1 ks kc qb qs qc /\
       pipe ld1 d2 ld2 /\
       pipe qb d2 qb2 /\
       bmult ld2 qb2 ns nc vb vs vc /\
       sticky ld2 vb vt /\
       bconnect pbp1 sa0 /\
       badder3 sa1 sc sd1 ms1 mc1 /\
       adder2 sa3 sd3 ms2 mc3 /\
       connect sa4 ms3 /\
       connect sa5 mc4 /\
       bconnect ms0 zs0 /\
       bconnect mc0 zc0 /\
       connect ground zc1 /\
       badder3 sb0 ms4 mc2 zs1 zc2 /\
       adder3 sb1 ms3 mc3 zs2 mw /\
       or3 sb2 mc4 mw zc3
       /\
       bdelay ps0 sa2 /\
       bdelay pc0 sb /\
       bdelay vs sc /\
       delay vt sd0 /\
       bdelay vc sd2`;;

export_thm montgomery_mult_reduce_def;;

(* --------------------------------------------- *)
(* Compress the Montgomery multiplication result *)
(* --------------------------------------------- *)
(*        r+2 r+1  r  ...  1   0                 *)
(* --------------------------------------------- *)
(*  xs  =  -   X   X  ...  X   X                 *)
(*  xc  =  X   X   X  ...  X   -                 *)
(*  rx  =  -   -   X  ...  X   X                 *)
(*  ry  =  -   -   X  ...  X   X                 *)
(*  rz  =  -   -   X  ...  X   X                 *)
(* --------------------------------------------- *)
(*  ns  =  -   X   -  ...  -   -                 *)
(*  nc  =  X   -   -  ...  -   -                 *)
(* --------------------------------------------- *)
(*  ys  =  -   -   X  ...  X   X                 *)
(*  yc  =  -   X   X  ...  X   -                 *)
(* --------------------------------------------- *)

let montgomery_mult_compress_def = new_definition
  `!xs xc d rx ry rz ys yc.
      montgomery_mult_compress xs xc d rx ry rz ys yc <=>
      ?r nct ns nc nsd ncd rnl rnh rn
       xs0 xs1 xs2 xc0 xc1 xc2 ys0 ys1 yc0 yc1 rn0 rn1.
         width xs = r + 2 /\
         width xc = r + 2 /\
         width rx = r + 1 /\
         width ry = r + 1 /\
         width rz = r + 1 /\
         width ys = r + 1 /\
         width yc = r + 1 /\
         width rnl = r + 1 /\
         width rnh = r + 1 /\
         width rn = r + 1
         /\
         wire xs 0 xs0 /\
         bsub xs 1 r xs1 /\
         wire xs (r + 1) xs2 /\
         bsub xc 0 r xc0 /\
         wire xc r xc1 /\
         wire xc (r + 1) xc2 /\
         wire ys 0 ys0 /\
         bsub ys 1 r ys1 /\
         wire yc 0 yc0 /\
         bsub yc 1 r yc1 /\
         wire rn 0 rn0 /\
         bsub rn 1 r rn1
         /\
         adder2 xs2 xc1 ns nct /\
         or2 nct xc2 nc /\
         pipe ns d nsd /\
         pipe nc d ncd /\
         bcase1 nsd rx (bground (r + 1)) rnl /\
         bcase1 nsd rz ry rnh /\
         bcase1 ncd rnh rnl rn /\
         adder2 xs0 rn0 ys0 yc0 /\
         badder3 xs1 xc0 rn1 ys1 yc1`;;

export_thm montgomery_mult_compress_def;;

(* --------------------------------------------------------------------- *)
(* Montgomery multiplication is simply reduction followed by compression *)
(* --------------------------------------------------------------------- *)

let montgomery_mult_def = new_definition
  `!ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc.
     montgomery_mult
       ld xs xc d0 ys yc d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn zs zc <=>
     ?r jp jpd ps pc qsp qcp qsr qcr.
        width xs = r + 1 /\
        width xc = r + 1 /\
        width ys = r + 1 /\
        width yc = r + 1 /\
        width ks = r + 2 /\
        width kc = r + 2 /\
        width ns = r /\
        width nc = r /\
        width rx = r + 1 /\
        width ry = r + 1 /\
        width rz = r + 1 /\
        width zs = r + 1 /\
        width zc = r + 1 /\
        width ps = r + 2 /\
        width pc = r + 2 /\
        width qsp = r + 2 /\
        width qcp = r + 2 /\
        width qsr = r + 2 /\
        width qcr = r + 2
        /\
        montgomery_mult_reduce ld xs xc d0 ys yc d1 ks kc d2 ns nc ps pc /\
        counter_pulse ld jb jp /\
        pipe jp d3 jpd /\
        bcase1 jpd ps qsp qsr /\
        bcase1 jpd pc qcp qcr /\
        connect jp dn /\
        montgomery_mult_compress qsp qcp d4 rx ry rz zs zc
        /\
        bdelay qsr qsp /\
        bdelay qcr qcp`;;

export_thm montgomery_mult_def;;

(* --------------------------------------------------------------------- *)
(* Double exponentiation using Montgomery multiplication                 *)
(* --------------------------------------------------------------------- *)
(* This circuit implements a controller with the following 4 states:     *)
(* --------------------------------------------------------------------- *)
(* (sb,sa)  description                                                  *)
(* --------------------------------------------------------------------- *)
(* reset    The circuit assumes this state whenever ld is true.          *)
(* (1,1)    In this state the internal register is loaded from the xs/xc *)
(*          input wires, and both counters and the Montgomery multiplier *)
(*          are reset.                                                   *)
(*          When ld becomes false the state changes to compute.          *)
(* --------------------------------------------------------------------- *)
(* compute  In this state the Montgomery multiplier is computing with    *)
(* (1,0)    both inputs wired to the internal register.                  *)
(*          When the counter becomes true the state changes to round.    *)
(* --------------------------------------------------------------------- *)
(* round    This state lasts for one cycle, and in it the event counter  *)
(* (0,1)    is incremented, the counter and Montgomery multiplier are    *)
(*          reset, and the computed result is copied to the internal     *)
(*          register.                                                    *)
(*          On the next cycle the state either changes to compute (if    *)
(*          the event counter is false) or done (if the event counter is *)
(*          true).                                                       *)
(* --------------------------------------------------------------------- *)
(* done     In this state the dn output wire is set to true, and the     *)
(* (0,0)    result can be read from the ys/yc output wires (which are    *)
(*          wired to the internal register).                             *)
(* --------------------------------------------------------------------- *)

let montgomery_double_exp_def = new_definition
  `!ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc.
     montgomery_double_exp
       ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc <=>
     ?r sa sb jp ps pc qs qc
      sad sadd san sap saq sar sbd sbdd sbp sbq sbr srdd
      jpn psq psr pcq pcr md mdn.
        width xs = r + 1 /\
        width xc = r + 1 /\
        width ks = r + 2 /\
        width kc = r + 2 /\
        width ns = r /\
        width nc = r /\
        width rx = r + 1 /\
        width ry = r + 1 /\
        width rz = r + 1 /\
        width ys = r + 1 /\
        width yc = r + 1 /\
        width ps = r + 1 /\
        width pc = r + 1 /\
        width qs = r + 1 /\
        width qc = r + 1 /\
        width psq = r + 1 /\
        width psr = r + 1 /\
        width pcq = r + 1 /\
        width pcr = r + 1
        /\
        not jp jpn /\
        not md mdn /\
        not sa san /\
        and2 sb jp sap /\
        and2 san sap saq /\
        or2 ld saq sar /\
        and2 sa mdn sbp /\
        case1 sb jpn sbp sbq /\
        or2 ld sbq sbr /\
        pipe sa (d3 + d4) sad /\
        delay sad sadd /\
        pipe sb (d3 + d4) sbd /\
        delay sbd sbdd /\
        and2 sadd sbdd srdd /\
        event_counter srdd mb sadd md /\
        montgomery_mult
          sadd ps pc d0 ps pc d1 ks kc d2 ns nc jb d3 d4 rx ry rz jp qs qc /\
        bcase1 sbd xs qs psq /\
        bcase1 sad psq ps psr /\
        bcase1 sbd xc qc pcq /\
        bcase1 sad pcq pc pcr /\
        nor2 sad sbd dn /\
        bconnect ps ys /\
        bconnect pc yc
        /\
        delay sar sa /\
        delay sbr sb /\
        bdelay psr ps /\
        bdelay pcr pc`;;

export_thm montgomery_double_exp_def;;

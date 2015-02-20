(* ========================================================================= *)
(* AUTOMATICALLY SYNTHESIZING MONTGOMERY MULTIPLICATION CIRCUITS             *)
(* Joe Leslie-Hurd                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* Synthesizing Montgomery multiplication reduction circuits.                *)
(* ------------------------------------------------------------------------- *)

let montgomery_mult_reduce_syn_gen n =
    setify
      ((n,montgomery_mult_reduce_def) ::
       scmult_syn @
       pipe_syn @
       bpipe_syn @
       bmult_syn @
       sticky_syn @
       badder3_syn @
       adder2_syn @
       adder3_syn @
       or3_syn);;

let montgomery_mult_reduce_syn = montgomery_mult_reduce_syn_gen "reduce";;

let synthesize_montgomery_mult_reduce n =
    let nn = mk_numeral n in
    let r_th = bit_width_conv (mk_comb (`bit_width`,nn)) in
    let rn = rand (concl r_th) in
    let r = dest_numeral rn in
    let r1 = add_num r num_1 in
    let (d0,d1,d2) =
        let d = add_num (quo_num (bit_width_num r) num_2) num_1 in
        let dn = mk_numeral d in
        (dn,dn,dn) in
    let ld = mk_var ("ld",wire_ty) in
    let xs = variable_bus "xs" r in
    let xc = variable_bus "xc" r in
    let ys = variable_bus "ys" r in
    let yc = variable_bus "yc" r in
    let zs = variable_bus "zs" r1 in
    let zc = variable_bus "zc" r1 in
    let egcd_th =
        let rtm =
            let tm0 = mk_comb (`(+) : num -> num -> num`, rn) in
            mk_comb (`(EXP) 2`, mk_comb (tm0, `2`)) in
        let rth = NUM_REDUCE_CONV rtm in
        let eth = prove_egcd (rhs (concl rth)) nn in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let sn = rand (lhs (concl egcd_th)) in
    let kn = lhand (lhand (rhs (concl egcd_th))) in
    let (ns,nc) =
        let r1 = sub_num r num_1 in
        let n1 = num_to_bitvec n r1 in
        let n2 = div_num (sub_num n (bits_to_num n1)) num_2 in
        (bits_to_bus n1, bits_to_bus (num_to_bitvec n2 r1)) in
    let k = dest_numeral kn in
    let (ks,kc) =
        let k1 = num_to_bitvec k r1 in
        let k2 = div_num (sub_num k (bits_to_num k1)) num_2 in
        (bits_to_bus k1, bits_to_bus (num_to_bitvec k2 r1)) in
    let fv_x = `x : num` in
    let fv_y = `y : num` in
    let fv_t = `t : cycle` in
    let th0 =
        SPECL
          [nn; rn; sn; kn; fv_x; fv_y; ld; xs; xc; d0; ys; yc; d1;
           ks; kc; d2; ns; nc; zs; zc; fv_t]
          montgomery_mult_reduce_bits_to_num in
    let th1 =
        let conv =
            REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th0 in
    let th2 =
        let conv =
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th1 in
    let th3 =
        let conv =
            LAND_CONV (REWR_CONV r_th) THENC
            REWR_CONV (EQT_INTRO (SPEC_ALL LE_REFL)) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th2 in
    let th4 =
        let conv =
            REWR_CONV (EQT_INTRO egcd_th) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th3 in
    let (ld_cond,th5) =
        let conv =
            RAND_CONV (ABS_CONV (LAND_CONV (RAND_CONV NUM_REDUCE_CONV))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th4) in
    let (x_cond,th6) =
        let conv = ALL_CONV in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th5) in
    let (y_cond,th7) =
        let conv =
            RAND_CONV
              (ABS_CONV (LAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th6) in
    let th8 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th7 in
    let th9 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th8 in
    let (ckt,th10) = undisch_bind th9 in
    let th11 =
        let conv =
            LAND_CONV
              (LAND_CONV
                 (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))) THENC
               RAND_CONV
                 (RAND_CONV
                    (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))))) THENC
            RAND_CONV
              (RATOR_CONV
                 (RATOR_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))) in
        CONV_RULE conv th10 in
    let th =
        (GEN fv_x o GEN fv_y o GEN fv_t o
         REWRITE_RULE [IMP_IMP; GSYM CONJ_ASSOC] o
         DISCH ld_cond o DISCH x_cond o DISCH y_cond) th11 in
    let syn = montgomery_mult_reduce_syn_gen "" in
    let primary = frees (concl th) in
    synthesize_hardware syn primary th;;

(* Testing
let montgomery_reduce_91_ckt = synthesize_montgomery_mult_reduce (dest_numeral `91`);;
let name = Verilog_module "montgomery_reduce_91";;
let comment = default_verilog_comment ();;
let primary = Verilog_primary (`clk : wire` :: frees_circuit montgomery_reduce_91_ckt);;
hardware_to_verilog_file name comment primary montgomery_reduce_91_ckt;;
*)

(* ------------------------------------------------------------------------- *)
(* Synthesizing Montgomery multiplication compression circuits.              *)
(* ------------------------------------------------------------------------- *)

let montgomery_mult_compress_syn =
    setify
      (("compress",montgomery_mult_compress_def) ::
       adder2_syn @
       pipe_syn @
       badder3_syn);;

(* ------------------------------------------------------------------------- *)
(* Synthesizing Montgomery multiplication circuits.                          *)
(* ------------------------------------------------------------------------- *)

let montgomery_mult_syn_gen n =
    setify
      ((n,montgomery_mult_def) ::
       montgomery_mult_reduce_syn @
       counter_pulse_syn @
       pipe_syn @
       montgomery_mult_compress_syn);;

let montgomery_mult_syn = montgomery_mult_syn_gen "multm";;

let synthesize_montgomery_mult n =
    let nn = mk_numeral n in
    let r_th = bit_width_conv (mk_comb (`bit_width`,nn)) in
    let rn = rand (concl r_th) in
    let r = dest_numeral rn in
    let (d0,d1,d2,d3,d4) =
        let d = add_num (quo_num (bit_width_num r) num_2) num_1 in
        (d,d,d,d,d) in
    let d0n = mk_numeral d0 in
    let d1n = mk_numeral d1 in
    let d2n = mk_numeral d2 in
    let d3n = mk_numeral d3 in
    let d4n = mk_numeral d4 in
    let ld = mk_var ("ld",wire_ty) in
    let xs = variable_bus "xs" r in
    let xc = variable_bus "xc" r in
    let ys = variable_bus "ys" r in
    let yc = variable_bus "yc" r in
    let dn = mk_var ("dn",wire_ty) in
    let zs = variable_bus "zs" r in
    let zc = variable_bus "zc" r in
    let egcd_th =
        let rtm =
            let tm0 = mk_comb (`(+) : num -> num -> num`, rn) in
            mk_comb (`(EXP) 2`, mk_comb (tm0, `2`)) in
        let rth = NUM_REDUCE_CONV rtm in
        let eth = prove_egcd (rhs (concl rth)) nn in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let sn = rand (lhs (concl egcd_th)) in
    let kn = lhand (lhand (rhs (concl egcd_th))) in
    let (ns,nc) =
        let r1 = sub_num r num_1 in
        let n1 = num_to_bitvec n r1 in
        let n2 = div_num (sub_num n (bits_to_num n1)) num_2 in
        (bits_to_bus n1, bits_to_bus (num_to_bitvec n2 r1)) in
    let k = dest_numeral kn in
    let (ks,kc) =
        let r1 = add_num r num_1 in
        let k1 = num_to_bitvec k r1 in
        let k2 = div_num (sub_num k (bits_to_num k1)) num_2 in
        (bits_to_bus k1, bits_to_bus (num_to_bitvec k2 r1)) in
    let jb =
        let jn = add_num d0 (add_num d1 (add_num d2 (add_num r num_1))) in
        mk_counter_arg (sub_num jn d3) in
    let rx_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            list_mk_comb (`(MOD)`, [tm0; nn]) in
        NUM_REDUCE_CONV tm in
    let rx =
        let n = dest_numeral (rhs (concl rx_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let ry_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            let tm1 = mk_comb (`( * ) 2`, tm0) in
            list_mk_comb (`(MOD)`, [tm1; nn]) in
        NUM_REDUCE_CONV tm in
    let ry =
        let n = dest_numeral (rhs (concl ry_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let rz_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            let tm1 = mk_comb (`( * ) 3`, tm0) in
            list_mk_comb (`(MOD)`, [tm1; nn]) in
        NUM_REDUCE_CONV tm in
    let rz =
        let n = dest_numeral (rhs (concl rz_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let fv_x = `x : num` in
    let fv_y = `y : num` in
    let fv_t = `t : cycle` in
    let th0 =
        SPECL
          [nn; rn; sn; kn; fv_x; fv_y; ld; xs; xc; d0n; ys; yc; d1n;
           ks; kc; d2n; ns; nc; jb; d3n; d4n; rx; ry; rz; dn; zs; zc; fv_t]
          montgomery_mult_bits_to_num in
    let th1 =
        let conv =
            REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th0 in
    let th2 =
        let conv =
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th1 in
    let th3 =
        let conv =
            LAND_CONV (REWR_CONV r_th) THENC
            REWR_CONV (EQT_INTRO (SPEC_ALL LE_REFL)) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th2 in
    let th4 =
        let conv =
            REWR_CONV (EQT_INTRO egcd_th) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th3 in
    let th5 =
        let conv =
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th4 in
    let (ld_cond,th6) =
        let conv =
            RAND_CONV (ABS_CONV (LAND_CONV (RAND_CONV NUM_REDUCE_CONV))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th5) in
    let (x_cond,th7) =
        let conv = ALL_CONV in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th6) in
    let (y_cond,th8) =
        let conv =
            RAND_CONV
              (ABS_CONV (LAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))) in
        undisch_bind
          (CONV_RULE
             (LAND_CONV (LAND_CONV conv) THENC
              REWR_CONV IMP_CONJ) th7) in
    let th9 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th8 in
    let th10 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv =
            RAND_CONV (ABS_CONV (RAND_CONV bits_conv)) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th9 in
    let th11 =
        let bits_conv =
            REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv = bits_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th10 in
    let th12 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv = RAND_CONV (REWR_CONV rx_th) THENC bits_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th11 in
    let th13 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv = RAND_CONV (REWR_CONV ry_th) THENC bits_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th12 in
    let th14 =
        let bits_conv =
            REWRITE_CONV
              [bnil_bsignal; bwire_bsignal; bappend_bsignal;
               ground_signal; power_signal; APPEND_SING;
               bits_to_num_cons; bits_to_num_nil;
               bit_cons_true; bit_cons_false] THENC
            NUM_REDUCE_CONV in
        let conv = RAND_CONV (REWR_CONV rz_th) THENC bits_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th13 in
    let (ckt,th15) = undisch_bind th14 in
    let th16 =
        let conv =
            LAND_CONV
              (LAND_CONV
                 (LAND_CONV
                    (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV))) THENC
                  RAND_CONV
                    (RAND_CONV
                       (RAND_CONV (RAND_CONV (RAND_CONV NUM_REDUCE_CONV)))))) in
        CONV_RULE conv th15 in
    let th =
        (GEN fv_x o GEN fv_y o GEN fv_t o
         REWRITE_RULE [IMP_IMP; GSYM CONJ_ASSOC] o
         DISCH ld_cond o DISCH x_cond o DISCH y_cond) th16 in
    let syn = montgomery_mult_syn_gen "" in
    let primary = frees (concl th) in
    synthesize_hardware syn primary th;;

(* Testing
let montgomery_91_ckt = synthesize_montgomery_mult (dest_numeral `91`);;
let name = Verilog_module "montgomery_91";;
let comment = default_verilog_comment ();;
let primary = Verilog_primary (`clk : wire` :: frees_circuit montgomery_91_ckt);;
hardware_to_verilog_file name comment primary montgomery_91_ckt;;
*)

(* ------------------------------------------------------------------------- *)
(* Synthesizing double exponentiation circuits.                              *)
(* ------------------------------------------------------------------------- *)

let montgomery_double_exp_syn_gen n =
    setify
      ((n,montgomery_double_exp_def) ::
       nor2_syn @
       pipe_syn @
       event_counter_syn @
       counter_pulse_syn @
       montgomery_mult_syn);;

let montgomery_double_exp_syn = montgomery_double_exp_syn_gen "dexp2m";;

let montgomery_double_exp_syn_spec = prove
 (`!n r s k m x ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc
    t l.
     width xs = r /\
     bit_width n <= r /\
     2 EXP (r + 2) * s = k * n + 1 /\
     d3 <= d0 + d1 + d2 + r + 1 /\
     d3 + d4 + 1 = l /\
     width mb + l <= d0 + d1 + d2 + d4 + r + 4 /\
     bits_to_num (bsignal mb (t + l + l + 1)) + m = 2 EXP width mb + 1 /\
     (!i.
        bits_to_num (bsignal ks (t + l + i)) +
        2 * bits_to_num (bsignal kc (t + l + i)) = k) /\
     (!i.
        bits_to_num (bsignal ns (t + l + i)) +
        2 * bits_to_num (bsignal nc (t + l + i)) = n) /\
     (!i.
        bits_to_num (bsignal jb (t + l + i)) + d0 + d1 + d2 + r + 3 =
        2 EXP width jb + width jb + d3) /\
     (!i. bits_to_num (bsignal rx (t + l + i)) = (2 EXP r) MOD n) /\
     (!i. bits_to_num (bsignal ry (t + l + i)) = (2 * (2 EXP r)) MOD n) /\
     (!i. bits_to_num (bsignal rz (t + l + i)) = (3 * (2 EXP r)) MOD n) /\
     montgomery_double_exp
       ld mb xs xc d0 d1 ks kc d2 ns nc jb d3 d4 rx ry rz dn ys yc ==>
     ?d. !j.
       (!i. i <= d + j ==> (signal ld (t + i) <=> i <= l)) /\
       (bits_to_num (bsignal xs (t + l + l)) +
        2 * bits_to_num (bsignal xc (t + l + l))) MOD n =
       (x * 2 EXP (r + 2)) MOD n ==>
       (!i. i <= d + j ==> (signal dn (t + l + i) <=> d <= i)) /\
       (bits_to_num (bsignal ys (t + l + d + j)) +
        2 * bits_to_num (bsignal yc (t + l + d + j))) MOD n =
       ((x EXP (2 EXP m)) * (2 EXP (r + 2))) MOD n`,
  REPEAT STRIP_TAC THEN
  MP_TAC
    (SPECL
       [`n : num`; `r : num`; `s : num`; `k : num`; `m : num`; `x : num`;
        `ld : wire`; `mb : bus`; `xs : bus`; `xc : bus`; `d0 : cycle`;
        `d1 : cycle`; `ks : bus`; `kc : bus`; `d2 : cycle`; `ns : bus`;
        `nc : bus`; `jb : bus`; `d3 : cycle`; `d4 : cycle`; `rx : bus`;
        `ry : bus`; `rz : bus`; `dn : wire`; `ys : bus`; `yc : bus`;
        `t : cycle`; `l : cycle`]
       montgomery_double_exp_bits_to_num) THEN
  ASM_REWRITE_TAC []);;

let instantiate_montgomery_double_exp n m =
    let QUANT_CONV c = RAND_CONV (ABS_CONV c) in
    let width_conv =
        REWRITE_CONV [bnil_width; bwire_width; bappend_width] THENC
        NUM_REDUCE_CONV in
    let bits_conv =
        REWRITE_CONV
          [bnil_bsignal; bwire_bsignal; bappend_bsignal;
           ground_signal; power_signal; APPEND_SING;
           bits_to_num_cons; bits_to_num_nil;
           bit_cons_true; bit_cons_false] THENC
        NUM_REDUCE_CONV in
    let nn = mk_numeral n in
    let mn = mk_numeral m in
    let r_th = bit_width_conv (mk_comb (`bit_width`,nn)) in
    let rn = rand (concl r_th) in
    let r = dest_numeral rn in
    let (d0,d1,d2,d3,d4) =
        let d = add_num (quo_num (bit_width_num r) num_2) num_1 in
        (d,d,d,d,d) in
    let d0n = mk_numeral d0 in
    let d1n = mk_numeral d1 in
    let d2n = mk_numeral d2 in
    let d3n = mk_numeral d3 in
    let d4n = mk_numeral d4 in
    let ld = mk_var ("ld",wire_ty) in
    let dn = mk_var ("dn",wire_ty) in
    let xs = variable_bus "xs" r in
    let xc = variable_bus "xc" r in
    let ys = variable_bus "ys" r in
    let yc = variable_bus "yc" r in
    let egcd_th =
        let rtm =
            let tm0 = mk_comb (`(+) : num -> num -> num`, rn) in
            mk_comb (`(EXP) 2`, mk_comb (tm0, `2`)) in
        let rth = NUM_REDUCE_CONV rtm in
        let eth = prove_egcd (rhs (concl rth)) nn in
        CONV_RULE (LAND_CONV (REWR_CONV MULT_SYM THENC
                              LAND_CONV (REWR_CONV (SYM rth)))) eth in
    let sn = rand (lhs (concl egcd_th)) in
    let kn = lhand (lhand (rhs (concl egcd_th))) in
    let (ns,nc) =
        let r1 = sub_num r num_1 in
        let n1 = num_to_bitvec n r1 in
        let n2 = div_num (sub_num n (bits_to_num n1)) num_2 in
        (bits_to_bus n1, bits_to_bus (num_to_bitvec n2 r1)) in
    let k = dest_numeral kn in
    let (ks,kc) =
        let r1 = add_num r num_1 in
        let k1 = num_to_bitvec k r1 in
        let k2 = div_num (sub_num k (bits_to_num k1)) num_2 in
        (bits_to_bus k1, bits_to_bus (num_to_bitvec k2 r1)) in
    let mb =
        let m1 = sub_num m num_1 in
        mk_event_counter_arg m1 in
    let jb =
        let jn = add_num d0 (add_num d1 (add_num d2 (add_num r num_1))) in
        mk_counter_arg (sub_num jn d3) in
    let rx_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            list_mk_comb (`(MOD)`, [tm0; nn]) in
        NUM_REDUCE_CONV tm in
    let rx =
        let n = dest_numeral (rhs (concl rx_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let ry_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            let tm1 = mk_comb (`( * ) 2`, tm0) in
            list_mk_comb (`(MOD)`, [tm1; nn]) in
        NUM_REDUCE_CONV tm in
    let ry =
        let n = dest_numeral (rhs (concl ry_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let rz_th =
        let tm =
            let tm0 = mk_comb (`(EXP) 2`, rn) in
            let tm1 = mk_comb (`( * ) 3`, tm0) in
            list_mk_comb (`(MOD)`, [tm1; nn]) in
        NUM_REDUCE_CONV tm in
    let rz =
        let n = dest_numeral (rhs (concl rz_th)) in
        bits_to_bus (num_to_bitvec n r) in
    let l_th =
        let tm =
            let tm0 = list_mk_comb (`(+) : num -> num -> num`, [d4n; `1`]) in
            list_mk_comb (`(+) : num -> num -> num`, [d3n; tm0]) in
        NUM_REDUCE_CONV tm in
    let ln = rand (concl l_th) in
    let fv_x = `x : num` in
    let fv_t = `t : cycle` in
    let th =
        SPECL
          [nn; rn; sn; kn; mn; fv_x; ld; mb; xs; xc; d0n; d1n; ks; kc; d2n;
           ns; nc; jb; d3n; d4n; rx; ry; rz; dn; ys; yc; fv_t; ln]
          montgomery_double_exp_syn_spec in
    let th =
        let conv =
            width_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            LAND_CONV (REWR_CONV r_th) THENC
            REWR_CONV (EQT_INTRO (SPEC_ALL LE_REFL)) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            REWR_CONV (EQT_INTRO egcd_th) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            REWR_CONV (EQT_INTRO l_th) in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            width_conv in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            LAND_CONV (LAND_CONV bits_conv) THENC
            RAND_CONV (LAND_CONV (RAND_CONV width_conv)) THENC
            NUM_REDUCE_CONV in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV
                 (LAND_CONV bits_conv THENC
                  RAND_CONV (RAND_CONV bits_conv)) THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV
                 (LAND_CONV bits_conv THENC
                  RAND_CONV (RAND_CONV bits_conv)) THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV (LAND_CONV bits_conv) THENC
               RAND_CONV
                 (LAND_CONV (RAND_CONV width_conv) THENC
                  RAND_CONV (LAND_CONV width_conv)) THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV bits_conv THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV bits_conv THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let th =
        let conv =
            QUANT_CONV
              (LAND_CONV bits_conv THENC
               NUM_REDUCE_CONV) THENC
            REWRITE_CONV [] in
        CONV_RULE
          (LAND_CONV
             (LAND_CONV conv THENC
              REWR_CONV TRUE_AND_THM)) th in
    let (ckt,th) = undisch_bind th in
    let th =
        let ll_th =
            let ll_tm = list_mk_comb (`(+) : num -> num -> num`, [ln; ln]) in
            NUM_REDUCE_CONV ll_tm in
        let r_th =
            let r_tm = list_mk_comb (`(+) : num -> num -> num`, [rn; `2`]) in
            NUM_REDUCE_CONV r_tm in
        REWRITE_RULE [ll_th; r_th] th in
    let th = (GEN fv_x o GEN fv_t) th in
    th;;

let synthesize_montgomery_double_exp rws n m =
    let spec =
        complain_timed "Instantiated parameters"
          (REWRITE_RULE rws o instantiate_montgomery_double_exp n) m in
    let syn = montgomery_double_exp_syn_gen "" in
    let primary = frees (concl spec) in
    synthesize_hardware syn primary spec;;

let testbench_montgomery_double_exp (Verilog_module name) ckt =
    let width =
        let xs =
            (lhand o rand o lhand o lhand o lhand o rand o lhand o snd o
             dest_abs o rand o snd o dest_abs o rand o snd o dest_abs o
             rand o snd o dest_abs o rand o spec_circuit) ckt in
        match dest_variable_bus xs with
          Bus_wires (_,l) -> num_of_int (length l) in
    let last_reset_cycle =
        (dest_numeral o rand o rand o rand o snd o dest_abs o rand o lhand o
         lhand o snd o dest_abs o rand o snd o dest_abs o rand o snd o
         dest_abs o rand o snd o dest_abs o rand o spec_circuit) ckt in
    let input_cycle =
        (dest_numeral o rand o rand o rand o lhand o lhand o lhand o rand o
         lhand o snd o dest_abs o rand o snd o dest_abs o rand o snd o
         dest_abs o rand o snd o dest_abs o rand o spec_circuit) ckt in
    let lines =
        ["`include \"" ^ name ^ ".v\"";
         "";
         "module main;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] xs;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] xc;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] ys;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] yc;";
         "";
         "  reg clk;";
         "  reg ld;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] ps;";
         "  reg [0:" ^ string_of_num (sub_num width num_1) ^ "] pc;";
         "  wire dn;";
         "  wire [0:" ^ string_of_num (sub_num width num_1) ^ "] qs;";
         "  wire [0:" ^ string_of_num (sub_num width num_1) ^ "] qc;";
         "";
         "  integer seed;";
         "";
         "  " ^ name;
         "    root";
         "    (.clk (clk),";
         "     .ld (ld),";
         "     .xs (ps),";
         "     .xc (pc),";
         "     .dn (dn),";
         "     .ys (qs),";
         "     .yc (qc));";
         "";
         "  initial";
         "    begin";
         "      seed = `SEED;";
         "      $display(\"+" ^ String.make (String.length name + 10) '-' ^ "+\");";
         "      $display(\"| Testing " ^ name ^ " |\");";
         "      $display(\"+" ^ String.make (String.length name + 10) '-' ^ "+\");";
         "      $display(\"Random seed = %0d\", seed);";
         "      $display(\"\");";
         "      xs = $random(seed);";
         "      xc = $random(seed);";
         "      clk = 1'b0;";
         "      @(posedge clk);";
         "      // Time 0";
         "      ld = 1'b1;";
         "      repeat(" ^ string_of_num (add_num last_reset_cycle num_1) ^ ") @(posedge clk);";
         "      // Time " ^ string_of_num (add_num last_reset_cycle num_1);
         "      ld = 1'b0;";
         "      repeat(" ^ string_of_num (sub_num input_cycle (add_num last_reset_cycle num_1)) ^ ") @(posedge clk);";
         "      // Time " ^ string_of_num input_cycle;
         "      ps = xs;";
         "      pc = xc;";
         "      @(posedge clk);";
         "      // Time " ^ string_of_num (add_num input_cycle num_1);
         "      ps = " ^ string_of_num (sub_num width num_1) ^ "'bx;";
         "      pc = " ^ string_of_num (sub_num width num_1) ^ "'bx;";
         "      @(posedge dn);";
         "      #1 ys = qs; yc = qc;";
         "      $display(\"Inputs: xs = %0d, xc = %0d\", xs, xc);";
         "      $display(\"Outputs: ys = %0d, yc = %0d\", ys, yc);";
         "      $display(\"\");";
         "      $display(\"Test complete at time %0t.\", $time);";
         "      $finish;";
         "    end";
         "";
         "  always";
         "    #5 clk = ~clk;";
         "";
         "endmodule // main"] in
    let file = "opentheory/hardware/" ^ name ^ "_testbench.v" in
    let s = String.concat "\n" lines ^ "\n" in
    let h = open_out file in
    let () = output_string h s in
    let () = close_out h in
    ();;

unset_jrh_lexer;;

let check_system cmd =
    match Unix.system cmd with
      Unix.WEXITED n ->
      if n = 0 then () else
      failwith ("couldn't run command (error " ^ string_of_int n ^ ")")
    | _ -> failwith "couldn't run command";;

set_jrh_lexer;;

let run_test_montgomery_double_exp (Verilog_module name) =
    let file = name ^ "_testbench.out" in
    let cmd = "make -C opentheory/hardware " ^ file ^ " >/dev/null" in
    let () = check_system cmd in
    ();;

let rec two_exp_num n =
    if eq_num n num_0 then num_1 else
    mult_num num_2 (two_exp_num (sub_num n num_1));;

let rec double_exp_mod_num n x m =
    let x = mod_num x n in
    if eq_num m num_0 then x else
    double_exp_mod_num n (mult_num x x) (sub_num m num_1);;

let check_test_montgomery_double_exp n m name ckt =
    let s =
        let r =
            (dest_numeral o rand o rand o lhand o rand o rand o
             lhand o snd o dest_abs o rand o snd o dest_abs o rand o snd o
             dest_abs o rand o snd o dest_abs o rand o spec_circuit) ckt in
        let (s,_,_) = egcd_num (two_exp_num r) n in
        s in
    let (x,y) =
        let h =
            let Verilog_module s = name in
            let f = "opentheory/hardware/" ^ s ^ "_testbench.out" in
            open_in f in
        let inp () =
            try (Some (input_line h))
            with End_of_file -> None in
        let rec f state =
            match inp () with
              None -> state
            | Some l ->
                let (t,ts) = split ' ' l in
                let state =
                    if t = "Inputs:" then
                      match state with
                        (None,y) -> (Some ts, y)
                      | _ -> failwith "multiple input lines"
                    else if t = "Outputs:" then
                      match state with
                        (x,None) -> (x, Some ts)
                      | _ -> failwith "multiple output lines"
                    else state in
                f state in
        let (x,y) = f (None,None) in
        let () = close_in h in
        let parse ts =
            match ts with
              [_; _; s; _; _; c] ->
              let (s,_) = split ',' s in
              add_num (num_of_string s) (mult_num num_2 (num_of_string c))
            | _ -> failwith "bad sum/carry format" in
        match (x,y) with
          (Some x, Some y) -> (parse x, parse y)
        | (None,_) -> failwith "no input line found"
        | (_,None) -> failwith "no output line found" in
    let spec = double_exp_mod_num n (mult_num x s) m in
    let ckt = mod_num (mult_num y s) n in
    if eq_num spec ckt then ()
    else failwith "TEST FAILED: spec <> ckt";;

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(* To estimate the time required to run a random test, we assume *)
(* the running time is a quadratic polynomial of (bit_width n)   *)
(* multiplied by m.                                              *)
(*                                                               *)
(* Solve for best fit coefficients using                         *)
(*                                                               *)
(*   http://www.arachnoid.com/polysolve/                         *)
(*                                                               *)
(* and entering the following performance results (m = 1000):    *)
(*                                                               *)
(*   64,35                                                       *)
(*   128,182                                                     *)
(*   256,907                                                     *)
(*   512,4453                                                    *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

let test_montgomery_double_exp_estimate_run =
    let c2 =  2.07112e-5 in
    let c1 = -2.09218e-3 in
    let c0 =  9.36666e-2 in
    fun n -> fun m ->
    let n = float_of_num (bit_width_num n) in
    let m = float_of_num m in
    let t = ((c2 *. n +. c1) *. n +. c0) *. m in
    max 0 (truncate t);;

let test_montgomery_double_exp_max_test_run = 1000;;

let test_montgomery_double_exp n m name ckt =
    let () =
        complain_timed "- Generated verilog testbench"
          (testbench_montgomery_double_exp name) ckt in
    let continue =
        let run = test_montgomery_double_exp_estimate_run n m in
        let go = run <= test_montgomery_double_exp_max_test_run in
        let () =
            complain
              ("- - Estimate random test run will take " ^
               string_of_int run ^ " second" ^
               (if run = 1 then "" else "s") ^ " (" ^
               (if go then "continuing" else "skipping") ^ ")") in
        go in
    if not continue then () else
    let () =
        complain_timed "- Ran a random test"
          run_test_montgomery_double_exp name in
    let () =
        complain_timed "- Checked the test result"
          (check_test_montgomery_double_exp n m name) ckt in
    ();;

let performance_test_montgomery_double_exp w =
    let n = random_odd_num w in
    let m = dest_numeral `1000` in
    let test () =
        let name = "double_exp_" ^ string_of_int w in
        let () = complain ("Synthesizing " ^ name ^ ":") in
        let ckt = synthesize_montgomery_double_exp [] n m in
        let name = Verilog_module name in
        let _ =
            let comment = default_verilog_comment () in
            let clk = `clk : wire` in
            let primary = Verilog_primary (clk :: frees_circuit ckt) in
            complain_timed "Generated verilog module"
              (hardware_to_verilog_file name comment primary) ckt in
        let () =
            complain_timed "Tested the verilog module"
              (test_montgomery_double_exp n m name) ckt in
        () in
    complain_timed "TOTAL" test ();;

let performance_test_max_size = 1024;;

let performance_tests_montgomery_double_exp () =
    let rec test w =
        if w > performance_test_max_size then () else
        let () = performance_test_montgomery_double_exp w in
        test (w * 2) in
     test 8;;

(* Testing
let double_exp_91_ckt = synthesize_montgomery_double_exp [] (dest_numeral `91`) (dest_numeral `11`);;
let name = Verilog_module "double_exp_91";;
let comment = default_verilog_comment ();;
let primary = Verilog_primary (`clk : wire` :: frees_circuit double_exp_91_ckt);;
hardware_to_verilog_file name comment primary double_exp_91_ckt;;

let n = dest_numeral `221`;;
let m = dest_numeral `1000`;;
let ckt = synthesize_montgomery_double_exp [] n m;;
let name = Verilog_module ("double_exp_" ^ string_of_num (bit_width_num n));;
let comment = default_verilog_comment ();;
let primary = Verilog_primary (`clk : wire` :: frees_circuit ckt);;
hardware_to_verilog_file name comment primary ckt;;
test_montgomery_double_exp_estimate_run n m;;
test_montgomery_double_exp n m name ckt;;

performance_test_montgomery_double_exp 8;;
disable_proof_logging ();;
performance_tests_montgomery_double_exp ();;
*)

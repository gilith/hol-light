/*----------------------------------------------------------------------------+
| module montgomery_reduce_91 satisfies the following property:               |
|                                                                             |
| !x y t.                                                                     |
|     (!i. i <= 12 ==> (signal ld (t + i) <=> i = 0)) /\                      |
|     bits_to_num (bsignal xs[0:6] t) + 2 * bits_to_num (bsignal xc[0:6] t) = |
|     x /\                                                                    |
|     (!i. 2 <= i /\ i <= 10                                                  |
|          ==> bits_to_num (bsignal ys[0:6] (t + i)) +                        |
|              2 * bits_to_num (bsignal yc[0:6] (t + i)) =                    |
|              y)                                                             |
|     ==> bits_to_num (bsignal zs[0:7] (t + 15)) +                            |
|         2 * bits_to_num (bsignal zc[0:7] (t + 15)) =                        |
|         montgomery_reduce 91 (2 EXP 9) 45 (x * y)                           |
|                                                                             |
| Copyright (c) 2014 Joe Leslie-Hurd, distributed under the MIT license       |
+----------------------------------------------------------------------------*/

module montgomery_reduce_91(clk,ld,xs,xc,ys,yc,zs,zc);
  input clk;
  input ld;
  input [6:0] xs;
  input [6:0] xc;
  input [6:0] ys;
  input [6:0] yc;

  output [7:0] zs;
  output [7:0] zc;

  reg ld1;  // 1:0|18/4=4
  reg ld2;  // 1:0|13/3=4
  reg mulb0_cp0;  // 5:7|4/1=4
  reg mulb0_cp1;  // 6:9|4/1=4
  reg mulb0_cp2;  // 6:13|4/1=4
  reg mulb0_cp3;  // 6:12|4/1=4
  reg mulb0_cp4;  // 6:9|4/1=4
  reg mulb0_cp5;  // 6:12|4/1=4
  reg mulb0_cp6;  // 5:8|4/1=4
  reg mulb0_cp7;  // 4:6|2/1=2
  reg mulb0_sp0;  // 5:7|3/1=3
  reg mulb0_sp1;  // 6:9|4/1=4
  reg mulb0_sp2;  // 6:13|4/1=4
  reg mulb0_sp3;  // 6:12|4/1=4
  reg mulb0_sp4;  // 6:9|4/1=4
  reg mulb0_sp5;  // 6:12|4/1=4
  reg mulb0_sp6;  // 5:8|4/1=4
  reg mulb0_sp7;  // 4:6|4/1=4
  reg mulsc_ldd;  // 1:0|16/4=4
  reg mulsc_mulb_cp4;  // 9:20|4/1=4
  reg mulsc_mulb_cp5;  // 9:20|4/1=4
  reg mulsc_mulb_cp6;  // 7:16|2/1=2
  reg mulsc_mulb_sp5;  // 9:17|4/1=4
  reg mulsc_mulb_sp6;  // 7:13|4/1=4
  reg mulsc_pipe_x1;  // 4:2|1/1=3
  reg mulsc_shrsc_cp0;  // 4:2|2/1=2
  reg mulsc_shrsc_cp1;  // 4:2|2/1=2
  reg mulsc_shrsc_cp2;  // 4:2|2/1=2
  reg mulsc_shrsc_cp3;  // 4:2|2/1=2
  reg mulsc_shrsc_cp4;  // 4:2|2/1=2
  reg mulsc_shrsc_cp5;  // 4:2|2/1=2
  reg mulsc_shrsc_cp6;  // 2:1|1/1=1
  reg mulsc_shrsc_sp0;  // 4:2|2/1=2
  reg mulsc_shrsc_sp1;  // 4:2|2/1=2
  reg mulsc_shrsc_sp2;  // 4:2|2/1=2
  reg mulsc_shrsc_sp3;  // 4:2|2/1=2
  reg mulsc_shrsc_sp4;  // 4:2|2/1=2
  reg mulsc_shrsc_sp5;  // 3:1|2/1=2
  reg mulsc_xbd;  // 1:0|15/3=5
  reg pipe0_x1;  // 1:0|1/1=4
  reg pipe0_x3;  // 1:0|1/1=4
  reg pipe1_x1;  // 1:0|1/1=3
  reg pipe2_x1;  // 3:3|1/1=3
  reg qb2;  // 1:0|13/3=4
  reg sa0;  // 1:0|2/1=2
  reg sa1;  // 1:0|3/1=3
  reg sa2;  // 1:0|16/3=5
  reg sa3;  // 4:4|3/1=5
  reg sa4;  // 8:12|6/1=6
  reg sa5;  // 9:17|8/1=8
  reg sa6;  // 9:17|8/1=8
  reg sa7;  // 9:17|6/1=6
  reg sa8;  // 9:17|5/1=5
  reg sb0;  // 8:15|6/1=6
  reg sb1;  // 9:20|6/1=6
  reg sb2;  // 9:20|6/1=6
  reg sb3;  // 9:20|5/1=5
  reg sc0;  // 5:8|5/1=5
  reg sc1;  // 6:12|6/1=6
  reg sc2;  // 6:9|6/1=6
  reg sc3;  // 6:13|6/1=6
  reg sc4;  // 6:12|7/1=7
  reg sc5;  // 5:7|8/1=8
  reg sd0;  // 4:5|3/1=3
  reg sd1;  // 5:8|6/1=6
  reg sd2;  // 6:12|6/1=6
  reg sd3;  // 6:9|6/1=6
  reg sd4;  // 6:13|7/1=7
  reg sd5;  // 6:12|8/1=8
  reg sd6;  // 5:10|6/1=6

  wire add3_maj3_or3_wx;
  wire add3_maj3_wx;
  wire add3_maj3_wy;
  wire add3_maj3_xy;
  wire add3_xor3_wx;
  wire add3b0_maj3b_or3b_wx0;
  wire add3b0_maj3b_or3b_wx1;
  wire add3b0_maj3b_or3b_wx2;
  wire add3b0_maj3b_or3b_wx3;
  wire add3b0_maj3b_or3b_wx4;
  wire add3b0_maj3b_or3b_wx5;
  wire add3b0_maj3b_wx0;
  wire add3b0_maj3b_wx1;
  wire add3b0_maj3b_wx2;
  wire add3b0_maj3b_wx3;
  wire add3b0_maj3b_wx4;
  wire add3b0_maj3b_wx5;
  wire add3b0_maj3b_wy0;
  wire add3b0_maj3b_wy1;
  wire add3b0_maj3b_wy2;
  wire add3b0_maj3b_wy3;
  wire add3b0_maj3b_wy4;
  wire add3b0_maj3b_wy5;
  wire add3b0_maj3b_xy0;
  wire add3b0_maj3b_xy1;
  wire add3b0_maj3b_xy2;
  wire add3b0_maj3b_xy3;
  wire add3b0_maj3b_xy4;
  wire add3b0_maj3b_xy5;
  wire add3b0_xor3b_wx0;
  wire add3b0_xor3b_wx1;
  wire add3b0_xor3b_wx2;
  wire add3b0_xor3b_wx3;
  wire add3b0_xor3b_wx4;
  wire add3b0_xor3b_wx5;
  wire add3b1_maj3b_or3b_wx0;
  wire add3b1_maj3b_or3b_wx1;
  wire add3b1_maj3b_wx0;
  wire add3b1_maj3b_wx1;
  wire add3b1_maj3b_wy0;
  wire add3b1_maj3b_wy1;
  wire add3b1_maj3b_xy0;
  wire add3b1_maj3b_xy1;
  wire add3b1_xor3b_wx0;
  wire add3b1_xor3b_wx1;
  wire mc4;
  wire mc5;
  wire mc6;
  wire ms5;
  wire ms6;
  wire mulb0_add3b_maj3b_or3b_wx1;
  wire mulb0_add3b_maj3b_or3b_wx2;
  wire mulb0_add3b_maj3b_or3b_wx4;
  wire mulb0_add3b_maj3b_wx1;
  wire mulb0_add3b_maj3b_wx2;
  wire mulb0_add3b_maj3b_wx4;
  wire mulb0_add3b_maj3b_wy1;
  wire mulb0_add3b_maj3b_wy2;
  wire mulb0_add3b_maj3b_wy4;
  wire mulb0_add3b_maj3b_xy1;
  wire mulb0_add3b_maj3b_xy2;
  wire mulb0_add3b_maj3b_xy4;
  wire mulb0_add3b_xor3b_wx1;
  wire mulb0_add3b_xor3b_wx2;
  wire mulb0_add3b_xor3b_wx4;
  wire mulb0_cq0;
  wire mulb0_cq1;
  wire mulb0_cq2;
  wire mulb0_cq3;
  wire mulb0_cq4;
  wire mulb0_cq5;
  wire mulb0_cq6;
  wire mulb0_cq7;
  wire mulb0_pc0;
  wire mulb0_pc1;
  wire mulb0_pc2;
  wire mulb0_pc3;
  wire mulb0_pc4;
  wire mulb0_pc5;
  wire mulb0_pc6;
  wire mulb0_pc7;
  wire mulb0_ps0;
  wire mulb0_ps1;
  wire mulb0_ps2;
  wire mulb0_ps3;
  wire mulb0_ps4;
  wire mulb0_ps5;
  wire mulb0_ps6;
  wire mulb0_sq0;
  wire mulb0_sq1;
  wire mulb0_sq2;
  wire mulb0_sq3;
  wire mulb0_sq4;
  wire mulb0_sq5;
  wire mulb0_sq6;
  wire mulb0_sq7;
  wire mulb1_add3_maj3_or3_wx;
  wire mulb1_add3_maj3_wx;
  wire mulb1_add3_maj3_wy;
  wire mulb1_add3_maj3_xy;
  wire mulb1_add3_xor3_wx;
  wire mulb1_add3b_maj3b_or3b_wx0;
  wire mulb1_add3b_maj3b_or3b_wx2;
  wire mulb1_add3b_maj3b_or3b_wx3;
  wire mulb1_add3b_maj3b_wx0;
  wire mulb1_add3b_maj3b_wx2;
  wire mulb1_add3b_maj3b_wx3;
  wire mulb1_add3b_maj3b_wy0;
  wire mulb1_add3b_maj3b_wy2;
  wire mulb1_add3b_maj3b_wy3;
  wire mulb1_add3b_maj3b_xy0;
  wire mulb1_add3b_maj3b_xy2;
  wire mulb1_add3b_maj3b_xy3;
  wire mulb1_add3b_xor3b_wx0;
  wire mulb1_add3b_xor3b_wx2;
  wire mulb1_add3b_xor3b_wx3;
  wire mulb1_cq0;
  wire mulb1_cq1;
  wire mulb1_cq2;
  wire mulb1_cq3;
  wire mulb1_cq4;
  wire mulb1_cq5;
  wire mulb1_pc0;
  wire mulb1_pc1;
  wire mulb1_pc2;
  wire mulb1_pc3;
  wire mulb1_pc4;
  wire mulb1_pc5;
  wire mulb1_ps0;
  wire mulb1_ps1;
  wire mulb1_ps2;
  wire mulb1_ps3;
  wire mulb1_ps4;
  wire mulb1_sq0;
  wire mulb1_sq1;
  wire mulb1_sq2;
  wire mulb1_sq3;
  wire mulb1_sq4;
  wire mulb1_sq5;
  wire mulsc_mulb_add3_maj3_or3_wx;
  wire mulsc_mulb_add3_maj3_wx;
  wire mulsc_mulb_add3_maj3_wy;
  wire mulsc_mulb_add3_maj3_xy;
  wire mulsc_mulb_add3_xor3_wx;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx0;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx1;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx2;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx3;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx4;
  wire mulsc_mulb_add3b0_maj3b_or3b_wx5;
  wire mulsc_mulb_add3b0_maj3b_wx0;
  wire mulsc_mulb_add3b0_maj3b_wx1;
  wire mulsc_mulb_add3b0_maj3b_wx2;
  wire mulsc_mulb_add3b0_maj3b_wx3;
  wire mulsc_mulb_add3b0_maj3b_wx4;
  wire mulsc_mulb_add3b0_maj3b_wx5;
  wire mulsc_mulb_add3b0_maj3b_wy0;
  wire mulsc_mulb_add3b0_maj3b_wy1;
  wire mulsc_mulb_add3b0_maj3b_wy2;
  wire mulsc_mulb_add3b0_maj3b_wy3;
  wire mulsc_mulb_add3b0_maj3b_wy4;
  wire mulsc_mulb_add3b0_maj3b_wy5;
  wire mulsc_mulb_add3b0_maj3b_xy0;
  wire mulsc_mulb_add3b0_maj3b_xy1;
  wire mulsc_mulb_add3b0_maj3b_xy2;
  wire mulsc_mulb_add3b0_maj3b_xy3;
  wire mulsc_mulb_add3b0_maj3b_xy4;
  wire mulsc_mulb_add3b0_maj3b_xy5;
  wire mulsc_mulb_add3b0_xor3b_wx0;
  wire mulsc_mulb_add3b0_xor3b_wx1;
  wire mulsc_mulb_add3b0_xor3b_wx2;
  wire mulsc_mulb_add3b0_xor3b_wx3;
  wire mulsc_mulb_add3b0_xor3b_wx4;
  wire mulsc_mulb_add3b0_xor3b_wx5;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx0;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx1;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx2;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx3;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx4;
  wire mulsc_mulb_add3b1_maj3b_or3b_wx5;
  wire mulsc_mulb_add3b1_maj3b_wx0;
  wire mulsc_mulb_add3b1_maj3b_wx1;
  wire mulsc_mulb_add3b1_maj3b_wx2;
  wire mulsc_mulb_add3b1_maj3b_wx3;
  wire mulsc_mulb_add3b1_maj3b_wx4;
  wire mulsc_mulb_add3b1_maj3b_wx5;
  wire mulsc_mulb_add3b1_maj3b_wy0;
  wire mulsc_mulb_add3b1_maj3b_wy1;
  wire mulsc_mulb_add3b1_maj3b_wy2;
  wire mulsc_mulb_add3b1_maj3b_wy3;
  wire mulsc_mulb_add3b1_maj3b_wy4;
  wire mulsc_mulb_add3b1_maj3b_wy5;
  wire mulsc_mulb_add3b1_maj3b_xy0;
  wire mulsc_mulb_add3b1_maj3b_xy1;
  wire mulsc_mulb_add3b1_maj3b_xy2;
  wire mulsc_mulb_add3b1_maj3b_xy3;
  wire mulsc_mulb_add3b1_maj3b_xy4;
  wire mulsc_mulb_add3b1_maj3b_xy5;
  wire mulsc_mulb_add3b1_xor3b_wx0;
  wire mulsc_mulb_add3b1_xor3b_wx1;
  wire mulsc_mulb_add3b1_xor3b_wx2;
  wire mulsc_mulb_add3b1_xor3b_wx3;
  wire mulsc_mulb_add3b1_xor3b_wx4;
  wire mulsc_mulb_add3b1_xor3b_wx5;
  wire mulsc_mulb_cq0;
  wire mulsc_mulb_cq1;
  wire mulsc_mulb_cq2;
  wire mulsc_mulb_cq3;
  wire mulsc_mulb_cq4;
  wire mulsc_mulb_cq5;
  wire mulsc_mulb_cq6;
  wire mulsc_mulb_pc0;
  wire mulsc_mulb_pc1;
  wire mulsc_mulb_pc2;
  wire mulsc_mulb_pc3;
  wire mulsc_mulb_pc4;
  wire mulsc_mulb_pc5;
  wire mulsc_mulb_pc6;
  wire mulsc_mulb_ps0;
  wire mulsc_mulb_ps1;
  wire mulsc_mulb_ps2;
  wire mulsc_mulb_ps3;
  wire mulsc_mulb_ps4;
  wire mulsc_mulb_ps5;
  wire mulsc_mulb_sq0;
  wire mulsc_mulb_sq1;
  wire mulsc_mulb_sq2;
  wire mulsc_mulb_sq3;
  wire mulsc_mulb_sq4;
  wire mulsc_mulb_sq5;
  wire mulsc_mulb_sq6;
  wire mulsc_mulb_yoc0;
  wire mulsc_mulb_yoc1;
  wire mulsc_mulb_yoc2;
  wire mulsc_mulb_yoc3;
  wire mulsc_mulb_yoc4;
  wire mulsc_mulb_yoc5;
  wire mulsc_mulb_yoc6;
  wire mulsc_mulb_yos0;
  wire mulsc_mulb_yos1;
  wire mulsc_mulb_yos2;
  wire mulsc_mulb_yos3;
  wire mulsc_mulb_yos4;
  wire mulsc_mulb_yos5;
  wire mulsc_mulb_yos6;
  wire mulsc_shrsc_cq0;
  wire mulsc_shrsc_cq1;
  wire mulsc_shrsc_cq2;
  wire mulsc_shrsc_cq3;
  wire mulsc_shrsc_cq4;
  wire mulsc_shrsc_cq5;
  wire mulsc_shrsc_cr0;
  wire mulsc_shrsc_cr1;
  wire mulsc_shrsc_cr2;
  wire mulsc_shrsc_cr3;
  wire mulsc_shrsc_cr4;
  wire mulsc_shrsc_cr5;
  wire mulsc_shrsc_cr6;
  wire mulsc_shrsc_sq0;
  wire mulsc_shrsc_sq1;
  wire mulsc_shrsc_sq2;
  wire mulsc_shrsc_sq3;
  wire mulsc_shrsc_sq4;
  wire mulsc_shrsc_sq5;
  wire mulsc_shrsc_sr0;
  wire mulsc_shrsc_sr1;
  wire mulsc_shrsc_sr2;
  wire mulsc_shrsc_sr3;
  wire mulsc_shrsc_sr4;
  wire mulsc_shrsc_sr5;
  wire mulsc_xb;
  wire mw;
  wire or3_wx;
  wire pb;
  wire pc0;
  wire pc1;
  wire pc2;
  wire pc3;
  wire pc4;
  wire pc5;
  wire pc6;
  wire ps0;
  wire ps1;
  wire ps2;
  wire ps3;
  wire ps4;
  wire ps5;
  wire ps6;
  wire qb;
  wire qc0;
  wire qc1;
  wire qc2;
  wire qc3;
  wire qc4;
  wire qc5;
  wire qc6;
  wire qc7;
  wire qs0;
  wire qs1;
  wire qs2;
  wire qs3;
  wire qs4;
  wire qs5;
  wire qs6;
  wire qs7;
  wire sticky_q;
  wire vb;
  wire vc0;
  wire vc1;
  wire vc2;
  wire vc3;
  wire vc4;
  wire vc5;
  wire vs0;
  wire vs1;
  wire vs2;
  wire vs3;
  wire vs4;
  wire vs5;
  wire vt;
  wire xn0;
  wire xn1;
  wire xn2;
  wire zc0_o;
  wire zc1_o;
  wire zc2_o;
  wire zc3_o;
  wire zc5_o;
  wire zc6_o;
  wire zc7_o;
  wire zs0_o;
  wire zs1_o;
  wire zs2_o;
  wire zs3_o;
  wire zs4_o;
  wire zs5_o;
  wire zs6_o;
  wire zs7_o;

  assign add3_maj3_or3_wx = add3_maj3_wx | add3_maj3_wy;
  assign add3_maj3_wx = sb2 & sa7;
  assign add3_maj3_wy = sb2 & mc6;
  assign add3_maj3_xy = sa7 & mc6;
  assign add3_xor3_wx = sb2 ^ sa7;
  assign add3b0_maj3b_or3b_wx0 = add3b0_maj3b_wx0 | add3b0_maj3b_wy0;
  assign add3b0_maj3b_or3b_wx1 = add3b0_maj3b_wx1 | add3b0_maj3b_wy1;
  assign add3b0_maj3b_or3b_wx2 = add3b0_maj3b_wx2 | add3b0_maj3b_wy2;
  assign add3b0_maj3b_or3b_wx3 = add3b0_maj3b_wx3 | add3b0_maj3b_wy3;
  assign add3b0_maj3b_or3b_wx4 = add3b0_maj3b_wx4 | add3b0_maj3b_wy4;
  assign add3b0_maj3b_or3b_wx5 = add3b0_maj3b_wx5 | add3b0_maj3b_wy5;
  assign add3b0_maj3b_wx0 = sa0 & sc0;
  assign add3b0_maj3b_wx1 = sa1 & sc1;
  assign add3b0_maj3b_wx2 = sa2 & sc2;
  assign add3b0_maj3b_wx3 = sa3 & sc3;
  assign add3b0_maj3b_wx4 = sa4 & sc4;
  assign add3b0_maj3b_wx5 = sa5 & sc5;
  assign add3b0_maj3b_wy0 = sa0 & sd0;
  assign add3b0_maj3b_wy1 = sa1 & sd1;
  assign add3b0_maj3b_wy2 = sa2 & sd2;
  assign add3b0_maj3b_wy3 = sa3 & sd3;
  assign add3b0_maj3b_wy4 = sa4 & sd4;
  assign add3b0_maj3b_wy5 = sa5 & sd5;
  assign add3b0_maj3b_xy0 = sc0 & sd0;
  assign add3b0_maj3b_xy1 = sc1 & sd1;
  assign add3b0_maj3b_xy2 = sc2 & sd2;
  assign add3b0_maj3b_xy3 = sc3 & sd3;
  assign add3b0_maj3b_xy4 = sc4 & sd4;
  assign add3b0_maj3b_xy5 = sc5 & sd5;
  assign add3b0_xor3b_wx0 = sa0 ^ sc0;
  assign add3b0_xor3b_wx1 = sa1 ^ sc1;
  assign add3b0_xor3b_wx2 = sa2 ^ sc2;
  assign add3b0_xor3b_wx3 = sa3 ^ sc3;
  assign add3b0_xor3b_wx4 = sa4 ^ sc4;
  assign add3b0_xor3b_wx5 = sa5 ^ sc5;
  assign add3b1_maj3b_or3b_wx0 = add3b1_maj3b_wx0 | add3b1_maj3b_wy0;
  assign add3b1_maj3b_or3b_wx1 = add3b1_maj3b_wx1 | add3b1_maj3b_wy1;
  assign add3b1_maj3b_wx0 = sb0 & ms5;
  assign add3b1_maj3b_wx1 = sb1 & ms6;
  assign add3b1_maj3b_wy0 = sb0 & mc4;
  assign add3b1_maj3b_wy1 = sb1 & mc5;
  assign add3b1_maj3b_xy0 = ms5 & mc4;
  assign add3b1_maj3b_xy1 = ms6 & mc5;
  assign add3b1_xor3b_wx0 = sb0 ^ ms5;
  assign add3b1_xor3b_wx1 = sb1 ^ ms6;
  assign mc4 = add3b0_maj3b_or3b_wx4 | add3b0_maj3b_xy4;
  assign mc5 = add3b0_maj3b_or3b_wx5 | add3b0_maj3b_xy5;
  assign mc6 = sa6 & sd6;
  assign ms5 = add3b0_xor3b_wx5 ^ sd5;
  assign ms6 = sa6 ^ sd6;
  assign mulb0_add3b_maj3b_or3b_wx1 = mulb0_add3b_maj3b_wx1 | mulb0_add3b_maj3b_wy1;
  assign mulb0_add3b_maj3b_or3b_wx2 = mulb0_add3b_maj3b_wx2 | mulb0_add3b_maj3b_wy2;
  assign mulb0_add3b_maj3b_or3b_wx4 = mulb0_add3b_maj3b_wx4 | mulb0_add3b_maj3b_wy4;
  assign mulb0_add3b_maj3b_wx1 = mulb0_sq2 & mulb0_cq1;
  assign mulb0_add3b_maj3b_wx2 = mulb0_sq3 & mulb0_cq2;
  assign mulb0_add3b_maj3b_wx4 = mulb0_sq5 & mulb0_cq4;
  assign mulb0_add3b_maj3b_wy1 = mulb0_sq2 & sa2;
  assign mulb0_add3b_maj3b_wy2 = mulb0_sq3 & sa2;
  assign mulb0_add3b_maj3b_wy4 = mulb0_sq5 & sa2;
  assign mulb0_add3b_maj3b_xy1 = mulb0_cq1 & sa2;
  assign mulb0_add3b_maj3b_xy2 = mulb0_cq2 & sa2;
  assign mulb0_add3b_maj3b_xy4 = mulb0_cq4 & sa2;
  assign mulb0_add3b_xor3b_wx1 = mulb0_sq2 ^ mulb0_cq1;
  assign mulb0_add3b_xor3b_wx2 = mulb0_sq3 ^ mulb0_cq2;
  assign mulb0_add3b_xor3b_wx4 = mulb0_sq5 ^ mulb0_cq4;
  assign mulb0_cq0 = xn0 & mulb0_cp0;
  assign mulb0_cq1 = xn0 & mulb0_cp1;
  assign mulb0_cq2 = xn0 & mulb0_cp2;
  assign mulb0_cq3 = xn0 & mulb0_cp3;
  assign mulb0_cq4 = xn0 & mulb0_cp4;
  assign mulb0_cq5 = xn0 & mulb0_cp5;
  assign mulb0_cq6 = xn0 & mulb0_cp6;
  assign mulb0_cq7 = xn0 & mulb0_cp7;
  assign mulb0_pc0 = mulb0_sq0 & sa2;
  assign mulb0_pc1 = mulb0_sq1 & mulb0_cq0;
  assign mulb0_pc2 = mulb0_add3b_maj3b_or3b_wx1 | mulb0_add3b_maj3b_xy1;
  assign mulb0_pc3 = mulb0_add3b_maj3b_or3b_wx2 | mulb0_add3b_maj3b_xy2;
  assign mulb0_pc4 = mulb0_sq4 & mulb0_cq3;
  assign mulb0_pc5 = mulb0_add3b_maj3b_or3b_wx4 | mulb0_add3b_maj3b_xy4;
  assign mulb0_pc6 = mulb0_sq6 & mulb0_cq5;
  assign mulb0_pc7 = mulb0_sq7 & mulb0_cq6;
  assign mulb0_ps0 = mulb0_sq1 ^ mulb0_cq0;
  assign mulb0_ps1 = mulb0_add3b_xor3b_wx1 ^ sa2;
  assign mulb0_ps2 = mulb0_add3b_xor3b_wx2 ^ sa2;
  assign mulb0_ps3 = mulb0_sq4 ^ mulb0_cq3;
  assign mulb0_ps4 = mulb0_add3b_xor3b_wx4 ^ sa2;
  assign mulb0_ps5 = mulb0_sq6 ^ mulb0_cq5;
  assign mulb0_ps6 = mulb0_sq7 ^ mulb0_cq6;
  assign mulb0_sq0 = xn0 & mulb0_sp0;
  assign mulb0_sq1 = xn0 & mulb0_sp1;
  assign mulb0_sq2 = xn0 & mulb0_sp2;
  assign mulb0_sq3 = xn0 & mulb0_sp3;
  assign mulb0_sq4 = xn0 & mulb0_sp4;
  assign mulb0_sq5 = xn0 & mulb0_sp5;
  assign mulb0_sq6 = xn0 & mulb0_sp6;
  assign mulb0_sq7 = xn0 & mulb0_sp7;
  assign mulb1_add3_maj3_or3_wx = mulb1_add3_maj3_wx | mulb1_add3_maj3_wy;
  assign mulb1_add3_maj3_wx = qb2 & mulb1_cq5;
  assign mulb1_add3_maj3_wy = qb2 & mulb1_pc5;
  assign mulb1_add3_maj3_xy = mulb1_cq5 & mulb1_pc5;
  assign mulb1_add3_xor3_wx = qb2 ^ mulb1_cq5;
  assign mulb1_add3b_maj3b_or3b_wx0 = mulb1_add3b_maj3b_wx0 | mulb1_add3b_maj3b_wy0;
  assign mulb1_add3b_maj3b_or3b_wx2 = mulb1_add3b_maj3b_wx2 | mulb1_add3b_maj3b_wy2;
  assign mulb1_add3b_maj3b_or3b_wx3 = mulb1_add3b_maj3b_wx3 | mulb1_add3b_maj3b_wy3;
  assign mulb1_add3b_maj3b_wx0 = mulb1_sq1 & mulb1_cq0;
  assign mulb1_add3b_maj3b_wx2 = mulb1_sq3 & mulb1_cq2;
  assign mulb1_add3b_maj3b_wx3 = mulb1_sq4 & mulb1_cq3;
  assign mulb1_add3b_maj3b_wy0 = mulb1_sq1 & qb2;
  assign mulb1_add3b_maj3b_wy2 = mulb1_sq3 & qb2;
  assign mulb1_add3b_maj3b_wy3 = mulb1_sq4 & qb2;
  assign mulb1_add3b_maj3b_xy0 = mulb1_cq0 & qb2;
  assign mulb1_add3b_maj3b_xy2 = mulb1_cq2 & qb2;
  assign mulb1_add3b_maj3b_xy3 = mulb1_cq3 & qb2;
  assign mulb1_add3b_xor3b_wx0 = mulb1_sq1 ^ mulb1_cq0;
  assign mulb1_add3b_xor3b_wx2 = mulb1_sq3 ^ mulb1_cq2;
  assign mulb1_add3b_xor3b_wx3 = mulb1_sq4 ^ mulb1_cq3;
  assign mulb1_cq0 = xn1 & sd1;
  assign mulb1_cq1 = xn1 & sd2;
  assign mulb1_cq2 = xn1 & sd3;
  assign mulb1_cq3 = xn1 & sd4;
  assign mulb1_cq4 = xn1 & sd5;
  assign mulb1_cq5 = xn1 & sd6;
  assign mulb1_pc0 = mulb1_sq0 & qb2;
  assign mulb1_pc1 = mulb1_add3b_maj3b_or3b_wx0 | mulb1_add3b_maj3b_xy0;
  assign mulb1_pc2 = mulb1_sq2 & mulb1_cq1;
  assign mulb1_pc3 = mulb1_add3b_maj3b_or3b_wx2 | mulb1_add3b_maj3b_xy2;
  assign mulb1_pc4 = mulb1_add3b_maj3b_or3b_wx3 | mulb1_add3b_maj3b_xy3;
  assign mulb1_pc5 = mulb1_sq5 & mulb1_cq4;
  assign mulb1_ps0 = mulb1_add3b_xor3b_wx0 ^ qb2;
  assign mulb1_ps1 = mulb1_sq2 ^ mulb1_cq1;
  assign mulb1_ps2 = mulb1_add3b_xor3b_wx2 ^ qb2;
  assign mulb1_ps3 = mulb1_add3b_xor3b_wx3 ^ qb2;
  assign mulb1_ps4 = mulb1_sq5 ^ mulb1_cq4;
  assign mulb1_sq0 = xn1 & sc0;
  assign mulb1_sq1 = xn1 & sc1;
  assign mulb1_sq2 = xn1 & sc2;
  assign mulb1_sq3 = xn1 & sc3;
  assign mulb1_sq4 = xn1 & sc4;
  assign mulb1_sq5 = xn1 & sc5;
  assign mulsc_mulb_add3_maj3_or3_wx = mulsc_mulb_add3_maj3_wx | mulsc_mulb_add3_maj3_wy;
  assign mulsc_mulb_add3_maj3_wx = mulsc_mulb_yoc6 & mulsc_mulb_cq6;
  assign mulsc_mulb_add3_maj3_wy = mulsc_mulb_yoc6 & mulsc_mulb_pc6;
  assign mulsc_mulb_add3_maj3_xy = mulsc_mulb_cq6 & mulsc_mulb_pc6;
  assign mulsc_mulb_add3_xor3_wx = mulsc_mulb_yoc6 ^ mulsc_mulb_cq6;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx0 = mulsc_mulb_add3b0_maj3b_wx0 | mulsc_mulb_add3b0_maj3b_wy0;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx1 = mulsc_mulb_add3b0_maj3b_wx1 | mulsc_mulb_add3b0_maj3b_wy1;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx2 = mulsc_mulb_add3b0_maj3b_wx2 | mulsc_mulb_add3b0_maj3b_wy2;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx3 = mulsc_mulb_add3b0_maj3b_wx3 | mulsc_mulb_add3b0_maj3b_wy3;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx4 = mulsc_mulb_add3b0_maj3b_wx4 | mulsc_mulb_add3b0_maj3b_wy4;
  assign mulsc_mulb_add3b0_maj3b_or3b_wx5 = mulsc_mulb_add3b0_maj3b_wx5 | mulsc_mulb_add3b0_maj3b_wy5;
  assign mulsc_mulb_add3b0_maj3b_wx0 = mulsc_mulb_sq1 & mulsc_mulb_cq0;
  assign mulsc_mulb_add3b0_maj3b_wx1 = mulsc_mulb_sq2 & mulsc_mulb_cq1;
  assign mulsc_mulb_add3b0_maj3b_wx2 = mulsc_mulb_sq3 & mulsc_mulb_cq2;
  assign mulsc_mulb_add3b0_maj3b_wx3 = mulsc_mulb_sq4 & mulsc_mulb_cq3;
  assign mulsc_mulb_add3b0_maj3b_wx4 = mulsc_mulb_sq5 & mulsc_mulb_cq4;
  assign mulsc_mulb_add3b0_maj3b_wx5 = mulsc_mulb_sq6 & mulsc_mulb_cq5;
  assign mulsc_mulb_add3b0_maj3b_wy0 = mulsc_mulb_sq1 & mulsc_mulb_yos1;
  assign mulsc_mulb_add3b0_maj3b_wy1 = mulsc_mulb_sq2 & mulsc_mulb_yos2;
  assign mulsc_mulb_add3b0_maj3b_wy2 = mulsc_mulb_sq3 & mulsc_mulb_yos3;
  assign mulsc_mulb_add3b0_maj3b_wy3 = mulsc_mulb_sq4 & mulsc_mulb_yos4;
  assign mulsc_mulb_add3b0_maj3b_wy4 = mulsc_mulb_sq5 & mulsc_mulb_yos5;
  assign mulsc_mulb_add3b0_maj3b_wy5 = mulsc_mulb_sq6 & mulsc_mulb_yos6;
  assign mulsc_mulb_add3b0_maj3b_xy0 = mulsc_mulb_cq0 & mulsc_mulb_yos1;
  assign mulsc_mulb_add3b0_maj3b_xy1 = mulsc_mulb_cq1 & mulsc_mulb_yos2;
  assign mulsc_mulb_add3b0_maj3b_xy2 = mulsc_mulb_cq2 & mulsc_mulb_yos3;
  assign mulsc_mulb_add3b0_maj3b_xy3 = mulsc_mulb_cq3 & mulsc_mulb_yos4;
  assign mulsc_mulb_add3b0_maj3b_xy4 = mulsc_mulb_cq4 & mulsc_mulb_yos5;
  assign mulsc_mulb_add3b0_maj3b_xy5 = mulsc_mulb_cq5 & mulsc_mulb_yos6;
  assign mulsc_mulb_add3b0_xor3b_wx0 = mulsc_mulb_sq1 ^ mulsc_mulb_cq0;
  assign mulsc_mulb_add3b0_xor3b_wx1 = mulsc_mulb_sq2 ^ mulsc_mulb_cq1;
  assign mulsc_mulb_add3b0_xor3b_wx2 = mulsc_mulb_sq3 ^ mulsc_mulb_cq2;
  assign mulsc_mulb_add3b0_xor3b_wx3 = mulsc_mulb_sq4 ^ mulsc_mulb_cq3;
  assign mulsc_mulb_add3b0_xor3b_wx4 = mulsc_mulb_sq5 ^ mulsc_mulb_cq4;
  assign mulsc_mulb_add3b0_xor3b_wx5 = mulsc_mulb_sq6 ^ mulsc_mulb_cq5;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx0 = mulsc_mulb_add3b1_maj3b_wx0 | mulsc_mulb_add3b1_maj3b_wy0;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx1 = mulsc_mulb_add3b1_maj3b_wx1 | mulsc_mulb_add3b1_maj3b_wy1;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx2 = mulsc_mulb_add3b1_maj3b_wx2 | mulsc_mulb_add3b1_maj3b_wy2;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx3 = mulsc_mulb_add3b1_maj3b_wx3 | mulsc_mulb_add3b1_maj3b_wy3;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx4 = mulsc_mulb_add3b1_maj3b_wx4 | mulsc_mulb_add3b1_maj3b_wy4;
  assign mulsc_mulb_add3b1_maj3b_or3b_wx5 = mulsc_mulb_add3b1_maj3b_wx5 | mulsc_mulb_add3b1_maj3b_wy5;
  assign mulsc_mulb_add3b1_maj3b_wx0 = mulsc_mulb_yoc0 & mulsc_mulb_ps0;
  assign mulsc_mulb_add3b1_maj3b_wx1 = mulsc_mulb_yoc1 & mulsc_mulb_ps1;
  assign mulsc_mulb_add3b1_maj3b_wx2 = mulsc_mulb_yoc2 & mulsc_mulb_ps2;
  assign mulsc_mulb_add3b1_maj3b_wx3 = mulsc_mulb_yoc3 & mulsc_mulb_ps3;
  assign mulsc_mulb_add3b1_maj3b_wx4 = mulsc_mulb_yoc4 & mulsc_mulb_ps4;
  assign mulsc_mulb_add3b1_maj3b_wx5 = mulsc_mulb_yoc5 & mulsc_mulb_ps5;
  assign mulsc_mulb_add3b1_maj3b_wy0 = mulsc_mulb_yoc0 & mulsc_mulb_pc0;
  assign mulsc_mulb_add3b1_maj3b_wy1 = mulsc_mulb_yoc1 & mulsc_mulb_pc1;
  assign mulsc_mulb_add3b1_maj3b_wy2 = mulsc_mulb_yoc2 & mulsc_mulb_pc2;
  assign mulsc_mulb_add3b1_maj3b_wy3 = mulsc_mulb_yoc3 & mulsc_mulb_pc3;
  assign mulsc_mulb_add3b1_maj3b_wy4 = mulsc_mulb_yoc4 & mulsc_mulb_pc4;
  assign mulsc_mulb_add3b1_maj3b_wy5 = mulsc_mulb_yoc5 & mulsc_mulb_pc5;
  assign mulsc_mulb_add3b1_maj3b_xy0 = mulsc_mulb_ps0 & mulsc_mulb_pc0;
  assign mulsc_mulb_add3b1_maj3b_xy1 = mulsc_mulb_ps1 & mulsc_mulb_pc1;
  assign mulsc_mulb_add3b1_maj3b_xy2 = mulsc_mulb_ps2 & mulsc_mulb_pc2;
  assign mulsc_mulb_add3b1_maj3b_xy3 = mulsc_mulb_ps3 & mulsc_mulb_pc3;
  assign mulsc_mulb_add3b1_maj3b_xy4 = mulsc_mulb_ps4 & mulsc_mulb_pc4;
  assign mulsc_mulb_add3b1_maj3b_xy5 = mulsc_mulb_ps5 & mulsc_mulb_pc5;
  assign mulsc_mulb_add3b1_xor3b_wx0 = mulsc_mulb_yoc0 ^ mulsc_mulb_ps0;
  assign mulsc_mulb_add3b1_xor3b_wx1 = mulsc_mulb_yoc1 ^ mulsc_mulb_ps1;
  assign mulsc_mulb_add3b1_xor3b_wx2 = mulsc_mulb_yoc2 ^ mulsc_mulb_ps2;
  assign mulsc_mulb_add3b1_xor3b_wx3 = mulsc_mulb_yoc3 ^ mulsc_mulb_ps3;
  assign mulsc_mulb_add3b1_xor3b_wx4 = mulsc_mulb_yoc4 ^ mulsc_mulb_ps4;
  assign mulsc_mulb_add3b1_xor3b_wx5 = mulsc_mulb_yoc5 ^ mulsc_mulb_ps5;
  assign mulsc_mulb_cq0 = xn2 & sb0;
  assign mulsc_mulb_cq1 = xn2 & sb1;
  assign mulsc_mulb_cq2 = xn2 & sb2;
  assign mulsc_mulb_cq3 = xn2 & sb3;
  assign mulsc_mulb_cq4 = xn2 & mulsc_mulb_cp4;
  assign mulsc_mulb_cq5 = xn2 & mulsc_mulb_cp5;
  assign mulsc_mulb_cq6 = xn2 & mulsc_mulb_cp6;
  assign mulsc_mulb_pc0 = mulsc_mulb_sq0 & mulsc_mulb_yos0;
  assign mulsc_mulb_pc1 = mulsc_mulb_add3b0_maj3b_or3b_wx0 | mulsc_mulb_add3b0_maj3b_xy0;
  assign mulsc_mulb_pc2 = mulsc_mulb_add3b0_maj3b_or3b_wx1 | mulsc_mulb_add3b0_maj3b_xy1;
  assign mulsc_mulb_pc3 = mulsc_mulb_add3b0_maj3b_or3b_wx2 | mulsc_mulb_add3b0_maj3b_xy2;
  assign mulsc_mulb_pc4 = mulsc_mulb_add3b0_maj3b_or3b_wx3 | mulsc_mulb_add3b0_maj3b_xy3;
  assign mulsc_mulb_pc5 = mulsc_mulb_add3b0_maj3b_or3b_wx4 | mulsc_mulb_add3b0_maj3b_xy4;
  assign mulsc_mulb_pc6 = mulsc_mulb_add3b0_maj3b_or3b_wx5 | mulsc_mulb_add3b0_maj3b_xy5;
  assign mulsc_mulb_ps0 = mulsc_mulb_add3b0_xor3b_wx0 ^ mulsc_mulb_yos1;
  assign mulsc_mulb_ps1 = mulsc_mulb_add3b0_xor3b_wx1 ^ mulsc_mulb_yos2;
  assign mulsc_mulb_ps2 = mulsc_mulb_add3b0_xor3b_wx2 ^ mulsc_mulb_yos3;
  assign mulsc_mulb_ps3 = mulsc_mulb_add3b0_xor3b_wx3 ^ mulsc_mulb_yos4;
  assign mulsc_mulb_ps4 = mulsc_mulb_add3b0_xor3b_wx4 ^ mulsc_mulb_yos5;
  assign mulsc_mulb_ps5 = mulsc_mulb_add3b0_xor3b_wx5 ^ mulsc_mulb_yos6;
  assign mulsc_mulb_sq0 = xn2 & sa4;
  assign mulsc_mulb_sq1 = xn2 & sa5;
  assign mulsc_mulb_sq2 = xn2 & sa6;
  assign mulsc_mulb_sq3 = xn2 & sa7;
  assign mulsc_mulb_sq4 = xn2 & sa8;
  assign mulsc_mulb_sq5 = xn2 & mulsc_mulb_sp5;
  assign mulsc_mulb_sq6 = xn2 & mulsc_mulb_sp6;
  assign mulsc_mulb_yoc0 = mulsc_xbd & yc[0];
  assign mulsc_mulb_yoc1 = mulsc_xbd & yc[1];
  assign mulsc_mulb_yoc2 = mulsc_xbd & yc[2];
  assign mulsc_mulb_yoc3 = mulsc_xbd & yc[3];
  assign mulsc_mulb_yoc4 = mulsc_xbd & yc[4];
  assign mulsc_mulb_yoc5 = mulsc_xbd & yc[5];
  assign mulsc_mulb_yoc6 = mulsc_xbd & yc[6];
  assign mulsc_mulb_yos0 = mulsc_xbd & ys[0];
  assign mulsc_mulb_yos1 = mulsc_xbd & ys[1];
  assign mulsc_mulb_yos2 = mulsc_xbd & ys[2];
  assign mulsc_mulb_yos3 = mulsc_xbd & ys[3];
  assign mulsc_mulb_yos4 = mulsc_xbd & ys[4];
  assign mulsc_mulb_yos5 = mulsc_xbd & ys[5];
  assign mulsc_mulb_yos6 = mulsc_xbd & ys[6];
  assign mulsc_shrsc_cq0 = mulsc_shrsc_sp0 & mulsc_shrsc_cp0;
  assign mulsc_shrsc_cq1 = mulsc_shrsc_sp1 & mulsc_shrsc_cp1;
  assign mulsc_shrsc_cq2 = mulsc_shrsc_sp2 & mulsc_shrsc_cp2;
  assign mulsc_shrsc_cq3 = mulsc_shrsc_sp3 & mulsc_shrsc_cp3;
  assign mulsc_shrsc_cq4 = mulsc_shrsc_sp4 & mulsc_shrsc_cp4;
  assign mulsc_shrsc_cq5 = mulsc_shrsc_sp5 & mulsc_shrsc_cp5;
  assign mulsc_shrsc_cr0 = ld ? xc[0] : mulsc_shrsc_cq0;
  assign mulsc_shrsc_cr1 = ld ? xc[1] : mulsc_shrsc_cq1;
  assign mulsc_shrsc_cr2 = ld ? xc[2] : mulsc_shrsc_cq2;
  assign mulsc_shrsc_cr3 = ld ? xc[3] : mulsc_shrsc_cq3;
  assign mulsc_shrsc_cr4 = ld ? xc[4] : mulsc_shrsc_cq4;
  assign mulsc_shrsc_cr5 = ld ? xc[5] : mulsc_shrsc_cq5;
  assign mulsc_shrsc_cr6 = ld & xc[6];
  assign mulsc_shrsc_sq0 = mulsc_shrsc_sp0 ^ mulsc_shrsc_cp0;
  assign mulsc_shrsc_sq1 = mulsc_shrsc_sp1 ^ mulsc_shrsc_cp1;
  assign mulsc_shrsc_sq2 = mulsc_shrsc_sp2 ^ mulsc_shrsc_cp2;
  assign mulsc_shrsc_sq3 = mulsc_shrsc_sp3 ^ mulsc_shrsc_cp3;
  assign mulsc_shrsc_sq4 = mulsc_shrsc_sp4 ^ mulsc_shrsc_cp4;
  assign mulsc_shrsc_sq5 = mulsc_shrsc_sp5 ^ mulsc_shrsc_cp5;
  assign mulsc_shrsc_sr0 = ld ? xs[1] : mulsc_shrsc_sq1;
  assign mulsc_shrsc_sr1 = ld ? xs[2] : mulsc_shrsc_sq2;
  assign mulsc_shrsc_sr2 = ld ? xs[3] : mulsc_shrsc_sq3;
  assign mulsc_shrsc_sr3 = ld ? xs[4] : mulsc_shrsc_sq4;
  assign mulsc_shrsc_sr4 = ld ? xs[5] : mulsc_shrsc_sq5;
  assign mulsc_shrsc_sr5 = ld ? xs[6] : mulsc_shrsc_cp6;
  assign mulsc_xb = ld ? xs[0] : mulsc_shrsc_sq0;
  assign mw = add3_maj3_or3_wx | add3_maj3_xy;
  assign or3_wx = sb3 | sa8;
  assign pb = mulsc_mulb_sq0 ^ mulsc_mulb_yos0;
  assign pc0 = mulsc_mulb_add3b1_maj3b_or3b_wx0 | mulsc_mulb_add3b1_maj3b_xy0;
  assign pc1 = mulsc_mulb_add3b1_maj3b_or3b_wx1 | mulsc_mulb_add3b1_maj3b_xy1;
  assign pc2 = mulsc_mulb_add3b1_maj3b_or3b_wx2 | mulsc_mulb_add3b1_maj3b_xy2;
  assign pc3 = mulsc_mulb_add3b1_maj3b_or3b_wx3 | mulsc_mulb_add3b1_maj3b_xy3;
  assign pc4 = mulsc_mulb_add3b1_maj3b_or3b_wx4 | mulsc_mulb_add3b1_maj3b_xy4;
  assign pc5 = mulsc_mulb_add3b1_maj3b_or3b_wx5 | mulsc_mulb_add3b1_maj3b_xy5;
  assign pc6 = mulsc_mulb_add3_maj3_or3_wx | mulsc_mulb_add3_maj3_xy;
  assign ps0 = mulsc_mulb_add3b1_xor3b_wx0 ^ mulsc_mulb_pc0;
  assign ps1 = mulsc_mulb_add3b1_xor3b_wx1 ^ mulsc_mulb_pc1;
  assign ps2 = mulsc_mulb_add3b1_xor3b_wx2 ^ mulsc_mulb_pc2;
  assign ps3 = mulsc_mulb_add3b1_xor3b_wx3 ^ mulsc_mulb_pc3;
  assign ps4 = mulsc_mulb_add3b1_xor3b_wx4 ^ mulsc_mulb_pc4;
  assign ps5 = mulsc_mulb_add3b1_xor3b_wx5 ^ mulsc_mulb_pc5;
  assign ps6 = mulsc_mulb_add3_xor3_wx ^ mulsc_mulb_pc6;
  assign qb = mulb0_sq0 ^ sa2;
  assign qc0 = mulb0_ps0 & mulb0_pc0;
  assign qc1 = mulb0_ps1 & mulb0_pc1;
  assign qc2 = mulb0_ps2 & mulb0_pc2;
  assign qc3 = mulb0_ps3 & mulb0_pc3;
  assign qc4 = mulb0_ps4 & mulb0_pc4;
  assign qc5 = mulb0_ps5 & mulb0_pc5;
  assign qc6 = mulb0_ps6 & mulb0_pc6;
  assign qc7 = mulb0_cq7 & mulb0_pc7;
  assign qs0 = mulb0_ps0 ^ mulb0_pc0;
  assign qs1 = mulb0_ps1 ^ mulb0_pc1;
  assign qs2 = mulb0_ps2 ^ mulb0_pc2;
  assign qs3 = mulb0_ps3 ^ mulb0_pc3;
  assign qs4 = mulb0_ps4 ^ mulb0_pc4;
  assign qs5 = mulb0_ps5 ^ mulb0_pc5;
  assign qs6 = mulb0_ps6 ^ mulb0_pc6;
  assign qs7 = mulb0_cq7 ^ mulb0_pc7;
  assign sticky_q = xn1 & sd0;
  assign vb = mulb1_sq0 ^ qb2;
  assign vc0 = mulb1_ps0 & mulb1_pc0;
  assign vc1 = mulb1_ps1 & mulb1_pc1;
  assign vc2 = mulb1_ps2 & mulb1_pc2;
  assign vc3 = mulb1_ps3 & mulb1_pc3;
  assign vc4 = mulb1_ps4 & mulb1_pc4;
  assign vc5 = mulb1_add3_maj3_or3_wx | mulb1_add3_maj3_xy;
  assign vs0 = mulb1_ps0 ^ mulb1_pc0;
  assign vs1 = mulb1_ps1 ^ mulb1_pc1;
  assign vs2 = mulb1_ps2 ^ mulb1_pc2;
  assign vs3 = mulb1_ps3 ^ mulb1_pc3;
  assign vs4 = mulb1_ps4 ^ mulb1_pc4;
  assign vs5 = mulb1_add3_xor3_wx ^ mulb1_pc5;
  assign vt = vb | sticky_q;
  assign xn0 = ~ld1;
  assign xn1 = ~ld2;
  assign xn2 = ~mulsc_ldd;
  assign zc0_o = add3b0_maj3b_or3b_wx0 | add3b0_maj3b_xy0;
  assign zc1_o = add3b0_maj3b_or3b_wx1 | add3b0_maj3b_xy1;
  assign zc2_o = add3b0_maj3b_or3b_wx2 | add3b0_maj3b_xy2;
  assign zc3_o = add3b0_maj3b_or3b_wx3 | add3b0_maj3b_xy3;
  assign zc5_o = add3b1_maj3b_or3b_wx0 | add3b1_maj3b_xy0;
  assign zc6_o = add3b1_maj3b_or3b_wx1 | add3b1_maj3b_xy1;
  assign zc7_o = or3_wx | mw;
  assign zs0_o = add3b0_xor3b_wx0 ^ sd0;
  assign zs1_o = add3b0_xor3b_wx1 ^ sd1;
  assign zs2_o = add3b0_xor3b_wx2 ^ sd2;
  assign zs3_o = add3b0_xor3b_wx3 ^ sd3;
  assign zs4_o = add3b0_xor3b_wx4 ^ sd4;
  assign zs5_o = add3b1_xor3b_wx0 ^ mc4;
  assign zs6_o = add3b1_xor3b_wx1 ^ mc5;
  assign zs7_o = add3_xor3_wx ^ mc6;
  assign zs[0] = zs0_o;
  assign zs[1] = zs1_o;
  assign zs[2] = zs2_o;
  assign zs[3] = zs3_o;
  assign zs[4] = zs4_o;
  assign zs[5] = zs5_o;
  assign zs[6] = zs6_o;
  assign zs[7] = zs7_o;
  assign zc[0] = zc0_o;
  assign zc[1] = zc1_o;
  assign zc[2] = zc2_o;
  assign zc[3] = zc3_o;
  assign zc[4] = 1'b0;
  assign zc[5] = zc5_o;
  assign zc[6] = zc6_o;
  assign zc[7] = zc7_o;

  always @(posedge clk)
    begin
      ld1 <= pipe0_x3;
      ld2 <= pipe1_x1;
      mulb0_cp0 <= qc0;
      mulb0_cp1 <= qc1;
      mulb0_cp2 <= qc2;
      mulb0_cp3 <= qc3;
      mulb0_cp4 <= qc4;
      mulb0_cp5 <= qc5;
      mulb0_cp6 <= qc6;
      mulb0_cp7 <= qc7;
      mulb0_sp0 <= qs0;
      mulb0_sp1 <= qs1;
      mulb0_sp2 <= qs2;
      mulb0_sp3 <= qs3;
      mulb0_sp4 <= qs4;
      mulb0_sp5 <= qs5;
      mulb0_sp6 <= qs6;
      mulb0_sp7 <= qs7;
      mulsc_ldd <= pipe0_x1;
      mulsc_mulb_cp4 <= pc4;
      mulsc_mulb_cp5 <= pc5;
      mulsc_mulb_cp6 <= pc6;
      mulsc_mulb_sp5 <= ps5;
      mulsc_mulb_sp6 <= ps6;
      mulsc_pipe_x1 <= mulsc_xb;
      mulsc_shrsc_cp0 <= mulsc_shrsc_cr0;
      mulsc_shrsc_cp1 <= mulsc_shrsc_cr1;
      mulsc_shrsc_cp2 <= mulsc_shrsc_cr2;
      mulsc_shrsc_cp3 <= mulsc_shrsc_cr3;
      mulsc_shrsc_cp4 <= mulsc_shrsc_cr4;
      mulsc_shrsc_cp5 <= mulsc_shrsc_cr5;
      mulsc_shrsc_cp6 <= mulsc_shrsc_cr6;
      mulsc_shrsc_sp0 <= mulsc_shrsc_sr0;
      mulsc_shrsc_sp1 <= mulsc_shrsc_sr1;
      mulsc_shrsc_sp2 <= mulsc_shrsc_sr2;
      mulsc_shrsc_sp3 <= mulsc_shrsc_sr3;
      mulsc_shrsc_sp4 <= mulsc_shrsc_sr4;
      mulsc_shrsc_sp5 <= mulsc_shrsc_sr5;
      mulsc_xbd <= mulsc_pipe_x1;
      pipe0_x1 <= ld;
      pipe0_x3 <= mulsc_ldd;
      pipe1_x1 <= ld1;
      pipe2_x1 <= qb;
      qb2 <= pipe2_x1;
      sa0 <= sa1;
      sa1 <= sa2;
      sa2 <= sa3;
      sa3 <= pb;
      sa4 <= ps0;
      sa5 <= ps1;
      sa6 <= ps2;
      sa7 <= ps3;
      sa8 <= ps4;
      sb0 <= pc0;
      sb1 <= pc1;
      sb2 <= pc2;
      sb3 <= pc3;
      sc0 <= vs0;
      sc1 <= vs1;
      sc2 <= vs2;
      sc3 <= vs3;
      sc4 <= vs4;
      sc5 <= vs5;
      sd0 <= vt;
      sd1 <= vc0;
      sd2 <= vc1;
      sd3 <= vc2;
      sd4 <= vc3;
      sd5 <= vc4;
      sd6 <= vc5;
    end

endmodule  // montgomery_reduce_91

/*----------------------------------------------------------------------------+
| Primary inputs: 29                                                          |
| Primary outputs: 16                                                         |
| Registers: 70                                                               |
| Gates: 338                                                                  |
| Fan-in: 25%=3 50%=5 75%=6 90%=9 95%=9 99%=9 max=9 (mulsc_mulb_cp5)          |
| Fan-in cone: 25%=2 50%=7 75%=12 90%=17 95%=17 99%=20                        |
|   max=20 (mulsc_mulb_cp5)                                                   |
| Fan-out: 25%=2 50%=4 75%=5 90%=8 95%=13 99%=16 max=18 (ld1)                 |
| Duplication: 25%=1 50%=1 75%=1 90%=1 95%=3 99%=4 max=4 (ld1)                |
| Fan-out load: 25%=2 50%=4 75%=4 90%=6 95%=7 99%=8 max=15 (ld)               |
+----------------------------------------------------------------------------*/

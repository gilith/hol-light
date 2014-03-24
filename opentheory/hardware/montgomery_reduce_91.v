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

  reg mulb1_cp0;
  reg mulb1_cp1;
  reg mulb1_cp2;
  reg mulb1_cp3;
  reg mulb1_cp4;
  reg mulb1_cp5;
  reg mulb1_cp6;
  reg mulb1_cp7;
  reg mulb1_sp0;
  reg mulb1_sp1;
  reg mulb1_sp2;
  reg mulb1_sp3;
  reg mulb1_sp4;
  reg mulb1_sp5;
  reg mulb1_sp6;
  reg mulb1_sp7;
  reg mulsc_mulb_cp4;
  reg mulsc_mulb_cp5;
  reg mulsc_mulb_cp6;
  reg mulsc_mulb_sp5;
  reg mulsc_mulb_sp6;
  reg mulsc_pipe_pipeb_xp0;
  reg mulsc_pipe_pipeb_xp1;
  reg mulsc_shrsc_cp0;
  reg mulsc_shrsc_cp1;
  reg mulsc_shrsc_cp2;
  reg mulsc_shrsc_cp3;
  reg mulsc_shrsc_cp4;
  reg mulsc_shrsc_cp5;
  reg mulsc_shrsc_sp0;
  reg mulsc_shrsc_sp1;
  reg mulsc_shrsc_sp2;
  reg mulsc_shrsc_sp3;
  reg mulsc_shrsc_sp4;
  reg mulsc_shrsc_sp5;
  reg mulsc_shrsc_sq6;
  reg pipe0_pipeb_xp0;
  reg pipe0_pipeb_xp1;
  reg pipe0_pipeb_xp2;
  reg pipe1_pipeb_xp0;
  reg pipe1_pipeb_xp1;
  reg pipe1_x0;
  reg pipe2_pipeb_xp0;
  reg pipe2_pipeb_xp1;
  reg pipeb_xp0;
  reg pipeb_xp1;
  reg pipeb_xp2;
  reg pipeb_xp3;
  reg sa4;
  reg sa5;
  reg sa6;
  reg sa7;
  reg sa8;
  reg sb0;
  reg sb1;
  reg sb2;
  reg sb3;
  reg sc0;
  reg sc1;
  reg sc2;
  reg sc3;
  reg sc4;
  reg sc5;
  reg sd0;
  reg sd1;
  reg sd2;
  reg sd3;
  reg sd4;
  reg sd5;
  reg sd6;

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
  wire mulb0_add3_maj3_or3_wx;
  wire mulb0_add3_maj3_wx;
  wire mulb0_add3_maj3_wy;
  wire mulb0_add3_maj3_xy;
  wire mulb0_add3_xor3_wx;
  wire mulb0_add3b0_maj3b_or3b_wx0;
  wire mulb0_add3b0_maj3b_or3b_wx2;
  wire mulb0_add3b0_maj3b_or3b_wx3;
  wire mulb0_add3b0_maj3b_wx0;
  wire mulb0_add3b0_maj3b_wx1;
  wire mulb0_add3b0_maj3b_wx2;
  wire mulb0_add3b0_maj3b_wx3;
  wire mulb0_add3b0_maj3b_wx4;
  wire mulb0_add3b0_maj3b_wy0;
  wire mulb0_add3b0_maj3b_wy2;
  wire mulb0_add3b0_maj3b_wy3;
  wire mulb0_add3b0_maj3b_xy0;
  wire mulb0_add3b0_maj3b_xy2;
  wire mulb0_add3b0_maj3b_xy3;
  wire mulb0_add3b0_xor3b_wx0;
  wire mulb0_add3b0_xor3b_wx1;
  wire mulb0_add3b0_xor3b_wx2;
  wire mulb0_add3b0_xor3b_wx3;
  wire mulb0_add3b0_xor3b_wx4;
  wire mulb0_add3b1_maj3b_xy0;
  wire mulb0_add3b1_maj3b_xy1;
  wire mulb0_add3b1_maj3b_xy2;
  wire mulb0_add3b1_maj3b_xy3;
  wire mulb0_add3b1_maj3b_xy4;
  wire mulb0_cq0;
  wire mulb0_cq1;
  wire mulb0_cq2;
  wire mulb0_cq3;
  wire mulb0_cq4;
  wire mulb0_cq5;
  wire mulb0_cr5;
  wire mulb0_pc0;
  wire mulb0_pc1;
  wire mulb0_pc3;
  wire mulb0_pc4;
  wire mulb0_ps0;
  wire mulb0_ps2;
  wire mulb0_ps3;
  wire mulb0_sq0;
  wire mulb0_sq1;
  wire mulb0_sq2;
  wire mulb0_sq3;
  wire mulb0_sq4;
  wire mulb0_sq5;
  wire mulb0_sr0;
  wire mulb0_sr1;
  wire mulb0_sr2;
  wire mulb0_sr3;
  wire mulb0_sr4;
  wire mulb0_sr5;
  wire mulb0_xn;
  wire mulb1_add3_maj3_xy;
  wire mulb1_add3b0_maj3b_xy0;
  wire mulb1_add3b0_maj3b_xy1;
  wire mulb1_add3b0_maj3b_xy2;
  wire mulb1_add3b0_maj3b_xy3;
  wire mulb1_add3b0_maj3b_xy4;
  wire mulb1_add3b0_maj3b_xy5;
  wire mulb1_add3b0_maj3b_xy6;
  wire mulb1_add3b1_maj3b_or3b_wx1;
  wire mulb1_add3b1_maj3b_or3b_wx2;
  wire mulb1_add3b1_maj3b_or3b_wx4;
  wire mulb1_add3b1_maj3b_wx0;
  wire mulb1_add3b1_maj3b_wx1;
  wire mulb1_add3b1_maj3b_wx2;
  wire mulb1_add3b1_maj3b_wx3;
  wire mulb1_add3b1_maj3b_wx4;
  wire mulb1_add3b1_maj3b_wx5;
  wire mulb1_add3b1_maj3b_wx6;
  wire mulb1_add3b1_maj3b_wy1;
  wire mulb1_add3b1_maj3b_wy2;
  wire mulb1_add3b1_maj3b_wy4;
  wire mulb1_add3b1_maj3b_xy1;
  wire mulb1_add3b1_maj3b_xy2;
  wire mulb1_add3b1_maj3b_xy4;
  wire mulb1_add3b1_xor3b_wx0;
  wire mulb1_add3b1_xor3b_wx1;
  wire mulb1_add3b1_xor3b_wx2;
  wire mulb1_add3b1_xor3b_wx3;
  wire mulb1_add3b1_xor3b_wx4;
  wire mulb1_add3b1_xor3b_wx5;
  wire mulb1_add3b1_xor3b_wx6;
  wire mulb1_cq0;
  wire mulb1_cq1;
  wire mulb1_cq2;
  wire mulb1_cq3;
  wire mulb1_cq4;
  wire mulb1_cq5;
  wire mulb1_cq6;
  wire mulb1_cq7;
  wire mulb1_pc0;
  wire mulb1_pc2;
  wire mulb1_pc3;
  wire mulb1_pc5;
  wire mulb1_ps1;
  wire mulb1_ps2;
  wire mulb1_ps4;
  wire mulb1_sq0;
  wire mulb1_sq1;
  wire mulb1_sq2;
  wire mulb1_sq3;
  wire mulb1_sq4;
  wire mulb1_sq5;
  wire mulb1_sq6;
  wire mulb1_sq7;
  wire mulb1_sr0;
  wire mulb1_sr1;
  wire mulb1_sr2;
  wire mulb1_sr3;
  wire mulb1_sr4;
  wire mulb1_sr5;
  wire mulb1_sr6;
  wire mulb1_sr7;
  wire mulb1_xn0;
  wire mulb1_xn1;
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
  wire mulsc_mulb_cr0;
  wire mulsc_mulb_cr1;
  wire mulsc_mulb_cr2;
  wire mulsc_mulb_cr3;
  wire mulsc_mulb_cr4;
  wire mulsc_mulb_cr5;
  wire mulsc_mulb_cr6;
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
  wire mulsc_mulb_sr0;
  wire mulsc_mulb_sr1;
  wire mulsc_mulb_sr2;
  wire mulsc_mulb_sr3;
  wire mulsc_mulb_sr4;
  wire mulsc_mulb_sr5;
  wire mulsc_mulb_sr6;
  wire mulsc_mulb_xn;
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
  wire mulsc_pipe_x0;
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
  wire mw;
  wire or3_wx;
  wire pbp0;
  wire pipe2_x0;
  wire sticky_q;
  wire sticky_r;
  wire sticky_xn;
  wire vb;
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
  assign add3b0_maj3b_wx0 = pipeb_xp3 & sc0;
  assign add3b0_maj3b_wx1 = pipeb_xp2 & sc1;
  assign add3b0_maj3b_wx2 = pipeb_xp1 & sc2;
  assign add3b0_maj3b_wx3 = pipeb_xp0 & sc3;
  assign add3b0_maj3b_wx4 = sa4 & sc4;
  assign add3b0_maj3b_wx5 = sa5 & sc5;
  assign add3b0_maj3b_wy0 = pipeb_xp3 & sd0;
  assign add3b0_maj3b_wy1 = pipeb_xp2 & sd1;
  assign add3b0_maj3b_wy2 = pipeb_xp1 & sd2;
  assign add3b0_maj3b_wy3 = pipeb_xp0 & sd3;
  assign add3b0_maj3b_wy4 = sa4 & sd4;
  assign add3b0_maj3b_wy5 = sa5 & sd5;
  assign add3b0_maj3b_xy0 = sc0 & sd0;
  assign add3b0_maj3b_xy1 = sc1 & sd1;
  assign add3b0_maj3b_xy2 = sc2 & sd2;
  assign add3b0_maj3b_xy3 = sc3 & sd3;
  assign add3b0_maj3b_xy4 = sc4 & sd4;
  assign add3b0_maj3b_xy5 = sc5 & sd5;
  assign add3b0_xor3b_wx0 = pipeb_xp3 ^ sc0;
  assign add3b0_xor3b_wx1 = pipeb_xp2 ^ sc1;
  assign add3b0_xor3b_wx2 = pipeb_xp1 ^ sc2;
  assign add3b0_xor3b_wx3 = pipeb_xp0 ^ sc3;
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
  assign mulb0_add3_maj3_or3_wx = mulb0_add3_maj3_wx | mulb0_add3_maj3_wy;
  assign mulb0_add3_maj3_wx = pipe2_pipeb_xp1 & mulb0_cq5;
  assign mulb0_add3_maj3_wy = pipe2_pipeb_xp1 & mulb0_add3b0_maj3b_wx4;
  assign mulb0_add3_maj3_xy = mulb0_cq5 & mulb0_add3b0_maj3b_wx4;
  assign mulb0_add3_xor3_wx = pipe2_pipeb_xp1 ^ mulb0_cq5;
  assign mulb0_add3b0_maj3b_or3b_wx0 = mulb0_add3b0_maj3b_wx0 | mulb0_add3b0_maj3b_wy0;
  assign mulb0_add3b0_maj3b_or3b_wx2 = mulb0_add3b0_maj3b_wx2 | mulb0_add3b0_maj3b_wy2;
  assign mulb0_add3b0_maj3b_or3b_wx3 = mulb0_add3b0_maj3b_wx3 | mulb0_add3b0_maj3b_wy3;
  assign mulb0_add3b0_maj3b_wx0 = mulb0_sq1 & mulb0_cq0;
  assign mulb0_add3b0_maj3b_wx1 = mulb0_sq2 & mulb0_cq1;
  assign mulb0_add3b0_maj3b_wx2 = mulb0_sq3 & mulb0_cq2;
  assign mulb0_add3b0_maj3b_wx3 = mulb0_sq4 & mulb0_cq3;
  assign mulb0_add3b0_maj3b_wx4 = mulb0_sq5 & mulb0_cq4;
  assign mulb0_add3b0_maj3b_wy0 = mulb0_sq1 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_maj3b_wy2 = mulb0_sq3 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_maj3b_wy3 = mulb0_sq4 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_maj3b_xy0 = mulb0_cq0 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_maj3b_xy2 = mulb0_cq2 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_maj3b_xy3 = mulb0_cq3 & pipe2_pipeb_xp1;
  assign mulb0_add3b0_xor3b_wx0 = mulb0_sq1 ^ mulb0_cq0;
  assign mulb0_add3b0_xor3b_wx1 = mulb0_sq2 ^ mulb0_cq1;
  assign mulb0_add3b0_xor3b_wx2 = mulb0_sq3 ^ mulb0_cq2;
  assign mulb0_add3b0_xor3b_wx3 = mulb0_sq4 ^ mulb0_cq3;
  assign mulb0_add3b0_xor3b_wx4 = mulb0_sq5 ^ mulb0_cq4;
  assign mulb0_add3b1_maj3b_xy0 = mulb0_ps0 & mulb0_pc0;
  assign mulb0_add3b1_maj3b_xy1 = mulb0_add3b0_xor3b_wx1 & mulb0_pc1;
  assign mulb0_add3b1_maj3b_xy2 = mulb0_ps2 & mulb0_add3b0_maj3b_wx1;
  assign mulb0_add3b1_maj3b_xy3 = mulb0_ps3 & mulb0_pc3;
  assign mulb0_add3b1_maj3b_xy4 = mulb0_add3b0_xor3b_wx4 & mulb0_pc4;
  assign mulb0_cq0 = sticky_xn & sd1;
  assign mulb0_cq1 = sticky_xn & sd2;
  assign mulb0_cq2 = sticky_xn & sd3;
  assign mulb0_cq3 = sticky_xn & sd4;
  assign mulb0_cq4 = sticky_xn & sd5;
  assign mulb0_cq5 = sticky_xn & sd6;
  assign mulb0_cr5 = mulb0_add3_maj3_or3_wx | mulb0_add3_maj3_xy;
  assign mulb0_pc0 = mulb0_sq0 & pipe2_pipeb_xp1;
  assign mulb0_pc1 = mulb0_add3b0_maj3b_or3b_wx0 | mulb0_add3b0_maj3b_xy0;
  assign mulb0_pc3 = mulb0_add3b0_maj3b_or3b_wx2 | mulb0_add3b0_maj3b_xy2;
  assign mulb0_pc4 = mulb0_add3b0_maj3b_or3b_wx3 | mulb0_add3b0_maj3b_xy3;
  assign mulb0_ps0 = mulb0_add3b0_xor3b_wx0 ^ pipe2_pipeb_xp1;
  assign mulb0_ps2 = mulb0_add3b0_xor3b_wx2 ^ pipe2_pipeb_xp1;
  assign mulb0_ps3 = mulb0_add3b0_xor3b_wx3 ^ pipe2_pipeb_xp1;
  assign mulb0_sq0 = sticky_xn & sc0;
  assign mulb0_sq1 = sticky_xn & sc1;
  assign mulb0_sq2 = sticky_xn & sc2;
  assign mulb0_sq3 = sticky_xn & sc3;
  assign mulb0_sq4 = sticky_xn & sc4;
  assign mulb0_sq5 = sticky_xn & sc5;
  assign mulb0_sr0 = mulb0_ps0 ^ mulb0_pc0;
  assign mulb0_sr1 = mulb0_add3b0_xor3b_wx1 ^ mulb0_pc1;
  assign mulb0_sr2 = mulb0_ps2 ^ mulb0_add3b0_maj3b_wx1;
  assign mulb0_sr3 = mulb0_ps3 ^ mulb0_pc3;
  assign mulb0_sr4 = mulb0_add3b0_xor3b_wx4 ^ mulb0_pc4;
  assign mulb0_sr5 = mulb0_add3_xor3_wx ^ mulb0_add3b0_maj3b_wx4;
  assign mulb0_xn = ~pipe2_pipeb_xp1;
  assign mulb1_add3_maj3_xy = mulb1_cq7 & mulb1_add3b1_maj3b_wx6;
  assign mulb1_add3b0_maj3b_xy0 = mulb1_add3b1_xor3b_wx0 & mulb1_pc0;
  assign mulb1_add3b0_maj3b_xy1 = mulb1_ps1 & mulb1_add3b1_maj3b_wx0;
  assign mulb1_add3b0_maj3b_xy2 = mulb1_ps2 & mulb1_pc2;
  assign mulb1_add3b0_maj3b_xy3 = mulb1_add3b1_xor3b_wx3 & mulb1_pc3;
  assign mulb1_add3b0_maj3b_xy4 = mulb1_ps4 & mulb1_add3b1_maj3b_wx3;
  assign mulb1_add3b0_maj3b_xy5 = mulb1_add3b1_xor3b_wx5 & mulb1_pc5;
  assign mulb1_add3b0_maj3b_xy6 = mulb1_add3b1_xor3b_wx6 & mulb1_add3b1_maj3b_wx5;
  assign mulb1_add3b1_maj3b_or3b_wx1 = mulb1_add3b1_maj3b_wx1 | mulb1_add3b1_maj3b_wy1;
  assign mulb1_add3b1_maj3b_or3b_wx2 = mulb1_add3b1_maj3b_wx2 | mulb1_add3b1_maj3b_wy2;
  assign mulb1_add3b1_maj3b_or3b_wx4 = mulb1_add3b1_maj3b_wx4 | mulb1_add3b1_maj3b_wy4;
  assign mulb1_add3b1_maj3b_wx0 = mulb1_sq1 & mulb1_cq0;
  assign mulb1_add3b1_maj3b_wx1 = mulb1_sq2 & mulb1_cq1;
  assign mulb1_add3b1_maj3b_wx2 = mulb1_sq3 & mulb1_cq2;
  assign mulb1_add3b1_maj3b_wx3 = mulb1_sq4 & mulb1_cq3;
  assign mulb1_add3b1_maj3b_wx4 = mulb1_sq5 & mulb1_cq4;
  assign mulb1_add3b1_maj3b_wx5 = mulb1_sq6 & mulb1_cq5;
  assign mulb1_add3b1_maj3b_wx6 = mulb1_sq7 & mulb1_cq6;
  assign mulb1_add3b1_maj3b_wy1 = mulb1_sq2 & pipeb_xp1;
  assign mulb1_add3b1_maj3b_wy2 = mulb1_sq3 & pipeb_xp1;
  assign mulb1_add3b1_maj3b_wy4 = mulb1_sq5 & pipeb_xp1;
  assign mulb1_add3b1_maj3b_xy1 = mulb1_cq1 & pipeb_xp1;
  assign mulb1_add3b1_maj3b_xy2 = mulb1_cq2 & pipeb_xp1;
  assign mulb1_add3b1_maj3b_xy4 = mulb1_cq4 & pipeb_xp1;
  assign mulb1_add3b1_xor3b_wx0 = mulb1_sq1 ^ mulb1_cq0;
  assign mulb1_add3b1_xor3b_wx1 = mulb1_sq2 ^ mulb1_cq1;
  assign mulb1_add3b1_xor3b_wx2 = mulb1_sq3 ^ mulb1_cq2;
  assign mulb1_add3b1_xor3b_wx3 = mulb1_sq4 ^ mulb1_cq3;
  assign mulb1_add3b1_xor3b_wx4 = mulb1_sq5 ^ mulb1_cq4;
  assign mulb1_add3b1_xor3b_wx5 = mulb1_sq6 ^ mulb1_cq5;
  assign mulb1_add3b1_xor3b_wx6 = mulb1_sq7 ^ mulb1_cq6;
  assign mulb1_cq0 = mulb1_xn0 & mulb1_cp0;
  assign mulb1_cq1 = mulb1_xn0 & mulb1_cp1;
  assign mulb1_cq2 = mulb1_xn0 & mulb1_cp2;
  assign mulb1_cq3 = mulb1_xn0 & mulb1_cp3;
  assign mulb1_cq4 = mulb1_xn0 & mulb1_cp4;
  assign mulb1_cq5 = mulb1_xn0 & mulb1_cp5;
  assign mulb1_cq6 = mulb1_xn0 & mulb1_cp6;
  assign mulb1_cq7 = mulb1_xn0 & mulb1_cp7;
  assign mulb1_pc0 = mulb1_sq0 & pipeb_xp1;
  assign mulb1_pc2 = mulb1_add3b1_maj3b_or3b_wx1 | mulb1_add3b1_maj3b_xy1;
  assign mulb1_pc3 = mulb1_add3b1_maj3b_or3b_wx2 | mulb1_add3b1_maj3b_xy2;
  assign mulb1_pc5 = mulb1_add3b1_maj3b_or3b_wx4 | mulb1_add3b1_maj3b_xy4;
  assign mulb1_ps1 = mulb1_add3b1_xor3b_wx1 ^ pipeb_xp1;
  assign mulb1_ps2 = mulb1_add3b1_xor3b_wx2 ^ pipeb_xp1;
  assign mulb1_ps4 = mulb1_add3b1_xor3b_wx4 ^ pipeb_xp1;
  assign mulb1_sq0 = mulb1_xn0 & mulb1_sp0;
  assign mulb1_sq1 = mulb1_xn0 & mulb1_sp1;
  assign mulb1_sq2 = mulb1_xn0 & mulb1_sp2;
  assign mulb1_sq3 = mulb1_xn0 & mulb1_sp3;
  assign mulb1_sq4 = mulb1_xn0 & mulb1_sp4;
  assign mulb1_sq5 = mulb1_xn0 & mulb1_sp5;
  assign mulb1_sq6 = mulb1_xn0 & mulb1_sp6;
  assign mulb1_sq7 = mulb1_xn0 & mulb1_sp7;
  assign mulb1_sr0 = mulb1_add3b1_xor3b_wx0 ^ mulb1_pc0;
  assign mulb1_sr1 = mulb1_ps1 ^ mulb1_add3b1_maj3b_wx0;
  assign mulb1_sr2 = mulb1_ps2 ^ mulb1_pc2;
  assign mulb1_sr3 = mulb1_add3b1_xor3b_wx3 ^ mulb1_pc3;
  assign mulb1_sr4 = mulb1_ps4 ^ mulb1_add3b1_maj3b_wx3;
  assign mulb1_sr5 = mulb1_add3b1_xor3b_wx5 ^ mulb1_pc5;
  assign mulb1_sr6 = mulb1_add3b1_xor3b_wx6 ^ mulb1_add3b1_maj3b_wx5;
  assign mulb1_sr7 = mulb1_cq7 ^ mulb1_add3b1_maj3b_wx6;
  assign mulb1_xn0 = ~pipe1_x0;
  assign mulb1_xn1 = ~pipeb_xp1;
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
  assign mulsc_mulb_cq0 = mulsc_mulb_xn & sb0;
  assign mulsc_mulb_cq1 = mulsc_mulb_xn & sb1;
  assign mulsc_mulb_cq2 = mulsc_mulb_xn & sb2;
  assign mulsc_mulb_cq3 = mulsc_mulb_xn & sb3;
  assign mulsc_mulb_cq4 = mulsc_mulb_xn & mulsc_mulb_cp4;
  assign mulsc_mulb_cq5 = mulsc_mulb_xn & mulsc_mulb_cp5;
  assign mulsc_mulb_cq6 = mulsc_mulb_xn & mulsc_mulb_cp6;
  assign mulsc_mulb_cr0 = mulsc_mulb_add3b1_maj3b_or3b_wx0 | mulsc_mulb_add3b1_maj3b_xy0;
  assign mulsc_mulb_cr1 = mulsc_mulb_add3b1_maj3b_or3b_wx1 | mulsc_mulb_add3b1_maj3b_xy1;
  assign mulsc_mulb_cr2 = mulsc_mulb_add3b1_maj3b_or3b_wx2 | mulsc_mulb_add3b1_maj3b_xy2;
  assign mulsc_mulb_cr3 = mulsc_mulb_add3b1_maj3b_or3b_wx3 | mulsc_mulb_add3b1_maj3b_xy3;
  assign mulsc_mulb_cr4 = mulsc_mulb_add3b1_maj3b_or3b_wx4 | mulsc_mulb_add3b1_maj3b_xy4;
  assign mulsc_mulb_cr5 = mulsc_mulb_add3b1_maj3b_or3b_wx5 | mulsc_mulb_add3b1_maj3b_xy5;
  assign mulsc_mulb_cr6 = mulsc_mulb_add3_maj3_or3_wx | mulsc_mulb_add3_maj3_xy;
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
  assign mulsc_mulb_sq0 = mulsc_mulb_xn & sa4;
  assign mulsc_mulb_sq1 = mulsc_mulb_xn & sa5;
  assign mulsc_mulb_sq2 = mulsc_mulb_xn & sa6;
  assign mulsc_mulb_sq3 = mulsc_mulb_xn & sa7;
  assign mulsc_mulb_sq4 = mulsc_mulb_xn & sa8;
  assign mulsc_mulb_sq5 = mulsc_mulb_xn & mulsc_mulb_sp5;
  assign mulsc_mulb_sq6 = mulsc_mulb_xn & mulsc_mulb_sp6;
  assign mulsc_mulb_sr0 = mulsc_mulb_add3b1_xor3b_wx0 ^ mulsc_mulb_pc0;
  assign mulsc_mulb_sr1 = mulsc_mulb_add3b1_xor3b_wx1 ^ mulsc_mulb_pc1;
  assign mulsc_mulb_sr2 = mulsc_mulb_add3b1_xor3b_wx2 ^ mulsc_mulb_pc2;
  assign mulsc_mulb_sr3 = mulsc_mulb_add3b1_xor3b_wx3 ^ mulsc_mulb_pc3;
  assign mulsc_mulb_sr4 = mulsc_mulb_add3b1_xor3b_wx4 ^ mulsc_mulb_pc4;
  assign mulsc_mulb_sr5 = mulsc_mulb_add3b1_xor3b_wx5 ^ mulsc_mulb_pc5;
  assign mulsc_mulb_sr6 = mulsc_mulb_add3_xor3_wx ^ mulsc_mulb_pc6;
  assign mulsc_mulb_xn = ~pipe0_pipeb_xp1;
  assign mulsc_mulb_yoc0 = mulsc_pipe_pipeb_xp1 & yc[0];
  assign mulsc_mulb_yoc1 = mulsc_pipe_pipeb_xp1 & yc[1];
  assign mulsc_mulb_yoc2 = mulsc_pipe_pipeb_xp1 & yc[2];
  assign mulsc_mulb_yoc3 = mulsc_pipe_pipeb_xp1 & yc[3];
  assign mulsc_mulb_yoc4 = mulsc_pipe_pipeb_xp1 & yc[4];
  assign mulsc_mulb_yoc5 = mulsc_pipe_pipeb_xp1 & yc[5];
  assign mulsc_mulb_yoc6 = mulsc_pipe_pipeb_xp1 & yc[6];
  assign mulsc_mulb_yos0 = mulsc_pipe_pipeb_xp1 & ys[0];
  assign mulsc_mulb_yos1 = mulsc_pipe_pipeb_xp1 & ys[1];
  assign mulsc_mulb_yos2 = mulsc_pipe_pipeb_xp1 & ys[2];
  assign mulsc_mulb_yos3 = mulsc_pipe_pipeb_xp1 & ys[3];
  assign mulsc_mulb_yos4 = mulsc_pipe_pipeb_xp1 & ys[4];
  assign mulsc_mulb_yos5 = mulsc_pipe_pipeb_xp1 & ys[5];
  assign mulsc_mulb_yos6 = mulsc_pipe_pipeb_xp1 & ys[6];
  assign mulsc_pipe_x0 = ld ? xs[0] : mulsc_shrsc_sq0;
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
  assign mulsc_shrsc_sr5 = ld ? xs[6] : mulsc_shrsc_sq6;
  assign mw = add3_maj3_or3_wx | add3_maj3_xy;
  assign or3_wx = sb3 | sa8;
  assign pbp0 = mulsc_mulb_sq0 ^ mulsc_mulb_yos0;
  assign pipe2_x0 = mulb1_sq0 ^ pipeb_xp1;
  assign sticky_q = sticky_xn & sd0;
  assign sticky_r = vb | sticky_q;
  assign sticky_xn = ~pipe1_pipeb_xp1;
  assign vb = mulb0_sq0 ^ pipe2_pipeb_xp1;
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
      mulb1_cp0 <= mulb1_add3b0_maj3b_xy0;
      mulb1_cp1 <= mulb1_add3b0_maj3b_xy1;
      mulb1_cp2 <= mulb1_add3b0_maj3b_xy2;
      mulb1_cp3 <= mulb1_add3b0_maj3b_xy3;
      mulb1_cp4 <= mulb1_add3b0_maj3b_xy4;
      mulb1_cp5 <= mulb1_add3b0_maj3b_xy5;
      mulb1_cp6 <= mulb1_add3b0_maj3b_xy6;
      mulb1_cp7 <= mulb1_add3_maj3_xy;
      mulb1_sp0 <= mulb1_sr0;
      mulb1_sp1 <= mulb1_sr1;
      mulb1_sp2 <= mulb1_sr2;
      mulb1_sp3 <= mulb1_sr3;
      mulb1_sp4 <= mulb1_sr4;
      mulb1_sp5 <= mulb1_sr5;
      mulb1_sp6 <= mulb1_sr6;
      mulb1_sp7 <= mulb1_sr7;
      mulsc_mulb_cp4 <= mulsc_mulb_cr4;
      mulsc_mulb_cp5 <= mulsc_mulb_cr5;
      mulsc_mulb_cp6 <= mulsc_mulb_cr6;
      mulsc_mulb_sp5 <= mulsc_mulb_sr5;
      mulsc_mulb_sp6 <= mulsc_mulb_sr6;
      mulsc_pipe_pipeb_xp0 <= mulsc_pipe_x0;
      mulsc_pipe_pipeb_xp1 <= mulsc_pipe_pipeb_xp0;
      mulsc_shrsc_cp0 <= mulsc_shrsc_cr0;
      mulsc_shrsc_cp1 <= mulsc_shrsc_cr1;
      mulsc_shrsc_cp2 <= mulsc_shrsc_cr2;
      mulsc_shrsc_cp3 <= mulsc_shrsc_cr3;
      mulsc_shrsc_cp4 <= mulsc_shrsc_cr4;
      mulsc_shrsc_cp5 <= mulsc_shrsc_cr5;
      mulsc_shrsc_sp0 <= mulsc_shrsc_sr0;
      mulsc_shrsc_sp1 <= mulsc_shrsc_sr1;
      mulsc_shrsc_sp2 <= mulsc_shrsc_sr2;
      mulsc_shrsc_sp3 <= mulsc_shrsc_sr3;
      mulsc_shrsc_sp4 <= mulsc_shrsc_sr4;
      mulsc_shrsc_sp5 <= mulsc_shrsc_sr5;
      mulsc_shrsc_sq6 <= mulsc_shrsc_cr6;
      pipe0_pipeb_xp0 <= ld;
      pipe0_pipeb_xp1 <= pipe0_pipeb_xp0;
      pipe0_pipeb_xp2 <= pipe0_pipeb_xp1;
      pipe1_pipeb_xp0 <= pipe1_x0;
      pipe1_pipeb_xp1 <= pipe1_pipeb_xp0;
      pipe1_x0 <= pipe0_pipeb_xp2;
      pipe2_pipeb_xp0 <= pipe2_x0;
      pipe2_pipeb_xp1 <= pipe2_pipeb_xp0;
      pipeb_xp0 <= pbp0;
      pipeb_xp1 <= pipeb_xp0;
      pipeb_xp2 <= pipeb_xp1;
      pipeb_xp3 <= pipeb_xp2;
      sa4 <= mulsc_mulb_sr0;
      sa5 <= mulsc_mulb_sr1;
      sa6 <= mulsc_mulb_sr2;
      sa7 <= mulsc_mulb_sr3;
      sa8 <= mulsc_mulb_sr4;
      sb0 <= mulsc_mulb_cr0;
      sb1 <= mulsc_mulb_cr1;
      sb2 <= mulsc_mulb_cr2;
      sb3 <= mulsc_mulb_cr3;
      sc0 <= mulb0_sr0;
      sc1 <= mulb0_sr1;
      sc2 <= mulb0_sr2;
      sc3 <= mulb0_sr3;
      sc4 <= mulb0_sr4;
      sc5 <= mulb0_sr5;
      sd0 <= sticky_r;
      sd1 <= mulb0_add3b1_maj3b_xy0;
      sd2 <= mulb0_add3b1_maj3b_xy1;
      sd3 <= mulb0_add3b1_maj3b_xy2;
      sd4 <= mulb0_add3b1_maj3b_xy3;
      sd5 <= mulb0_add3b1_maj3b_xy4;
      sd6 <= mulb0_cr5;
    end

endmodule // montgomery_reduce_91

/*----------------------------------------------------------------------------+
| Primary inputs: 29                                                          |
| Primary outputs: 16                                                         |
| Delays: 70                                                                  |
| Gates: 340                                                                  |
| Fan-in: 25%=3 50%=5 75%=6 90%=9 95%=9 99%=9 max=9 (sb1)                     |
| Fan-in cone: 25%=2 50%=7 75%=12 90%=17 95%=17 99%=20 max=20 (sb1)           |
| Fan-out: 25%=2 50%=4 75%=5 90%=8 95%=13 99%=16 max=18 (pipe1_x0)            |
| Fan-out load: 25%=2 50%=3 75%=4 90%=6 95%=7 99%=8 max=8 (sd5)               |
| Duplication: 25%=1 50%=1 75%=1 90%=2 95%=3 99%=4 max=4 (pipe0_pipeb_xp1)    |
+----------------------------------------------------------------------------*/


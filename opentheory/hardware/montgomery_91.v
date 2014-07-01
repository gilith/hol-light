/*----------------------------------------------------------------------------+
| module montgomery_91 satisfies the following property:                      |
|                                                                             |
| !x y t.                                                                     |
|     (!i. i <= 17 ==> (signal ld (t + i) <=> i = 0)) /\                      |
|     bits_to_num (bsignal xs[0:6] t) + 2 * bits_to_num (bsignal xc[0:6] t) = |
|     x /\                                                                    |
|     (!i. 2 <= i /\ i <= 10                                                  |
|          ==> bits_to_num (bsignal ys[0:6] (t + i)) +                        |
|              2 * bits_to_num (bsignal yc[0:6] (t + i)) =                    |
|              y)                                                             |
|     ==> (bits_to_num (bsignal zs[0:6] (t + 18)) +                           |
|          2 * bits_to_num (bsignal zc[0:6] (t + 18))) MOD                    |
|         91 =                                                                |
|         ((x * y) * 8) MOD 91                                                |
|                                                                             |
| Copyright (c) 2014 Joe Leslie-Hurd, distributed under the MIT license       |
+----------------------------------------------------------------------------*/

module montgomery_91(clk,ld,xs,xc,ys,yc,zs,zc);
  input clk;
  input ld;
  input [6:0] xs;
  input [6:0] xc;
  input [6:0] ys;
  input [6:0] yc;

  output [6:0] zs;
  output [6:0] zc;

  reg compress_ncd;  // 1:0|12/3=4
  reg compress_nsd;  // 1:0|14/3=4
  reg compress_pipe0_x1;  // 2:1|1/1=3
  reg compress_pipe1_x1;  // 3:2|1/1=3
  reg ctrp_ctr_cp0;  // 2:3|3/1=3
  reg ctrp_ctr_cp1;  // 3:3|2/1=2
  reg ctrp_ctr_cp2;  // 3:3|2/1=2
  reg ctrp_ctr_cp3;  // 3:3|2/1=2
  reg ctrp_ctr_dp;  // 3:3|2/1=2
  reg ctrp_ctr_sp0;  // 3:2|2/1=2
  reg ctrp_ctr_sp1;  // 3:2|2/1=2
  reg ctrp_ctr_sp2;  // 3:3|2/1=2
  reg jpd;  // 1:0|16/4=4
  reg pipe_x1;  // 3:5|1/1=4
  reg qcp0;  // 5:6|3/1=3
  reg qcp1;  // 5:6|3/1=3
  reg qcp2;  // 5:6|3/1=3
  reg qcp3;  // 5:6|3/1=3
  reg qcp4;  // 2:2|3/1=3
  reg qcp5;  // 9:13|3/1=3
  reg qcp6;  // 8:12|3/1=3
  reg qcp7;  // 8:9|2/1=2
  reg qsp0;  // 5:3|3/1=3
  reg qsp1;  // 5:3|3/1=3
  reg qsp2;  // 5:3|3/1=3
  reg qsp3;  // 5:3|3/1=3
  reg qsp4;  // 5:3|3/1=3
  reg qsp5;  // 9:10|3/1=3
  reg qsp6;  // 8:9|3/1=3
  reg qsp7;  // 6:4|3/1=3
  reg reduce_ld1;  // 1:0|18/4=4
  reg reduce_ld2;  // 1:0|13/3=4
  reg reduce_mulb0_cp0;  // 5:7|4/1=4
  reg reduce_mulb0_cp1;  // 6:9|4/1=4
  reg reduce_mulb0_cp2;  // 6:13|4/1=4
  reg reduce_mulb0_cp3;  // 6:12|4/1=4
  reg reduce_mulb0_cp4;  // 6:9|4/1=4
  reg reduce_mulb0_cp5;  // 6:12|4/1=4
  reg reduce_mulb0_cp6;  // 5:8|4/1=4
  reg reduce_mulb0_cp7;  // 4:6|2/1=2
  reg reduce_mulb0_sp0;  // 5:7|3/1=3
  reg reduce_mulb0_sp1;  // 6:9|4/1=4
  reg reduce_mulb0_sp2;  // 6:13|4/1=4
  reg reduce_mulb0_sp3;  // 6:12|4/1=4
  reg reduce_mulb0_sp4;  // 6:9|4/1=4
  reg reduce_mulb0_sp5;  // 6:12|4/1=4
  reg reduce_mulb0_sp6;  // 5:8|4/1=4
  reg reduce_mulb0_sp7;  // 4:6|4/1=4
  reg reduce_mulsc_mulb_cp4;  // 9:20|4/1=4
  reg reduce_mulsc_mulb_cp5;  // 9:20|4/1=4
  reg reduce_mulsc_mulb_cp6;  // 7:16|2/1=2
  reg reduce_mulsc_mulb_sp5;  // 9:17|4/1=4
  reg reduce_mulsc_mulb_sp6;  // 7:13|4/1=4
  reg reduce_mulsc_pipe_x1;  // 4:2|1/1=3
  reg reduce_mulsc_shrsc_cp0;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp1;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp2;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp3;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp4;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp5;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_cp6;  // 2:1|1/1=1
  reg reduce_mulsc_shrsc_sp0;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_sp1;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_sp2;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_sp3;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_sp4;  // 4:2|2/1=2
  reg reduce_mulsc_shrsc_sp5;  // 3:1|2/1=2
  reg reduce_mulsc_xbd;  // 1:0|15/3=5
  reg reduce_pipe0_x1;  // 1:0|1/1=4
  reg reduce_pipe0_x2;  // 1:0|16/4=4
  reg reduce_pipe0_x3;  // 1:0|1/1=4
  reg reduce_pipe1_x1;  // 1:0|1/1=3
  reg reduce_pipe2_x1;  // 3:3|1/1=3
  reg reduce_qb2;  // 1:0|13/3=4
  reg reduce_sa0;  // 1:0|2/1=2
  reg reduce_sa1;  // 1:0|3/1=3
  reg reduce_sa2;  // 1:0|16/3=5
  reg reduce_sa3;  // 4:4|3/1=5
  reg reduce_sa4;  // 8:12|6/1=6
  reg reduce_sa5;  // 9:17|8/1=8
  reg reduce_sa6;  // 9:17|8/1=8
  reg reduce_sa7;  // 9:17|6/1=6
  reg reduce_sa8;  // 9:17|5/1=5
  reg reduce_sb0;  // 8:15|6/1=6
  reg reduce_sb1;  // 9:20|6/1=6
  reg reduce_sb2;  // 9:20|6/1=6
  reg reduce_sb3;  // 9:20|5/1=5
  reg reduce_sc0;  // 5:8|5/1=5
  reg reduce_sc1;  // 6:12|6/1=6
  reg reduce_sc2;  // 6:9|6/1=6
  reg reduce_sc3;  // 6:13|6/1=6
  reg reduce_sc4;  // 6:12|7/1=7
  reg reduce_sc5;  // 5:7|8/1=8
  reg reduce_sd0;  // 4:5|3/1=3
  reg reduce_sd1;  // 5:8|6/1=6
  reg reduce_sd2;  // 6:12|6/1=6
  reg reduce_sd3;  // 6:9|6/1=6
  reg reduce_sd4;  // 6:13|7/1=7
  reg reduce_sd5;  // 6:12|8/1=8
  reg reduce_sd6;  // 5:10|6/1=6

  wire compress_add3b_maj3b_or3b_wx0;
  wire compress_add3b_maj3b_or3b_wx1;
  wire compress_add3b_maj3b_or3b_wx2;
  wire compress_add3b_maj3b_or3b_wx3;
  wire compress_add3b_maj3b_or3b_wx4;
  wire compress_add3b_maj3b_or3b_wx5;
  wire compress_add3b_maj3b_wx0;
  wire compress_add3b_maj3b_wx1;
  wire compress_add3b_maj3b_wx2;
  wire compress_add3b_maj3b_wx3;
  wire compress_add3b_maj3b_wx4;
  wire compress_add3b_maj3b_wx5;
  wire compress_add3b_maj3b_wy0;
  wire compress_add3b_maj3b_wy1;
  wire compress_add3b_maj3b_wy2;
  wire compress_add3b_maj3b_wy3;
  wire compress_add3b_maj3b_wy4;
  wire compress_add3b_maj3b_wy5;
  wire compress_add3b_maj3b_xy0;
  wire compress_add3b_maj3b_xy1;
  wire compress_add3b_maj3b_xy2;
  wire compress_add3b_maj3b_xy3;
  wire compress_add3b_maj3b_xy4;
  wire compress_add3b_maj3b_xy5;
  wire compress_add3b_xor3b_wx0;
  wire compress_add3b_xor3b_wx1;
  wire compress_add3b_xor3b_wx2;
  wire compress_add3b_xor3b_wx3;
  wire compress_add3b_xor3b_wx4;
  wire compress_add3b_xor3b_wx5;
  wire compress_nc;
  wire compress_nct;
  wire compress_ns;
  wire compress_rn0;
  wire compress_rn1;
  wire compress_rn4;
  wire compress_rnh1;
  wire ctrp_ctr_cq0;
  wire ctrp_ctr_cq1;
  wire ctrp_ctr_cq2;
  wire ctrp_ctr_cq3;
  wire ctrp_ctr_cr0;
  wire ctrp_ctr_cr1;
  wire ctrp_ctr_cr2;
  wire ctrp_ctr_cr3;
  wire ctrp_ctr_dq;
  wire ctrp_ctr_sq0;
  wire ctrp_ctr_sq1;
  wire ctrp_ctr_sq2;
  wire ctrp_ctr_sr0;
  wire ctrp_ctr_sr1;
  wire ctrp_ctr_sr2;
  wire ctrp_ds;
  wire ctrp_pulse_xn;
  wire jp;
  wire pc0;
  wire pc1;
  wire pc2;
  wire pc3;
  wire pc5;
  wire pc6;
  wire pc7;
  wire ps0;
  wire ps1;
  wire ps2;
  wire ps3;
  wire ps4;
  wire ps5;
  wire ps6;
  wire ps7;
  wire qcr0;
  wire qcr1;
  wire qcr2;
  wire qcr3;
  wire qcr4;
  wire qcr5;
  wire qcr6;
  wire qcr7;
  wire qsr0;
  wire qsr1;
  wire qsr2;
  wire qsr3;
  wire qsr4;
  wire qsr5;
  wire qsr6;
  wire qsr7;
  wire reduce_add3_maj3_or3_wx;
  wire reduce_add3_maj3_wx;
  wire reduce_add3_maj3_wy;
  wire reduce_add3_maj3_xy;
  wire reduce_add3_xor3_wx;
  wire reduce_add3b0_maj3b_or3b_wx0;
  wire reduce_add3b0_maj3b_or3b_wx1;
  wire reduce_add3b0_maj3b_or3b_wx2;
  wire reduce_add3b0_maj3b_or3b_wx3;
  wire reduce_add3b0_maj3b_or3b_wx4;
  wire reduce_add3b0_maj3b_or3b_wx5;
  wire reduce_add3b0_maj3b_wx0;
  wire reduce_add3b0_maj3b_wx1;
  wire reduce_add3b0_maj3b_wx2;
  wire reduce_add3b0_maj3b_wx3;
  wire reduce_add3b0_maj3b_wx4;
  wire reduce_add3b0_maj3b_wx5;
  wire reduce_add3b0_maj3b_wy0;
  wire reduce_add3b0_maj3b_wy1;
  wire reduce_add3b0_maj3b_wy2;
  wire reduce_add3b0_maj3b_wy3;
  wire reduce_add3b0_maj3b_wy4;
  wire reduce_add3b0_maj3b_wy5;
  wire reduce_add3b0_maj3b_xy0;
  wire reduce_add3b0_maj3b_xy1;
  wire reduce_add3b0_maj3b_xy2;
  wire reduce_add3b0_maj3b_xy3;
  wire reduce_add3b0_maj3b_xy4;
  wire reduce_add3b0_maj3b_xy5;
  wire reduce_add3b0_xor3b_wx0;
  wire reduce_add3b0_xor3b_wx1;
  wire reduce_add3b0_xor3b_wx2;
  wire reduce_add3b0_xor3b_wx3;
  wire reduce_add3b0_xor3b_wx4;
  wire reduce_add3b0_xor3b_wx5;
  wire reduce_add3b1_maj3b_or3b_wx0;
  wire reduce_add3b1_maj3b_or3b_wx1;
  wire reduce_add3b1_maj3b_wx0;
  wire reduce_add3b1_maj3b_wx1;
  wire reduce_add3b1_maj3b_wy0;
  wire reduce_add3b1_maj3b_wy1;
  wire reduce_add3b1_maj3b_xy0;
  wire reduce_add3b1_maj3b_xy1;
  wire reduce_add3b1_xor3b_wx0;
  wire reduce_add3b1_xor3b_wx1;
  wire reduce_mc4;
  wire reduce_mc5;
  wire reduce_mc6;
  wire reduce_ms5;
  wire reduce_ms6;
  wire reduce_mulb0_add3b_maj3b_or3b_wx1;
  wire reduce_mulb0_add3b_maj3b_or3b_wx2;
  wire reduce_mulb0_add3b_maj3b_or3b_wx4;
  wire reduce_mulb0_add3b_maj3b_wx1;
  wire reduce_mulb0_add3b_maj3b_wx2;
  wire reduce_mulb0_add3b_maj3b_wx4;
  wire reduce_mulb0_add3b_maj3b_wy1;
  wire reduce_mulb0_add3b_maj3b_wy2;
  wire reduce_mulb0_add3b_maj3b_wy4;
  wire reduce_mulb0_add3b_maj3b_xy1;
  wire reduce_mulb0_add3b_maj3b_xy2;
  wire reduce_mulb0_add3b_maj3b_xy4;
  wire reduce_mulb0_add3b_xor3b_wx1;
  wire reduce_mulb0_add3b_xor3b_wx2;
  wire reduce_mulb0_add3b_xor3b_wx4;
  wire reduce_mulb0_cq0;
  wire reduce_mulb0_cq1;
  wire reduce_mulb0_cq2;
  wire reduce_mulb0_cq3;
  wire reduce_mulb0_cq4;
  wire reduce_mulb0_cq5;
  wire reduce_mulb0_cq6;
  wire reduce_mulb0_cq7;
  wire reduce_mulb0_pc0;
  wire reduce_mulb0_pc1;
  wire reduce_mulb0_pc2;
  wire reduce_mulb0_pc3;
  wire reduce_mulb0_pc4;
  wire reduce_mulb0_pc5;
  wire reduce_mulb0_pc6;
  wire reduce_mulb0_pc7;
  wire reduce_mulb0_ps0;
  wire reduce_mulb0_ps1;
  wire reduce_mulb0_ps2;
  wire reduce_mulb0_ps3;
  wire reduce_mulb0_ps4;
  wire reduce_mulb0_ps5;
  wire reduce_mulb0_ps6;
  wire reduce_mulb0_sq0;
  wire reduce_mulb0_sq1;
  wire reduce_mulb0_sq2;
  wire reduce_mulb0_sq3;
  wire reduce_mulb0_sq4;
  wire reduce_mulb0_sq5;
  wire reduce_mulb0_sq6;
  wire reduce_mulb0_sq7;
  wire reduce_mulb1_add3_maj3_or3_wx;
  wire reduce_mulb1_add3_maj3_wx;
  wire reduce_mulb1_add3_maj3_wy;
  wire reduce_mulb1_add3_maj3_xy;
  wire reduce_mulb1_add3_xor3_wx;
  wire reduce_mulb1_add3b_maj3b_or3b_wx0;
  wire reduce_mulb1_add3b_maj3b_or3b_wx2;
  wire reduce_mulb1_add3b_maj3b_or3b_wx3;
  wire reduce_mulb1_add3b_maj3b_wx0;
  wire reduce_mulb1_add3b_maj3b_wx2;
  wire reduce_mulb1_add3b_maj3b_wx3;
  wire reduce_mulb1_add3b_maj3b_wy0;
  wire reduce_mulb1_add3b_maj3b_wy2;
  wire reduce_mulb1_add3b_maj3b_wy3;
  wire reduce_mulb1_add3b_maj3b_xy0;
  wire reduce_mulb1_add3b_maj3b_xy2;
  wire reduce_mulb1_add3b_maj3b_xy3;
  wire reduce_mulb1_add3b_xor3b_wx0;
  wire reduce_mulb1_add3b_xor3b_wx2;
  wire reduce_mulb1_add3b_xor3b_wx3;
  wire reduce_mulb1_cq0;
  wire reduce_mulb1_cq1;
  wire reduce_mulb1_cq2;
  wire reduce_mulb1_cq3;
  wire reduce_mulb1_cq4;
  wire reduce_mulb1_cq5;
  wire reduce_mulb1_pc0;
  wire reduce_mulb1_pc1;
  wire reduce_mulb1_pc2;
  wire reduce_mulb1_pc3;
  wire reduce_mulb1_pc4;
  wire reduce_mulb1_pc5;
  wire reduce_mulb1_ps0;
  wire reduce_mulb1_ps1;
  wire reduce_mulb1_ps2;
  wire reduce_mulb1_ps3;
  wire reduce_mulb1_ps4;
  wire reduce_mulb1_sq0;
  wire reduce_mulb1_sq1;
  wire reduce_mulb1_sq2;
  wire reduce_mulb1_sq3;
  wire reduce_mulb1_sq4;
  wire reduce_mulb1_sq5;
  wire reduce_mulsc_mulb_add3_maj3_or3_wx;
  wire reduce_mulsc_mulb_add3_maj3_wx;
  wire reduce_mulsc_mulb_add3_maj3_wy;
  wire reduce_mulsc_mulb_add3_maj3_xy;
  wire reduce_mulsc_mulb_add3_xor3_wx;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4;
  wire reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx0;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx1;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx2;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx3;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx4;
  wire reduce_mulsc_mulb_add3b0_maj3b_wx5;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy0;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy1;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy2;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy3;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy4;
  wire reduce_mulsc_mulb_add3b0_maj3b_wy5;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy0;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy1;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy2;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy3;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy4;
  wire reduce_mulsc_mulb_add3b0_maj3b_xy5;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx0;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx1;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx2;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx3;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx4;
  wire reduce_mulsc_mulb_add3b0_xor3b_wx5;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4;
  wire reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx0;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx1;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx2;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx3;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx4;
  wire reduce_mulsc_mulb_add3b1_maj3b_wx5;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy0;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy1;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy2;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy3;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy4;
  wire reduce_mulsc_mulb_add3b1_maj3b_wy5;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy0;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy1;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy2;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy3;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy4;
  wire reduce_mulsc_mulb_add3b1_maj3b_xy5;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx0;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx1;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx2;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx3;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx4;
  wire reduce_mulsc_mulb_add3b1_xor3b_wx5;
  wire reduce_mulsc_mulb_cq0;
  wire reduce_mulsc_mulb_cq1;
  wire reduce_mulsc_mulb_cq2;
  wire reduce_mulsc_mulb_cq3;
  wire reduce_mulsc_mulb_cq4;
  wire reduce_mulsc_mulb_cq5;
  wire reduce_mulsc_mulb_cq6;
  wire reduce_mulsc_mulb_pc0;
  wire reduce_mulsc_mulb_pc1;
  wire reduce_mulsc_mulb_pc2;
  wire reduce_mulsc_mulb_pc3;
  wire reduce_mulsc_mulb_pc4;
  wire reduce_mulsc_mulb_pc5;
  wire reduce_mulsc_mulb_pc6;
  wire reduce_mulsc_mulb_ps0;
  wire reduce_mulsc_mulb_ps1;
  wire reduce_mulsc_mulb_ps2;
  wire reduce_mulsc_mulb_ps3;
  wire reduce_mulsc_mulb_ps4;
  wire reduce_mulsc_mulb_ps5;
  wire reduce_mulsc_mulb_sq0;
  wire reduce_mulsc_mulb_sq1;
  wire reduce_mulsc_mulb_sq2;
  wire reduce_mulsc_mulb_sq3;
  wire reduce_mulsc_mulb_sq4;
  wire reduce_mulsc_mulb_sq5;
  wire reduce_mulsc_mulb_sq6;
  wire reduce_mulsc_mulb_yoc0;
  wire reduce_mulsc_mulb_yoc1;
  wire reduce_mulsc_mulb_yoc2;
  wire reduce_mulsc_mulb_yoc3;
  wire reduce_mulsc_mulb_yoc4;
  wire reduce_mulsc_mulb_yoc5;
  wire reduce_mulsc_mulb_yoc6;
  wire reduce_mulsc_mulb_yos0;
  wire reduce_mulsc_mulb_yos1;
  wire reduce_mulsc_mulb_yos2;
  wire reduce_mulsc_mulb_yos3;
  wire reduce_mulsc_mulb_yos4;
  wire reduce_mulsc_mulb_yos5;
  wire reduce_mulsc_mulb_yos6;
  wire reduce_mulsc_shrsc_cq0;
  wire reduce_mulsc_shrsc_cq1;
  wire reduce_mulsc_shrsc_cq2;
  wire reduce_mulsc_shrsc_cq3;
  wire reduce_mulsc_shrsc_cq4;
  wire reduce_mulsc_shrsc_cq5;
  wire reduce_mulsc_shrsc_cr0;
  wire reduce_mulsc_shrsc_cr1;
  wire reduce_mulsc_shrsc_cr2;
  wire reduce_mulsc_shrsc_cr3;
  wire reduce_mulsc_shrsc_cr4;
  wire reduce_mulsc_shrsc_cr5;
  wire reduce_mulsc_shrsc_cr6;
  wire reduce_mulsc_shrsc_sq0;
  wire reduce_mulsc_shrsc_sq1;
  wire reduce_mulsc_shrsc_sq2;
  wire reduce_mulsc_shrsc_sq3;
  wire reduce_mulsc_shrsc_sq4;
  wire reduce_mulsc_shrsc_sq5;
  wire reduce_mulsc_shrsc_sr0;
  wire reduce_mulsc_shrsc_sr1;
  wire reduce_mulsc_shrsc_sr2;
  wire reduce_mulsc_shrsc_sr3;
  wire reduce_mulsc_shrsc_sr4;
  wire reduce_mulsc_shrsc_sr5;
  wire reduce_mulsc_xb;
  wire reduce_mw;
  wire reduce_or3_wx;
  wire reduce_pb;
  wire reduce_pc0;
  wire reduce_pc1;
  wire reduce_pc2;
  wire reduce_pc3;
  wire reduce_pc4;
  wire reduce_pc5;
  wire reduce_pc6;
  wire reduce_ps0;
  wire reduce_ps1;
  wire reduce_ps2;
  wire reduce_ps3;
  wire reduce_ps4;
  wire reduce_ps5;
  wire reduce_ps6;
  wire reduce_qb;
  wire reduce_qc0;
  wire reduce_qc1;
  wire reduce_qc2;
  wire reduce_qc3;
  wire reduce_qc4;
  wire reduce_qc5;
  wire reduce_qc6;
  wire reduce_qc7;
  wire reduce_qs0;
  wire reduce_qs1;
  wire reduce_qs2;
  wire reduce_qs3;
  wire reduce_qs4;
  wire reduce_qs5;
  wire reduce_qs6;
  wire reduce_qs7;
  wire reduce_sticky_q;
  wire reduce_vb;
  wire reduce_vc0;
  wire reduce_vc1;
  wire reduce_vc2;
  wire reduce_vc3;
  wire reduce_vc4;
  wire reduce_vc5;
  wire reduce_vs0;
  wire reduce_vs1;
  wire reduce_vs2;
  wire reduce_vs3;
  wire reduce_vs4;
  wire reduce_vs5;
  wire reduce_vt;
  wire xn0;
  wire xn1;
  wire xn2;
  wire xn3;
  wire xn4;
  wire xn5;
  wire zc0_o;
  wire zc1_o;
  wire zc2_o;
  wire zc3_o;
  wire zc4_o;
  wire zc5_o;
  wire zc6_o;
  wire zs0_o;
  wire zs1_o;
  wire zs2_o;
  wire zs3_o;
  wire zs4_o;
  wire zs5_o;
  wire zs6_o;

  assign compress_add3b_maj3b_or3b_wx0 = compress_add3b_maj3b_wx0 | compress_add3b_maj3b_wy0;
  assign compress_add3b_maj3b_or3b_wx1 = compress_add3b_maj3b_wx1 | compress_add3b_maj3b_wy1;
  assign compress_add3b_maj3b_or3b_wx2 = compress_add3b_maj3b_wx2 | compress_add3b_maj3b_wy2;
  assign compress_add3b_maj3b_or3b_wx3 = compress_add3b_maj3b_wx3 | compress_add3b_maj3b_wy3;
  assign compress_add3b_maj3b_or3b_wx4 = compress_add3b_maj3b_wx4 | compress_add3b_maj3b_wy4;
  assign compress_add3b_maj3b_or3b_wx5 = compress_add3b_maj3b_wx5 | compress_add3b_maj3b_wy5;
  assign compress_add3b_maj3b_wx0 = qsp1 & qcp0;
  assign compress_add3b_maj3b_wx1 = qsp2 & qcp1;
  assign compress_add3b_maj3b_wx2 = qsp3 & qcp2;
  assign compress_add3b_maj3b_wx3 = qsp4 & qcp3;
  assign compress_add3b_maj3b_wx4 = qsp5 & qcp4;
  assign compress_add3b_maj3b_wx5 = qsp6 & qcp5;
  assign compress_add3b_maj3b_wy0 = qsp1 & compress_rn1;
  assign compress_add3b_maj3b_wy1 = qsp2 & compress_nsd;
  assign compress_add3b_maj3b_wy2 = qsp3 & compress_rn1;
  assign compress_add3b_maj3b_wy3 = qsp4 & compress_rn4;
  assign compress_add3b_maj3b_wy4 = qsp5 & compress_rn0;
  assign compress_add3b_maj3b_wy5 = qsp6 & compress_rn1;
  assign compress_add3b_maj3b_xy0 = qcp0 & compress_rn1;
  assign compress_add3b_maj3b_xy1 = qcp1 & compress_nsd;
  assign compress_add3b_maj3b_xy2 = qcp2 & compress_rn1;
  assign compress_add3b_maj3b_xy3 = qcp3 & compress_rn4;
  assign compress_add3b_maj3b_xy4 = qcp4 & compress_rn0;
  assign compress_add3b_maj3b_xy5 = qcp5 & compress_rn1;
  assign compress_add3b_xor3b_wx0 = qsp1 ^ qcp0;
  assign compress_add3b_xor3b_wx1 = qsp2 ^ qcp1;
  assign compress_add3b_xor3b_wx2 = qsp3 ^ qcp2;
  assign compress_add3b_xor3b_wx3 = qsp4 ^ qcp3;
  assign compress_add3b_xor3b_wx4 = qsp5 ^ qcp4;
  assign compress_add3b_xor3b_wx5 = qsp6 ^ qcp5;
  assign compress_nc = compress_nct | qcp7;
  assign compress_nct = qsp7 & qcp6;
  assign compress_ns = qsp7 ^ qcp6;
  assign compress_rn0 = xn5 & compress_nsd;
  assign compress_rn1 = compress_ncd & compress_rnh1;
  assign compress_rn4 = compress_ncd & compress_nsd;
  assign compress_rnh1 = ~compress_nsd;
  assign ctrp_ctr_cq0 = ~ctrp_ctr_cp0;
  assign ctrp_ctr_cq1 = ctrp_ctr_sp0 & ctrp_ctr_cp0;
  assign ctrp_ctr_cq2 = ctrp_ctr_sp1 & ctrp_ctr_cp1;
  assign ctrp_ctr_cq3 = ctrp_ctr_sp2 & ctrp_ctr_cp2;
  assign ctrp_ctr_cr0 = xn1 & ctrp_ctr_cq0;
  assign ctrp_ctr_cr1 = xn1 & ctrp_ctr_cq1;
  assign ctrp_ctr_cr2 = xn1 & ctrp_ctr_cq2;
  assign ctrp_ctr_cr3 = xn1 & ctrp_ctr_cq3;
  assign ctrp_ctr_dq = ctrp_ctr_dp | ctrp_ctr_cp3;
  assign ctrp_ctr_sq0 = ctrp_ctr_sp0 ^ ctrp_ctr_cp0;
  assign ctrp_ctr_sq1 = ctrp_ctr_sp1 ^ ctrp_ctr_cp1;
  assign ctrp_ctr_sq2 = ctrp_ctr_sp2 ^ ctrp_ctr_cp2;
  assign ctrp_ctr_sr0 = ld | ctrp_ctr_sq0;
  assign ctrp_ctr_sr1 = ld | ctrp_ctr_sq1;
  assign ctrp_ctr_sr2 = xn1 & ctrp_ctr_sq2;
  assign ctrp_ds = xn1 & ctrp_ctr_dq;
  assign ctrp_pulse_xn = ~ctrp_ctr_dp;
  assign jp = ctrp_ds & ctrp_pulse_xn;
  assign pc0 = reduce_add3b0_maj3b_or3b_wx0 | reduce_add3b0_maj3b_xy0;
  assign pc1 = reduce_add3b0_maj3b_or3b_wx1 | reduce_add3b0_maj3b_xy1;
  assign pc2 = reduce_add3b0_maj3b_or3b_wx2 | reduce_add3b0_maj3b_xy2;
  assign pc3 = reduce_add3b0_maj3b_or3b_wx3 | reduce_add3b0_maj3b_xy3;
  assign pc5 = reduce_add3b1_maj3b_or3b_wx0 | reduce_add3b1_maj3b_xy0;
  assign pc6 = reduce_add3b1_maj3b_or3b_wx1 | reduce_add3b1_maj3b_xy1;
  assign pc7 = reduce_or3_wx | reduce_mw;
  assign ps0 = reduce_add3b0_xor3b_wx0 ^ reduce_sd0;
  assign ps1 = reduce_add3b0_xor3b_wx1 ^ reduce_sd1;
  assign ps2 = reduce_add3b0_xor3b_wx2 ^ reduce_sd2;
  assign ps3 = reduce_add3b0_xor3b_wx3 ^ reduce_sd3;
  assign ps4 = reduce_add3b0_xor3b_wx4 ^ reduce_sd4;
  assign ps5 = reduce_add3b1_xor3b_wx0 ^ reduce_mc4;
  assign ps6 = reduce_add3b1_xor3b_wx1 ^ reduce_mc5;
  assign ps7 = reduce_add3_xor3_wx ^ reduce_mc6;
  assign qcr0 = jpd ? pc0 : qcp0;
  assign qcr1 = jpd ? pc1 : qcp1;
  assign qcr2 = jpd ? pc2 : qcp2;
  assign qcr3 = jpd ? pc3 : qcp3;
  assign qcr4 = xn0 & qcp4;
  assign qcr5 = jpd ? pc5 : qcp5;
  assign qcr6 = jpd ? pc6 : qcp6;
  assign qcr7 = jpd ? pc7 : qcp7;
  assign qsr0 = jpd ? ps0 : qsp0;
  assign qsr1 = jpd ? ps1 : qsp1;
  assign qsr2 = jpd ? ps2 : qsp2;
  assign qsr3 = jpd ? ps3 : qsp3;
  assign qsr4 = jpd ? ps4 : qsp4;
  assign qsr5 = jpd ? ps5 : qsp5;
  assign qsr6 = jpd ? ps6 : qsp6;
  assign qsr7 = jpd ? ps7 : qsp7;
  assign reduce_add3_maj3_or3_wx = reduce_add3_maj3_wx | reduce_add3_maj3_wy;
  assign reduce_add3_maj3_wx = reduce_sb2 & reduce_sa7;
  assign reduce_add3_maj3_wy = reduce_sb2 & reduce_mc6;
  assign reduce_add3_maj3_xy = reduce_sa7 & reduce_mc6;
  assign reduce_add3_xor3_wx = reduce_sb2 ^ reduce_sa7;
  assign reduce_add3b0_maj3b_or3b_wx0 = reduce_add3b0_maj3b_wx0 | reduce_add3b0_maj3b_wy0;
  assign reduce_add3b0_maj3b_or3b_wx1 = reduce_add3b0_maj3b_wx1 | reduce_add3b0_maj3b_wy1;
  assign reduce_add3b0_maj3b_or3b_wx2 = reduce_add3b0_maj3b_wx2 | reduce_add3b0_maj3b_wy2;
  assign reduce_add3b0_maj3b_or3b_wx3 = reduce_add3b0_maj3b_wx3 | reduce_add3b0_maj3b_wy3;
  assign reduce_add3b0_maj3b_or3b_wx4 = reduce_add3b0_maj3b_wx4 | reduce_add3b0_maj3b_wy4;
  assign reduce_add3b0_maj3b_or3b_wx5 = reduce_add3b0_maj3b_wx5 | reduce_add3b0_maj3b_wy5;
  assign reduce_add3b0_maj3b_wx0 = reduce_sa0 & reduce_sc0;
  assign reduce_add3b0_maj3b_wx1 = reduce_sa1 & reduce_sc1;
  assign reduce_add3b0_maj3b_wx2 = reduce_sa2 & reduce_sc2;
  assign reduce_add3b0_maj3b_wx3 = reduce_sa3 & reduce_sc3;
  assign reduce_add3b0_maj3b_wx4 = reduce_sa4 & reduce_sc4;
  assign reduce_add3b0_maj3b_wx5 = reduce_sa5 & reduce_sc5;
  assign reduce_add3b0_maj3b_wy0 = reduce_sa0 & reduce_sd0;
  assign reduce_add3b0_maj3b_wy1 = reduce_sa1 & reduce_sd1;
  assign reduce_add3b0_maj3b_wy2 = reduce_sa2 & reduce_sd2;
  assign reduce_add3b0_maj3b_wy3 = reduce_sa3 & reduce_sd3;
  assign reduce_add3b0_maj3b_wy4 = reduce_sa4 & reduce_sd4;
  assign reduce_add3b0_maj3b_wy5 = reduce_sa5 & reduce_sd5;
  assign reduce_add3b0_maj3b_xy0 = reduce_sc0 & reduce_sd0;
  assign reduce_add3b0_maj3b_xy1 = reduce_sc1 & reduce_sd1;
  assign reduce_add3b0_maj3b_xy2 = reduce_sc2 & reduce_sd2;
  assign reduce_add3b0_maj3b_xy3 = reduce_sc3 & reduce_sd3;
  assign reduce_add3b0_maj3b_xy4 = reduce_sc4 & reduce_sd4;
  assign reduce_add3b0_maj3b_xy5 = reduce_sc5 & reduce_sd5;
  assign reduce_add3b0_xor3b_wx0 = reduce_sa0 ^ reduce_sc0;
  assign reduce_add3b0_xor3b_wx1 = reduce_sa1 ^ reduce_sc1;
  assign reduce_add3b0_xor3b_wx2 = reduce_sa2 ^ reduce_sc2;
  assign reduce_add3b0_xor3b_wx3 = reduce_sa3 ^ reduce_sc3;
  assign reduce_add3b0_xor3b_wx4 = reduce_sa4 ^ reduce_sc4;
  assign reduce_add3b0_xor3b_wx5 = reduce_sa5 ^ reduce_sc5;
  assign reduce_add3b1_maj3b_or3b_wx0 = reduce_add3b1_maj3b_wx0 | reduce_add3b1_maj3b_wy0;
  assign reduce_add3b1_maj3b_or3b_wx1 = reduce_add3b1_maj3b_wx1 | reduce_add3b1_maj3b_wy1;
  assign reduce_add3b1_maj3b_wx0 = reduce_sb0 & reduce_ms5;
  assign reduce_add3b1_maj3b_wx1 = reduce_sb1 & reduce_ms6;
  assign reduce_add3b1_maj3b_wy0 = reduce_sb0 & reduce_mc4;
  assign reduce_add3b1_maj3b_wy1 = reduce_sb1 & reduce_mc5;
  assign reduce_add3b1_maj3b_xy0 = reduce_ms5 & reduce_mc4;
  assign reduce_add3b1_maj3b_xy1 = reduce_ms6 & reduce_mc5;
  assign reduce_add3b1_xor3b_wx0 = reduce_sb0 ^ reduce_ms5;
  assign reduce_add3b1_xor3b_wx1 = reduce_sb1 ^ reduce_ms6;
  assign reduce_mc4 = reduce_add3b0_maj3b_or3b_wx4 | reduce_add3b0_maj3b_xy4;
  assign reduce_mc5 = reduce_add3b0_maj3b_or3b_wx5 | reduce_add3b0_maj3b_xy5;
  assign reduce_mc6 = reduce_sa6 & reduce_sd6;
  assign reduce_ms5 = reduce_add3b0_xor3b_wx5 ^ reduce_sd5;
  assign reduce_ms6 = reduce_sa6 ^ reduce_sd6;
  assign reduce_mulb0_add3b_maj3b_or3b_wx1 = reduce_mulb0_add3b_maj3b_wx1 | reduce_mulb0_add3b_maj3b_wy1;
  assign reduce_mulb0_add3b_maj3b_or3b_wx2 = reduce_mulb0_add3b_maj3b_wx2 | reduce_mulb0_add3b_maj3b_wy2;
  assign reduce_mulb0_add3b_maj3b_or3b_wx4 = reduce_mulb0_add3b_maj3b_wx4 | reduce_mulb0_add3b_maj3b_wy4;
  assign reduce_mulb0_add3b_maj3b_wx1 = reduce_mulb0_sq2 & reduce_mulb0_cq1;
  assign reduce_mulb0_add3b_maj3b_wx2 = reduce_mulb0_sq3 & reduce_mulb0_cq2;
  assign reduce_mulb0_add3b_maj3b_wx4 = reduce_mulb0_sq5 & reduce_mulb0_cq4;
  assign reduce_mulb0_add3b_maj3b_wy1 = reduce_mulb0_sq2 & reduce_sa2;
  assign reduce_mulb0_add3b_maj3b_wy2 = reduce_mulb0_sq3 & reduce_sa2;
  assign reduce_mulb0_add3b_maj3b_wy4 = reduce_mulb0_sq5 & reduce_sa2;
  assign reduce_mulb0_add3b_maj3b_xy1 = reduce_mulb0_cq1 & reduce_sa2;
  assign reduce_mulb0_add3b_maj3b_xy2 = reduce_mulb0_cq2 & reduce_sa2;
  assign reduce_mulb0_add3b_maj3b_xy4 = reduce_mulb0_cq4 & reduce_sa2;
  assign reduce_mulb0_add3b_xor3b_wx1 = reduce_mulb0_sq2 ^ reduce_mulb0_cq1;
  assign reduce_mulb0_add3b_xor3b_wx2 = reduce_mulb0_sq3 ^ reduce_mulb0_cq2;
  assign reduce_mulb0_add3b_xor3b_wx4 = reduce_mulb0_sq5 ^ reduce_mulb0_cq4;
  assign reduce_mulb0_cq0 = xn2 & reduce_mulb0_cp0;
  assign reduce_mulb0_cq1 = xn2 & reduce_mulb0_cp1;
  assign reduce_mulb0_cq2 = xn2 & reduce_mulb0_cp2;
  assign reduce_mulb0_cq3 = xn2 & reduce_mulb0_cp3;
  assign reduce_mulb0_cq4 = xn2 & reduce_mulb0_cp4;
  assign reduce_mulb0_cq5 = xn2 & reduce_mulb0_cp5;
  assign reduce_mulb0_cq6 = xn2 & reduce_mulb0_cp6;
  assign reduce_mulb0_cq7 = xn2 & reduce_mulb0_cp7;
  assign reduce_mulb0_pc0 = reduce_mulb0_sq0 & reduce_sa2;
  assign reduce_mulb0_pc1 = reduce_mulb0_sq1 & reduce_mulb0_cq0;
  assign reduce_mulb0_pc2 = reduce_mulb0_add3b_maj3b_or3b_wx1 | reduce_mulb0_add3b_maj3b_xy1;
  assign reduce_mulb0_pc3 = reduce_mulb0_add3b_maj3b_or3b_wx2 | reduce_mulb0_add3b_maj3b_xy2;
  assign reduce_mulb0_pc4 = reduce_mulb0_sq4 & reduce_mulb0_cq3;
  assign reduce_mulb0_pc5 = reduce_mulb0_add3b_maj3b_or3b_wx4 | reduce_mulb0_add3b_maj3b_xy4;
  assign reduce_mulb0_pc6 = reduce_mulb0_sq6 & reduce_mulb0_cq5;
  assign reduce_mulb0_pc7 = reduce_mulb0_sq7 & reduce_mulb0_cq6;
  assign reduce_mulb0_ps0 = reduce_mulb0_sq1 ^ reduce_mulb0_cq0;
  assign reduce_mulb0_ps1 = reduce_mulb0_add3b_xor3b_wx1 ^ reduce_sa2;
  assign reduce_mulb0_ps2 = reduce_mulb0_add3b_xor3b_wx2 ^ reduce_sa2;
  assign reduce_mulb0_ps3 = reduce_mulb0_sq4 ^ reduce_mulb0_cq3;
  assign reduce_mulb0_ps4 = reduce_mulb0_add3b_xor3b_wx4 ^ reduce_sa2;
  assign reduce_mulb0_ps5 = reduce_mulb0_sq6 ^ reduce_mulb0_cq5;
  assign reduce_mulb0_ps6 = reduce_mulb0_sq7 ^ reduce_mulb0_cq6;
  assign reduce_mulb0_sq0 = xn2 & reduce_mulb0_sp0;
  assign reduce_mulb0_sq1 = xn2 & reduce_mulb0_sp1;
  assign reduce_mulb0_sq2 = xn2 & reduce_mulb0_sp2;
  assign reduce_mulb0_sq3 = xn2 & reduce_mulb0_sp3;
  assign reduce_mulb0_sq4 = xn2 & reduce_mulb0_sp4;
  assign reduce_mulb0_sq5 = xn2 & reduce_mulb0_sp5;
  assign reduce_mulb0_sq6 = xn2 & reduce_mulb0_sp6;
  assign reduce_mulb0_sq7 = xn2 & reduce_mulb0_sp7;
  assign reduce_mulb1_add3_maj3_or3_wx = reduce_mulb1_add3_maj3_wx | reduce_mulb1_add3_maj3_wy;
  assign reduce_mulb1_add3_maj3_wx = reduce_qb2 & reduce_mulb1_cq5;
  assign reduce_mulb1_add3_maj3_wy = reduce_qb2 & reduce_mulb1_pc5;
  assign reduce_mulb1_add3_maj3_xy = reduce_mulb1_cq5 & reduce_mulb1_pc5;
  assign reduce_mulb1_add3_xor3_wx = reduce_qb2 ^ reduce_mulb1_cq5;
  assign reduce_mulb1_add3b_maj3b_or3b_wx0 = reduce_mulb1_add3b_maj3b_wx0 | reduce_mulb1_add3b_maj3b_wy0;
  assign reduce_mulb1_add3b_maj3b_or3b_wx2 = reduce_mulb1_add3b_maj3b_wx2 | reduce_mulb1_add3b_maj3b_wy2;
  assign reduce_mulb1_add3b_maj3b_or3b_wx3 = reduce_mulb1_add3b_maj3b_wx3 | reduce_mulb1_add3b_maj3b_wy3;
  assign reduce_mulb1_add3b_maj3b_wx0 = reduce_mulb1_sq1 & reduce_mulb1_cq0;
  assign reduce_mulb1_add3b_maj3b_wx2 = reduce_mulb1_sq3 & reduce_mulb1_cq2;
  assign reduce_mulb1_add3b_maj3b_wx3 = reduce_mulb1_sq4 & reduce_mulb1_cq3;
  assign reduce_mulb1_add3b_maj3b_wy0 = reduce_mulb1_sq1 & reduce_qb2;
  assign reduce_mulb1_add3b_maj3b_wy2 = reduce_mulb1_sq3 & reduce_qb2;
  assign reduce_mulb1_add3b_maj3b_wy3 = reduce_mulb1_sq4 & reduce_qb2;
  assign reduce_mulb1_add3b_maj3b_xy0 = reduce_mulb1_cq0 & reduce_qb2;
  assign reduce_mulb1_add3b_maj3b_xy2 = reduce_mulb1_cq2 & reduce_qb2;
  assign reduce_mulb1_add3b_maj3b_xy3 = reduce_mulb1_cq3 & reduce_qb2;
  assign reduce_mulb1_add3b_xor3b_wx0 = reduce_mulb1_sq1 ^ reduce_mulb1_cq0;
  assign reduce_mulb1_add3b_xor3b_wx2 = reduce_mulb1_sq3 ^ reduce_mulb1_cq2;
  assign reduce_mulb1_add3b_xor3b_wx3 = reduce_mulb1_sq4 ^ reduce_mulb1_cq3;
  assign reduce_mulb1_cq0 = xn3 & reduce_sd1;
  assign reduce_mulb1_cq1 = xn3 & reduce_sd2;
  assign reduce_mulb1_cq2 = xn3 & reduce_sd3;
  assign reduce_mulb1_cq3 = xn3 & reduce_sd4;
  assign reduce_mulb1_cq4 = xn3 & reduce_sd5;
  assign reduce_mulb1_cq5 = xn3 & reduce_sd6;
  assign reduce_mulb1_pc0 = reduce_mulb1_sq0 & reduce_qb2;
  assign reduce_mulb1_pc1 = reduce_mulb1_add3b_maj3b_or3b_wx0 | reduce_mulb1_add3b_maj3b_xy0;
  assign reduce_mulb1_pc2 = reduce_mulb1_sq2 & reduce_mulb1_cq1;
  assign reduce_mulb1_pc3 = reduce_mulb1_add3b_maj3b_or3b_wx2 | reduce_mulb1_add3b_maj3b_xy2;
  assign reduce_mulb1_pc4 = reduce_mulb1_add3b_maj3b_or3b_wx3 | reduce_mulb1_add3b_maj3b_xy3;
  assign reduce_mulb1_pc5 = reduce_mulb1_sq5 & reduce_mulb1_cq4;
  assign reduce_mulb1_ps0 = reduce_mulb1_add3b_xor3b_wx0 ^ reduce_qb2;
  assign reduce_mulb1_ps1 = reduce_mulb1_sq2 ^ reduce_mulb1_cq1;
  assign reduce_mulb1_ps2 = reduce_mulb1_add3b_xor3b_wx2 ^ reduce_qb2;
  assign reduce_mulb1_ps3 = reduce_mulb1_add3b_xor3b_wx3 ^ reduce_qb2;
  assign reduce_mulb1_ps4 = reduce_mulb1_sq5 ^ reduce_mulb1_cq4;
  assign reduce_mulb1_sq0 = xn3 & reduce_sc0;
  assign reduce_mulb1_sq1 = xn3 & reduce_sc1;
  assign reduce_mulb1_sq2 = xn3 & reduce_sc2;
  assign reduce_mulb1_sq3 = xn3 & reduce_sc3;
  assign reduce_mulb1_sq4 = xn3 & reduce_sc4;
  assign reduce_mulb1_sq5 = xn3 & reduce_sc5;
  assign reduce_mulsc_mulb_add3_maj3_or3_wx = reduce_mulsc_mulb_add3_maj3_wx | reduce_mulsc_mulb_add3_maj3_wy;
  assign reduce_mulsc_mulb_add3_maj3_wx = reduce_mulsc_mulb_yoc6 & reduce_mulsc_mulb_cq6;
  assign reduce_mulsc_mulb_add3_maj3_wy = reduce_mulsc_mulb_yoc6 & reduce_mulsc_mulb_pc6;
  assign reduce_mulsc_mulb_add3_maj3_xy = reduce_mulsc_mulb_cq6 & reduce_mulsc_mulb_pc6;
  assign reduce_mulsc_mulb_add3_xor3_wx = reduce_mulsc_mulb_yoc6 ^ reduce_mulsc_mulb_cq6;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0 = reduce_mulsc_mulb_add3b0_maj3b_wx0 | reduce_mulsc_mulb_add3b0_maj3b_wy0;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1 = reduce_mulsc_mulb_add3b0_maj3b_wx1 | reduce_mulsc_mulb_add3b0_maj3b_wy1;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2 = reduce_mulsc_mulb_add3b0_maj3b_wx2 | reduce_mulsc_mulb_add3b0_maj3b_wy2;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3 = reduce_mulsc_mulb_add3b0_maj3b_wx3 | reduce_mulsc_mulb_add3b0_maj3b_wy3;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4 = reduce_mulsc_mulb_add3b0_maj3b_wx4 | reduce_mulsc_mulb_add3b0_maj3b_wy4;
  assign reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5 = reduce_mulsc_mulb_add3b0_maj3b_wx5 | reduce_mulsc_mulb_add3b0_maj3b_wy5;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx0 = reduce_mulsc_mulb_sq1 & reduce_mulsc_mulb_cq0;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx1 = reduce_mulsc_mulb_sq2 & reduce_mulsc_mulb_cq1;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx2 = reduce_mulsc_mulb_sq3 & reduce_mulsc_mulb_cq2;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx3 = reduce_mulsc_mulb_sq4 & reduce_mulsc_mulb_cq3;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx4 = reduce_mulsc_mulb_sq5 & reduce_mulsc_mulb_cq4;
  assign reduce_mulsc_mulb_add3b0_maj3b_wx5 = reduce_mulsc_mulb_sq6 & reduce_mulsc_mulb_cq5;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy0 = reduce_mulsc_mulb_sq1 & reduce_mulsc_mulb_yos1;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy1 = reduce_mulsc_mulb_sq2 & reduce_mulsc_mulb_yos2;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy2 = reduce_mulsc_mulb_sq3 & reduce_mulsc_mulb_yos3;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy3 = reduce_mulsc_mulb_sq4 & reduce_mulsc_mulb_yos4;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy4 = reduce_mulsc_mulb_sq5 & reduce_mulsc_mulb_yos5;
  assign reduce_mulsc_mulb_add3b0_maj3b_wy5 = reduce_mulsc_mulb_sq6 & reduce_mulsc_mulb_yos6;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy0 = reduce_mulsc_mulb_cq0 & reduce_mulsc_mulb_yos1;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy1 = reduce_mulsc_mulb_cq1 & reduce_mulsc_mulb_yos2;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy2 = reduce_mulsc_mulb_cq2 & reduce_mulsc_mulb_yos3;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy3 = reduce_mulsc_mulb_cq3 & reduce_mulsc_mulb_yos4;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy4 = reduce_mulsc_mulb_cq4 & reduce_mulsc_mulb_yos5;
  assign reduce_mulsc_mulb_add3b0_maj3b_xy5 = reduce_mulsc_mulb_cq5 & reduce_mulsc_mulb_yos6;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx0 = reduce_mulsc_mulb_sq1 ^ reduce_mulsc_mulb_cq0;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx1 = reduce_mulsc_mulb_sq2 ^ reduce_mulsc_mulb_cq1;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx2 = reduce_mulsc_mulb_sq3 ^ reduce_mulsc_mulb_cq2;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx3 = reduce_mulsc_mulb_sq4 ^ reduce_mulsc_mulb_cq3;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx4 = reduce_mulsc_mulb_sq5 ^ reduce_mulsc_mulb_cq4;
  assign reduce_mulsc_mulb_add3b0_xor3b_wx5 = reduce_mulsc_mulb_sq6 ^ reduce_mulsc_mulb_cq5;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0 = reduce_mulsc_mulb_add3b1_maj3b_wx0 | reduce_mulsc_mulb_add3b1_maj3b_wy0;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1 = reduce_mulsc_mulb_add3b1_maj3b_wx1 | reduce_mulsc_mulb_add3b1_maj3b_wy1;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2 = reduce_mulsc_mulb_add3b1_maj3b_wx2 | reduce_mulsc_mulb_add3b1_maj3b_wy2;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3 = reduce_mulsc_mulb_add3b1_maj3b_wx3 | reduce_mulsc_mulb_add3b1_maj3b_wy3;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4 = reduce_mulsc_mulb_add3b1_maj3b_wx4 | reduce_mulsc_mulb_add3b1_maj3b_wy4;
  assign reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5 = reduce_mulsc_mulb_add3b1_maj3b_wx5 | reduce_mulsc_mulb_add3b1_maj3b_wy5;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx0 = reduce_mulsc_mulb_yoc0 & reduce_mulsc_mulb_ps0;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx1 = reduce_mulsc_mulb_yoc1 & reduce_mulsc_mulb_ps1;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx2 = reduce_mulsc_mulb_yoc2 & reduce_mulsc_mulb_ps2;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx3 = reduce_mulsc_mulb_yoc3 & reduce_mulsc_mulb_ps3;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx4 = reduce_mulsc_mulb_yoc4 & reduce_mulsc_mulb_ps4;
  assign reduce_mulsc_mulb_add3b1_maj3b_wx5 = reduce_mulsc_mulb_yoc5 & reduce_mulsc_mulb_ps5;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy0 = reduce_mulsc_mulb_yoc0 & reduce_mulsc_mulb_pc0;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy1 = reduce_mulsc_mulb_yoc1 & reduce_mulsc_mulb_pc1;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy2 = reduce_mulsc_mulb_yoc2 & reduce_mulsc_mulb_pc2;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy3 = reduce_mulsc_mulb_yoc3 & reduce_mulsc_mulb_pc3;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy4 = reduce_mulsc_mulb_yoc4 & reduce_mulsc_mulb_pc4;
  assign reduce_mulsc_mulb_add3b1_maj3b_wy5 = reduce_mulsc_mulb_yoc5 & reduce_mulsc_mulb_pc5;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy0 = reduce_mulsc_mulb_ps0 & reduce_mulsc_mulb_pc0;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy1 = reduce_mulsc_mulb_ps1 & reduce_mulsc_mulb_pc1;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy2 = reduce_mulsc_mulb_ps2 & reduce_mulsc_mulb_pc2;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy3 = reduce_mulsc_mulb_ps3 & reduce_mulsc_mulb_pc3;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy4 = reduce_mulsc_mulb_ps4 & reduce_mulsc_mulb_pc4;
  assign reduce_mulsc_mulb_add3b1_maj3b_xy5 = reduce_mulsc_mulb_ps5 & reduce_mulsc_mulb_pc5;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx0 = reduce_mulsc_mulb_yoc0 ^ reduce_mulsc_mulb_ps0;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx1 = reduce_mulsc_mulb_yoc1 ^ reduce_mulsc_mulb_ps1;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx2 = reduce_mulsc_mulb_yoc2 ^ reduce_mulsc_mulb_ps2;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx3 = reduce_mulsc_mulb_yoc3 ^ reduce_mulsc_mulb_ps3;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx4 = reduce_mulsc_mulb_yoc4 ^ reduce_mulsc_mulb_ps4;
  assign reduce_mulsc_mulb_add3b1_xor3b_wx5 = reduce_mulsc_mulb_yoc5 ^ reduce_mulsc_mulb_ps5;
  assign reduce_mulsc_mulb_cq0 = xn4 & reduce_sb0;
  assign reduce_mulsc_mulb_cq1 = xn4 & reduce_sb1;
  assign reduce_mulsc_mulb_cq2 = xn4 & reduce_sb2;
  assign reduce_mulsc_mulb_cq3 = xn4 & reduce_sb3;
  assign reduce_mulsc_mulb_cq4 = xn4 & reduce_mulsc_mulb_cp4;
  assign reduce_mulsc_mulb_cq5 = xn4 & reduce_mulsc_mulb_cp5;
  assign reduce_mulsc_mulb_cq6 = xn4 & reduce_mulsc_mulb_cp6;
  assign reduce_mulsc_mulb_pc0 = reduce_mulsc_mulb_sq0 & reduce_mulsc_mulb_yos0;
  assign reduce_mulsc_mulb_pc1 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0 | reduce_mulsc_mulb_add3b0_maj3b_xy0;
  assign reduce_mulsc_mulb_pc2 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1 | reduce_mulsc_mulb_add3b0_maj3b_xy1;
  assign reduce_mulsc_mulb_pc3 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2 | reduce_mulsc_mulb_add3b0_maj3b_xy2;
  assign reduce_mulsc_mulb_pc4 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3 | reduce_mulsc_mulb_add3b0_maj3b_xy3;
  assign reduce_mulsc_mulb_pc5 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4 | reduce_mulsc_mulb_add3b0_maj3b_xy4;
  assign reduce_mulsc_mulb_pc6 = reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5 | reduce_mulsc_mulb_add3b0_maj3b_xy5;
  assign reduce_mulsc_mulb_ps0 = reduce_mulsc_mulb_add3b0_xor3b_wx0 ^ reduce_mulsc_mulb_yos1;
  assign reduce_mulsc_mulb_ps1 = reduce_mulsc_mulb_add3b0_xor3b_wx1 ^ reduce_mulsc_mulb_yos2;
  assign reduce_mulsc_mulb_ps2 = reduce_mulsc_mulb_add3b0_xor3b_wx2 ^ reduce_mulsc_mulb_yos3;
  assign reduce_mulsc_mulb_ps3 = reduce_mulsc_mulb_add3b0_xor3b_wx3 ^ reduce_mulsc_mulb_yos4;
  assign reduce_mulsc_mulb_ps4 = reduce_mulsc_mulb_add3b0_xor3b_wx4 ^ reduce_mulsc_mulb_yos5;
  assign reduce_mulsc_mulb_ps5 = reduce_mulsc_mulb_add3b0_xor3b_wx5 ^ reduce_mulsc_mulb_yos6;
  assign reduce_mulsc_mulb_sq0 = xn4 & reduce_sa4;
  assign reduce_mulsc_mulb_sq1 = xn4 & reduce_sa5;
  assign reduce_mulsc_mulb_sq2 = xn4 & reduce_sa6;
  assign reduce_mulsc_mulb_sq3 = xn4 & reduce_sa7;
  assign reduce_mulsc_mulb_sq4 = xn4 & reduce_sa8;
  assign reduce_mulsc_mulb_sq5 = xn4 & reduce_mulsc_mulb_sp5;
  assign reduce_mulsc_mulb_sq6 = xn4 & reduce_mulsc_mulb_sp6;
  assign reduce_mulsc_mulb_yoc0 = reduce_mulsc_xbd & yc[0];
  assign reduce_mulsc_mulb_yoc1 = reduce_mulsc_xbd & yc[1];
  assign reduce_mulsc_mulb_yoc2 = reduce_mulsc_xbd & yc[2];
  assign reduce_mulsc_mulb_yoc3 = reduce_mulsc_xbd & yc[3];
  assign reduce_mulsc_mulb_yoc4 = reduce_mulsc_xbd & yc[4];
  assign reduce_mulsc_mulb_yoc5 = reduce_mulsc_xbd & yc[5];
  assign reduce_mulsc_mulb_yoc6 = reduce_mulsc_xbd & yc[6];
  assign reduce_mulsc_mulb_yos0 = reduce_mulsc_xbd & ys[0];
  assign reduce_mulsc_mulb_yos1 = reduce_mulsc_xbd & ys[1];
  assign reduce_mulsc_mulb_yos2 = reduce_mulsc_xbd & ys[2];
  assign reduce_mulsc_mulb_yos3 = reduce_mulsc_xbd & ys[3];
  assign reduce_mulsc_mulb_yos4 = reduce_mulsc_xbd & ys[4];
  assign reduce_mulsc_mulb_yos5 = reduce_mulsc_xbd & ys[5];
  assign reduce_mulsc_mulb_yos6 = reduce_mulsc_xbd & ys[6];
  assign reduce_mulsc_shrsc_cq0 = reduce_mulsc_shrsc_sp0 & reduce_mulsc_shrsc_cp0;
  assign reduce_mulsc_shrsc_cq1 = reduce_mulsc_shrsc_sp1 & reduce_mulsc_shrsc_cp1;
  assign reduce_mulsc_shrsc_cq2 = reduce_mulsc_shrsc_sp2 & reduce_mulsc_shrsc_cp2;
  assign reduce_mulsc_shrsc_cq3 = reduce_mulsc_shrsc_sp3 & reduce_mulsc_shrsc_cp3;
  assign reduce_mulsc_shrsc_cq4 = reduce_mulsc_shrsc_sp4 & reduce_mulsc_shrsc_cp4;
  assign reduce_mulsc_shrsc_cq5 = reduce_mulsc_shrsc_sp5 & reduce_mulsc_shrsc_cp5;
  assign reduce_mulsc_shrsc_cr0 = ld ? xc[0] : reduce_mulsc_shrsc_cq0;
  assign reduce_mulsc_shrsc_cr1 = ld ? xc[1] : reduce_mulsc_shrsc_cq1;
  assign reduce_mulsc_shrsc_cr2 = ld ? xc[2] : reduce_mulsc_shrsc_cq2;
  assign reduce_mulsc_shrsc_cr3 = ld ? xc[3] : reduce_mulsc_shrsc_cq3;
  assign reduce_mulsc_shrsc_cr4 = ld ? xc[4] : reduce_mulsc_shrsc_cq4;
  assign reduce_mulsc_shrsc_cr5 = ld ? xc[5] : reduce_mulsc_shrsc_cq5;
  assign reduce_mulsc_shrsc_cr6 = ld & xc[6];
  assign reduce_mulsc_shrsc_sq0 = reduce_mulsc_shrsc_sp0 ^ reduce_mulsc_shrsc_cp0;
  assign reduce_mulsc_shrsc_sq1 = reduce_mulsc_shrsc_sp1 ^ reduce_mulsc_shrsc_cp1;
  assign reduce_mulsc_shrsc_sq2 = reduce_mulsc_shrsc_sp2 ^ reduce_mulsc_shrsc_cp2;
  assign reduce_mulsc_shrsc_sq3 = reduce_mulsc_shrsc_sp3 ^ reduce_mulsc_shrsc_cp3;
  assign reduce_mulsc_shrsc_sq4 = reduce_mulsc_shrsc_sp4 ^ reduce_mulsc_shrsc_cp4;
  assign reduce_mulsc_shrsc_sq5 = reduce_mulsc_shrsc_sp5 ^ reduce_mulsc_shrsc_cp5;
  assign reduce_mulsc_shrsc_sr0 = ld ? xs[1] : reduce_mulsc_shrsc_sq1;
  assign reduce_mulsc_shrsc_sr1 = ld ? xs[2] : reduce_mulsc_shrsc_sq2;
  assign reduce_mulsc_shrsc_sr2 = ld ? xs[3] : reduce_mulsc_shrsc_sq3;
  assign reduce_mulsc_shrsc_sr3 = ld ? xs[4] : reduce_mulsc_shrsc_sq4;
  assign reduce_mulsc_shrsc_sr4 = ld ? xs[5] : reduce_mulsc_shrsc_sq5;
  assign reduce_mulsc_shrsc_sr5 = ld ? xs[6] : reduce_mulsc_shrsc_cp6;
  assign reduce_mulsc_xb = ld ? xs[0] : reduce_mulsc_shrsc_sq0;
  assign reduce_mw = reduce_add3_maj3_or3_wx | reduce_add3_maj3_xy;
  assign reduce_or3_wx = reduce_sb3 | reduce_sa8;
  assign reduce_pb = reduce_mulsc_mulb_sq0 ^ reduce_mulsc_mulb_yos0;
  assign reduce_pc0 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0 | reduce_mulsc_mulb_add3b1_maj3b_xy0;
  assign reduce_pc1 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1 | reduce_mulsc_mulb_add3b1_maj3b_xy1;
  assign reduce_pc2 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2 | reduce_mulsc_mulb_add3b1_maj3b_xy2;
  assign reduce_pc3 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3 | reduce_mulsc_mulb_add3b1_maj3b_xy3;
  assign reduce_pc4 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4 | reduce_mulsc_mulb_add3b1_maj3b_xy4;
  assign reduce_pc5 = reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5 | reduce_mulsc_mulb_add3b1_maj3b_xy5;
  assign reduce_pc6 = reduce_mulsc_mulb_add3_maj3_or3_wx | reduce_mulsc_mulb_add3_maj3_xy;
  assign reduce_ps0 = reduce_mulsc_mulb_add3b1_xor3b_wx0 ^ reduce_mulsc_mulb_pc0;
  assign reduce_ps1 = reduce_mulsc_mulb_add3b1_xor3b_wx1 ^ reduce_mulsc_mulb_pc1;
  assign reduce_ps2 = reduce_mulsc_mulb_add3b1_xor3b_wx2 ^ reduce_mulsc_mulb_pc2;
  assign reduce_ps3 = reduce_mulsc_mulb_add3b1_xor3b_wx3 ^ reduce_mulsc_mulb_pc3;
  assign reduce_ps4 = reduce_mulsc_mulb_add3b1_xor3b_wx4 ^ reduce_mulsc_mulb_pc4;
  assign reduce_ps5 = reduce_mulsc_mulb_add3b1_xor3b_wx5 ^ reduce_mulsc_mulb_pc5;
  assign reduce_ps6 = reduce_mulsc_mulb_add3_xor3_wx ^ reduce_mulsc_mulb_pc6;
  assign reduce_qb = reduce_mulb0_sq0 ^ reduce_sa2;
  assign reduce_qc0 = reduce_mulb0_ps0 & reduce_mulb0_pc0;
  assign reduce_qc1 = reduce_mulb0_ps1 & reduce_mulb0_pc1;
  assign reduce_qc2 = reduce_mulb0_ps2 & reduce_mulb0_pc2;
  assign reduce_qc3 = reduce_mulb0_ps3 & reduce_mulb0_pc3;
  assign reduce_qc4 = reduce_mulb0_ps4 & reduce_mulb0_pc4;
  assign reduce_qc5 = reduce_mulb0_ps5 & reduce_mulb0_pc5;
  assign reduce_qc6 = reduce_mulb0_ps6 & reduce_mulb0_pc6;
  assign reduce_qc7 = reduce_mulb0_cq7 & reduce_mulb0_pc7;
  assign reduce_qs0 = reduce_mulb0_ps0 ^ reduce_mulb0_pc0;
  assign reduce_qs1 = reduce_mulb0_ps1 ^ reduce_mulb0_pc1;
  assign reduce_qs2 = reduce_mulb0_ps2 ^ reduce_mulb0_pc2;
  assign reduce_qs3 = reduce_mulb0_ps3 ^ reduce_mulb0_pc3;
  assign reduce_qs4 = reduce_mulb0_ps4 ^ reduce_mulb0_pc4;
  assign reduce_qs5 = reduce_mulb0_ps5 ^ reduce_mulb0_pc5;
  assign reduce_qs6 = reduce_mulb0_ps6 ^ reduce_mulb0_pc6;
  assign reduce_qs7 = reduce_mulb0_cq7 ^ reduce_mulb0_pc7;
  assign reduce_sticky_q = xn3 & reduce_sd0;
  assign reduce_vb = reduce_mulb1_sq0 ^ reduce_qb2;
  assign reduce_vc0 = reduce_mulb1_ps0 & reduce_mulb1_pc0;
  assign reduce_vc1 = reduce_mulb1_ps1 & reduce_mulb1_pc1;
  assign reduce_vc2 = reduce_mulb1_ps2 & reduce_mulb1_pc2;
  assign reduce_vc3 = reduce_mulb1_ps3 & reduce_mulb1_pc3;
  assign reduce_vc4 = reduce_mulb1_ps4 & reduce_mulb1_pc4;
  assign reduce_vc5 = reduce_mulb1_add3_maj3_or3_wx | reduce_mulb1_add3_maj3_xy;
  assign reduce_vs0 = reduce_mulb1_ps0 ^ reduce_mulb1_pc0;
  assign reduce_vs1 = reduce_mulb1_ps1 ^ reduce_mulb1_pc1;
  assign reduce_vs2 = reduce_mulb1_ps2 ^ reduce_mulb1_pc2;
  assign reduce_vs3 = reduce_mulb1_ps3 ^ reduce_mulb1_pc3;
  assign reduce_vs4 = reduce_mulb1_ps4 ^ reduce_mulb1_pc4;
  assign reduce_vs5 = reduce_mulb1_add3_xor3_wx ^ reduce_mulb1_pc5;
  assign reduce_vt = reduce_vb | reduce_sticky_q;
  assign xn0 = ~jpd;
  assign xn1 = ~ld;
  assign xn2 = ~reduce_ld1;
  assign xn3 = ~reduce_ld2;
  assign xn4 = ~reduce_pipe0_x2;
  assign xn5 = ~compress_ncd;
  assign zc0_o = qsp0 & compress_rn0;
  assign zc1_o = compress_add3b_maj3b_or3b_wx0 | compress_add3b_maj3b_xy0;
  assign zc2_o = compress_add3b_maj3b_or3b_wx1 | compress_add3b_maj3b_xy1;
  assign zc3_o = compress_add3b_maj3b_or3b_wx2 | compress_add3b_maj3b_xy2;
  assign zc4_o = compress_add3b_maj3b_or3b_wx3 | compress_add3b_maj3b_xy3;
  assign zc5_o = compress_add3b_maj3b_or3b_wx4 | compress_add3b_maj3b_xy4;
  assign zc6_o = compress_add3b_maj3b_or3b_wx5 | compress_add3b_maj3b_xy5;
  assign zs0_o = qsp0 ^ compress_rn0;
  assign zs1_o = compress_add3b_xor3b_wx0 ^ compress_rn1;
  assign zs2_o = compress_add3b_xor3b_wx1 ^ compress_nsd;
  assign zs3_o = compress_add3b_xor3b_wx2 ^ compress_rn1;
  assign zs4_o = compress_add3b_xor3b_wx3 ^ compress_rn4;
  assign zs5_o = compress_add3b_xor3b_wx4 ^ compress_rn0;
  assign zs6_o = compress_add3b_xor3b_wx5 ^ compress_rn1;
  assign zs[0] = zs0_o;
  assign zs[1] = zs1_o;
  assign zs[2] = zs2_o;
  assign zs[3] = zs3_o;
  assign zs[4] = zs4_o;
  assign zs[5] = zs5_o;
  assign zs[6] = zs6_o;
  assign zc[0] = zc0_o;
  assign zc[1] = zc1_o;
  assign zc[2] = zc2_o;
  assign zc[3] = zc3_o;
  assign zc[4] = zc4_o;
  assign zc[5] = zc5_o;
  assign zc[6] = zc6_o;

  always @(posedge clk)
    begin
      compress_ncd <= compress_pipe1_x1;
      compress_nsd <= compress_pipe0_x1;
      compress_pipe0_x1 <= compress_ns;
      compress_pipe1_x1 <= compress_nc;
      ctrp_ctr_cp0 <= ctrp_ctr_cr0;
      ctrp_ctr_cp1 <= ctrp_ctr_cr1;
      ctrp_ctr_cp2 <= ctrp_ctr_cr2;
      ctrp_ctr_cp3 <= ctrp_ctr_cr3;
      ctrp_ctr_dp <= ctrp_ds;
      ctrp_ctr_sp0 <= ctrp_ctr_sr0;
      ctrp_ctr_sp1 <= ctrp_ctr_sr1;
      ctrp_ctr_sp2 <= ctrp_ctr_sr2;
      jpd <= pipe_x1;
      pipe_x1 <= jp;
      qcp0 <= qcr0;
      qcp1 <= qcr1;
      qcp2 <= qcr2;
      qcp3 <= qcr3;
      qcp4 <= qcr4;
      qcp5 <= qcr5;
      qcp6 <= qcr6;
      qcp7 <= qcr7;
      qsp0 <= qsr0;
      qsp1 <= qsr1;
      qsp2 <= qsr2;
      qsp3 <= qsr3;
      qsp4 <= qsr4;
      qsp5 <= qsr5;
      qsp6 <= qsr6;
      qsp7 <= qsr7;
      reduce_ld1 <= reduce_pipe0_x3;
      reduce_ld2 <= reduce_pipe1_x1;
      reduce_mulb0_cp0 <= reduce_qc0;
      reduce_mulb0_cp1 <= reduce_qc1;
      reduce_mulb0_cp2 <= reduce_qc2;
      reduce_mulb0_cp3 <= reduce_qc3;
      reduce_mulb0_cp4 <= reduce_qc4;
      reduce_mulb0_cp5 <= reduce_qc5;
      reduce_mulb0_cp6 <= reduce_qc6;
      reduce_mulb0_cp7 <= reduce_qc7;
      reduce_mulb0_sp0 <= reduce_qs0;
      reduce_mulb0_sp1 <= reduce_qs1;
      reduce_mulb0_sp2 <= reduce_qs2;
      reduce_mulb0_sp3 <= reduce_qs3;
      reduce_mulb0_sp4 <= reduce_qs4;
      reduce_mulb0_sp5 <= reduce_qs5;
      reduce_mulb0_sp6 <= reduce_qs6;
      reduce_mulb0_sp7 <= reduce_qs7;
      reduce_mulsc_mulb_cp4 <= reduce_pc4;
      reduce_mulsc_mulb_cp5 <= reduce_pc5;
      reduce_mulsc_mulb_cp6 <= reduce_pc6;
      reduce_mulsc_mulb_sp5 <= reduce_ps5;
      reduce_mulsc_mulb_sp6 <= reduce_ps6;
      reduce_mulsc_pipe_x1 <= reduce_mulsc_xb;
      reduce_mulsc_shrsc_cp0 <= reduce_mulsc_shrsc_cr0;
      reduce_mulsc_shrsc_cp1 <= reduce_mulsc_shrsc_cr1;
      reduce_mulsc_shrsc_cp2 <= reduce_mulsc_shrsc_cr2;
      reduce_mulsc_shrsc_cp3 <= reduce_mulsc_shrsc_cr3;
      reduce_mulsc_shrsc_cp4 <= reduce_mulsc_shrsc_cr4;
      reduce_mulsc_shrsc_cp5 <= reduce_mulsc_shrsc_cr5;
      reduce_mulsc_shrsc_cp6 <= reduce_mulsc_shrsc_cr6;
      reduce_mulsc_shrsc_sp0 <= reduce_mulsc_shrsc_sr0;
      reduce_mulsc_shrsc_sp1 <= reduce_mulsc_shrsc_sr1;
      reduce_mulsc_shrsc_sp2 <= reduce_mulsc_shrsc_sr2;
      reduce_mulsc_shrsc_sp3 <= reduce_mulsc_shrsc_sr3;
      reduce_mulsc_shrsc_sp4 <= reduce_mulsc_shrsc_sr4;
      reduce_mulsc_shrsc_sp5 <= reduce_mulsc_shrsc_sr5;
      reduce_mulsc_xbd <= reduce_mulsc_pipe_x1;
      reduce_pipe0_x1 <= ld;
      reduce_pipe0_x2 <= reduce_pipe0_x1;
      reduce_pipe0_x3 <= reduce_pipe0_x2;
      reduce_pipe1_x1 <= reduce_ld1;
      reduce_pipe2_x1 <= reduce_qb;
      reduce_qb2 <= reduce_pipe2_x1;
      reduce_sa0 <= reduce_sa1;
      reduce_sa1 <= reduce_sa2;
      reduce_sa2 <= reduce_sa3;
      reduce_sa3 <= reduce_pb;
      reduce_sa4 <= reduce_ps0;
      reduce_sa5 <= reduce_ps1;
      reduce_sa6 <= reduce_ps2;
      reduce_sa7 <= reduce_ps3;
      reduce_sa8 <= reduce_ps4;
      reduce_sb0 <= reduce_pc0;
      reduce_sb1 <= reduce_pc1;
      reduce_sb2 <= reduce_pc2;
      reduce_sb3 <= reduce_pc3;
      reduce_sc0 <= reduce_vs0;
      reduce_sc1 <= reduce_vs1;
      reduce_sc2 <= reduce_vs2;
      reduce_sc3 <= reduce_vs3;
      reduce_sc4 <= reduce_vs4;
      reduce_sc5 <= reduce_vs5;
      reduce_sd0 <= reduce_vt;
      reduce_sd1 <= reduce_vc0;
      reduce_sd2 <= reduce_vc1;
      reduce_sd3 <= reduce_vc2;
      reduce_sd4 <= reduce_vc3;
      reduce_sd5 <= reduce_vc4;
      reduce_sd6 <= reduce_vc5;
    end

endmodule  // montgomery_91

/*----------------------------------------------------------------------------+
| Primary inputs: 29                                                          |
| Primary outputs: 14                                                         |
| Registers: 100                                                              |
| Gates: 426                                                                  |
| Fan-in: 25%=3 50%=4 75%=6 90%=8 95%=9 99%=9 max=9 (reduce_sa7)              |
| Fan-in cone: 25%=2 50%=5 75%=10 90%=13 95%=17 99%=20 max=20 (reduce_sb2)    |
| Fan-out: 25%=2 50%=3 75%=4 90%=8 95%=13 99%=16 max=24 (ld)                  |
| Duplication: 25%=1 50%=1 75%=1 90%=1 95%=3 99%=4 max=4 (reduce_ld1)         |
| Fan-out load: 25%=2 50%=3 75%=4 90%=6 95%=6 99%=8 max=24 (ld)               |
+----------------------------------------------------------------------------*/

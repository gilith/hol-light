/*----------------------------------------------------------------------------+
| module double_exp_91 satisfies the following property:                      |
|                                                                             |
| !x t.                                                                       |
|     ?d. !j. (!i. i <= d + j ==> (signal ld (t + i) <=> i <= 5)) /\          |
|             (bits_to_num (bsignal xs[0:6] (t + 10)) +                       |
|              2 * bits_to_num (bsignal xc[0:6] (t + 10))) MOD                |
|             91 =                                                            |
|             (x * 2 EXP 9) MOD 91                                            |
|             ==> (!i. i <= d + j ==> (signal dn (t + 5 + i) <=> d <= i)) /\  |
|                 (bits_to_num (bsignal ys[0:6] (t + 5 + d + j)) +            |
|                  2 * bits_to_num (bsignal yc[0:6] (t + 5 + d + j))) MOD     |
|                 91 =                                                        |
|                 (x EXP (2 EXP 11) * 2 EXP 9) MOD 91                         |
|                                                                             |
| Copyright (c) 2014 Joe Leslie-Hurd, distributed under the MIT license       |
+----------------------------------------------------------------------------*/

module double_exp_91(clk,ld,xs,xc,dn,ys,yc);
  input clk;
  input ld;
  input [6:0] xs;
  input [6:0] xc;

  output dn;
  output [6:0] ys;
  output [6:0] yc;

  reg ctre_cp0;  // 3:4|2/1=2
  reg ctre_cp1;  // 4:4|2/1=2
  reg ctre_cp2;  // 4:4|2/1=2
  reg ctre_cp3;  // 4:4|2/1=2
  reg ctre_dp;  // 4:4|2/1=2
  reg ctre_sp0;  // 3:4|2/1=2
  reg ctre_sp1;  // 4:3|2/1=2
  reg ctre_sp2;  // 4:3|2/1=2
  reg ctre_sp3;  // 4:4|2/1=2
  reg multm_compress_ncd;  // 1:0|12/3=4
  reg multm_compress_nsd;  // 1:0|14/3=4
  reg multm_compress_pipe0_x1;  // 2:1|1/1=3
  reg multm_compress_pipe1_x1;  // 3:2|1/1=3
  reg multm_ctrp_ctr_cp0;  // 2:3|3/1=3
  reg multm_ctrp_ctr_cp1;  // 3:3|2/1=2
  reg multm_ctrp_ctr_cp2;  // 3:3|2/1=2
  reg multm_ctrp_ctr_cp3;  // 3:3|4/1=4
  reg multm_ctrp_ctr_dp;  // 3:3|4/1=4
  reg multm_ctrp_ctr_sp0;  // 3:2|2/1=2
  reg multm_ctrp_ctr_sp1;  // 3:2|2/1=2
  reg multm_ctrp_ctr_sp2;  // 3:3|2/1=2
  reg multm_jpd;  // 1:0|16/4=4
  reg multm_pipe_x1;  // 3:5|1/1=4
  reg multm_qcp0;  // 5:6|3/1=3
  reg multm_qcp1;  // 5:6|3/1=3
  reg multm_qcp2;  // 5:6|3/1=3
  reg multm_qcp3;  // 5:6|3/1=3
  reg multm_qcp4;  // 2:2|3/1=3
  reg multm_qcp5;  // 9:13|3/1=3
  reg multm_qcp6;  // 8:12|3/1=3
  reg multm_qcp7;  // 8:9|2/1=2
  reg multm_qsp0;  // 5:3|3/1=3
  reg multm_qsp1;  // 5:3|3/1=3
  reg multm_qsp2;  // 5:3|3/1=3
  reg multm_qsp3;  // 5:3|3/1=3
  reg multm_qsp4;  // 5:3|3/1=3
  reg multm_qsp5;  // 9:10|3/1=3
  reg multm_qsp6;  // 8:9|3/1=3
  reg multm_qsp7;  // 6:4|3/1=3
  reg multm_reduce_ld1;  // 1:0|18/4=4
  reg multm_reduce_ld2;  // 1:0|13/3=4
  reg multm_reduce_mulb0_cp0;  // 5:7|4/1=4
  reg multm_reduce_mulb0_cp1;  // 6:9|4/1=4
  reg multm_reduce_mulb0_cp2;  // 6:13|4/1=4
  reg multm_reduce_mulb0_cp3;  // 6:12|4/1=4
  reg multm_reduce_mulb0_cp4;  // 6:9|4/1=4
  reg multm_reduce_mulb0_cp5;  // 6:12|4/1=4
  reg multm_reduce_mulb0_cp6;  // 5:8|4/1=4
  reg multm_reduce_mulb0_cp7;  // 4:6|2/1=2
  reg multm_reduce_mulb0_sp0;  // 5:7|3/1=3
  reg multm_reduce_mulb0_sp1;  // 6:9|4/1=4
  reg multm_reduce_mulb0_sp2;  // 6:13|4/1=4
  reg multm_reduce_mulb0_sp3;  // 6:12|4/1=4
  reg multm_reduce_mulb0_sp4;  // 6:9|4/1=4
  reg multm_reduce_mulb0_sp5;  // 6:12|4/1=4
  reg multm_reduce_mulb0_sp6;  // 5:8|4/1=4
  reg multm_reduce_mulb0_sp7;  // 4:6|4/1=4
  reg multm_reduce_mulsc_mulb_cp4;  // 9:20|4/1=4
  reg multm_reduce_mulsc_mulb_cp5;  // 9:20|4/1=4
  reg multm_reduce_mulsc_mulb_cp6;  // 7:16|2/1=2
  reg multm_reduce_mulsc_mulb_sp5;  // 9:17|4/1=4
  reg multm_reduce_mulsc_mulb_sp6;  // 7:13|4/1=4
  reg multm_reduce_mulsc_pipe_x1;  // 4:2|1/1=3
  reg multm_reduce_mulsc_shrsc_cp0;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp1;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp2;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp3;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp4;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp5;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_cp6;  // 2:1|1/1=1
  reg multm_reduce_mulsc_shrsc_sp0;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_sp1;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_sp2;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_sp3;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_sp4;  // 4:2|2/1=2
  reg multm_reduce_mulsc_shrsc_sp5;  // 3:1|2/1=2
  reg multm_reduce_mulsc_xbd;  // 1:0|15/3=5
  reg multm_reduce_pipe0_x1;  // 1:0|1/1=4
  reg multm_reduce_pipe0_x2;  // 1:0|16/4=4
  reg multm_reduce_pipe0_x3;  // 1:0|1/1=4
  reg multm_reduce_pipe1_x1;  // 1:0|1/1=3
  reg multm_reduce_pipe2_x1;  // 3:3|1/1=3
  reg multm_reduce_qb2;  // 1:0|13/3=4
  reg multm_reduce_sa0;  // 1:0|2/1=2
  reg multm_reduce_sa1;  // 1:0|3/1=3
  reg multm_reduce_sa2;  // 1:0|16/3=5
  reg multm_reduce_sa3;  // 4:4|3/1=5
  reg multm_reduce_sa4;  // 8:12|6/1=6
  reg multm_reduce_sa5;  // 9:17|8/1=8
  reg multm_reduce_sa6;  // 9:17|8/1=8
  reg multm_reduce_sa7;  // 9:17|6/1=6
  reg multm_reduce_sa8;  // 9:17|5/1=5
  reg multm_reduce_sb0;  // 8:15|6/1=6
  reg multm_reduce_sb1;  // 9:20|6/1=6
  reg multm_reduce_sb2;  // 9:20|6/1=6
  reg multm_reduce_sb3;  // 9:20|5/1=5
  reg multm_reduce_sc0;  // 5:8|5/1=5
  reg multm_reduce_sc1;  // 6:12|6/1=6
  reg multm_reduce_sc2;  // 6:9|6/1=6
  reg multm_reduce_sc3;  // 6:13|6/1=6
  reg multm_reduce_sc4;  // 6:12|7/1=7
  reg multm_reduce_sc5;  // 5:7|8/1=8
  reg multm_reduce_sd0;  // 4:5|3/1=3
  reg multm_reduce_sd1;  // 5:8|6/1=6
  reg multm_reduce_sd2;  // 6:12|6/1=6
  reg multm_reduce_sd3;  // 6:9|6/1=6
  reg multm_reduce_sd4;  // 6:13|7/1=7
  reg multm_reduce_sd5;  // 6:12|8/1=8
  reg multm_reduce_sd6;  // 5:10|6/1=6
  reg pipe0_x1;  // 1:0|1/1=1
  reg pipe0_x2;  // 1:0|1/1=2
  reg pipe0_x3;  // 1:0|1/2=3
  reg pipe1_x1;  // 1:0|1/1=1
  reg pipe1_x2;  // 1:0|1/1=2
  reg pipe1_x3;  // 1:0|1/2=2
  reg sa;  // 6:9|3/1=3
  reg sad;  // 1:0|16/6=3
  reg sadd;  // 1:0|35/8=4
  reg sb;  // 9:14|3/1=3
  reg sbd;  // 1:0|16/5=3
  reg sbdd;  // 1:0|10/2=5
  reg yc0_o;  // 7:5|5/1=5
  reg yc1_o;  // 8:9|5/1=5
  reg yc2_o;  // 7:7|5/1=5
  reg yc3_o;  // 8:9|5/1=5
  reg yc4_o;  // 8:8|5/1=5
  reg yc5_o;  // 8:9|5/1=5
  reg yc6_o;  // 8:9|5/1=5
  reg ys0_o;  // 7:5|6/1=6
  reg ys1_o;  // 8:6|7/1=7
  reg ys2_o;  // 7:4|7/1=7
  reg ys3_o;  // 8:6|7/1=7
  reg ys4_o;  // 8:5|7/1=7
  reg ys5_o;  // 8:6|7/1=7
  reg ys6_o;  // 8:6|7/1=7

  wire ctre_cq0;
  wire ctre_cq1;
  wire ctre_cq2;
  wire ctre_cq3;
  wire ctre_cr0;
  wire ctre_cr1;
  wire ctre_cr2;
  wire ctre_cr3;
  wire ctre_dq;
  wire ctre_sq0;
  wire ctre_sq1;
  wire ctre_sq2;
  wire ctre_sq3;
  wire ctre_sr0;
  wire ctre_sr1;
  wire ctre_sr2;
  wire ctre_sr3;
  wire dn_o;
  wire jp;
  wire jpn;
  wire md;
  wire mdn;
  wire multm_compress_add3b_maj3b_or3b_wx0;
  wire multm_compress_add3b_maj3b_or3b_wx1;
  wire multm_compress_add3b_maj3b_or3b_wx2;
  wire multm_compress_add3b_maj3b_or3b_wx3;
  wire multm_compress_add3b_maj3b_or3b_wx4;
  wire multm_compress_add3b_maj3b_or3b_wx5;
  wire multm_compress_add3b_maj3b_wx0;
  wire multm_compress_add3b_maj3b_wx1;
  wire multm_compress_add3b_maj3b_wx2;
  wire multm_compress_add3b_maj3b_wx3;
  wire multm_compress_add3b_maj3b_wx4;
  wire multm_compress_add3b_maj3b_wx5;
  wire multm_compress_add3b_maj3b_wy0;
  wire multm_compress_add3b_maj3b_wy1;
  wire multm_compress_add3b_maj3b_wy2;
  wire multm_compress_add3b_maj3b_wy3;
  wire multm_compress_add3b_maj3b_wy4;
  wire multm_compress_add3b_maj3b_wy5;
  wire multm_compress_add3b_maj3b_xy0;
  wire multm_compress_add3b_maj3b_xy1;
  wire multm_compress_add3b_maj3b_xy2;
  wire multm_compress_add3b_maj3b_xy3;
  wire multm_compress_add3b_maj3b_xy4;
  wire multm_compress_add3b_maj3b_xy5;
  wire multm_compress_add3b_xor3b_wx0;
  wire multm_compress_add3b_xor3b_wx1;
  wire multm_compress_add3b_xor3b_wx2;
  wire multm_compress_add3b_xor3b_wx3;
  wire multm_compress_add3b_xor3b_wx4;
  wire multm_compress_add3b_xor3b_wx5;
  wire multm_compress_nc;
  wire multm_compress_nct;
  wire multm_compress_ns;
  wire multm_compress_rn0;
  wire multm_compress_rn1;
  wire multm_compress_rn4;
  wire multm_compress_rnh3;
  wire multm_ctrp_ctr_cq0;
  wire multm_ctrp_ctr_cq1;
  wire multm_ctrp_ctr_cq2;
  wire multm_ctrp_ctr_cq3;
  wire multm_ctrp_ctr_cr0;
  wire multm_ctrp_ctr_cr1;
  wire multm_ctrp_ctr_cr2;
  wire multm_ctrp_ctr_cr3;
  wire multm_ctrp_ctr_dq;
  wire multm_ctrp_ctr_sq0;
  wire multm_ctrp_ctr_sq1;
  wire multm_ctrp_ctr_sq2;
  wire multm_ctrp_ctr_sr0;
  wire multm_ctrp_ctr_sr1;
  wire multm_ctrp_ctr_sr2;
  wire multm_ctrp_ds;
  wire multm_ctrp_pulse_xn;
  wire multm_pc0;
  wire multm_pc1;
  wire multm_pc2;
  wire multm_pc3;
  wire multm_pc5;
  wire multm_pc6;
  wire multm_pc7;
  wire multm_ps0;
  wire multm_ps1;
  wire multm_ps2;
  wire multm_ps3;
  wire multm_ps4;
  wire multm_ps5;
  wire multm_ps6;
  wire multm_ps7;
  wire multm_qcr0;
  wire multm_qcr1;
  wire multm_qcr2;
  wire multm_qcr3;
  wire multm_qcr4;
  wire multm_qcr5;
  wire multm_qcr6;
  wire multm_qcr7;
  wire multm_qsr0;
  wire multm_qsr1;
  wire multm_qsr2;
  wire multm_qsr3;
  wire multm_qsr4;
  wire multm_qsr5;
  wire multm_qsr6;
  wire multm_qsr7;
  wire multm_reduce_add3_maj3_or3_wx;
  wire multm_reduce_add3_maj3_wx;
  wire multm_reduce_add3_maj3_wy;
  wire multm_reduce_add3_maj3_xy;
  wire multm_reduce_add3_xor3_wx;
  wire multm_reduce_add3b0_maj3b_or3b_wx0;
  wire multm_reduce_add3b0_maj3b_or3b_wx1;
  wire multm_reduce_add3b0_maj3b_or3b_wx2;
  wire multm_reduce_add3b0_maj3b_or3b_wx3;
  wire multm_reduce_add3b0_maj3b_or3b_wx4;
  wire multm_reduce_add3b0_maj3b_or3b_wx5;
  wire multm_reduce_add3b0_maj3b_wx0;
  wire multm_reduce_add3b0_maj3b_wx1;
  wire multm_reduce_add3b0_maj3b_wx2;
  wire multm_reduce_add3b0_maj3b_wx3;
  wire multm_reduce_add3b0_maj3b_wx4;
  wire multm_reduce_add3b0_maj3b_wx5;
  wire multm_reduce_add3b0_maj3b_wy0;
  wire multm_reduce_add3b0_maj3b_wy1;
  wire multm_reduce_add3b0_maj3b_wy2;
  wire multm_reduce_add3b0_maj3b_wy3;
  wire multm_reduce_add3b0_maj3b_wy4;
  wire multm_reduce_add3b0_maj3b_wy5;
  wire multm_reduce_add3b0_maj3b_xy0;
  wire multm_reduce_add3b0_maj3b_xy1;
  wire multm_reduce_add3b0_maj3b_xy2;
  wire multm_reduce_add3b0_maj3b_xy3;
  wire multm_reduce_add3b0_maj3b_xy4;
  wire multm_reduce_add3b0_maj3b_xy5;
  wire multm_reduce_add3b0_xor3b_wx0;
  wire multm_reduce_add3b0_xor3b_wx1;
  wire multm_reduce_add3b0_xor3b_wx2;
  wire multm_reduce_add3b0_xor3b_wx3;
  wire multm_reduce_add3b0_xor3b_wx4;
  wire multm_reduce_add3b0_xor3b_wx5;
  wire multm_reduce_add3b1_maj3b_or3b_wx0;
  wire multm_reduce_add3b1_maj3b_or3b_wx1;
  wire multm_reduce_add3b1_maj3b_wx0;
  wire multm_reduce_add3b1_maj3b_wx1;
  wire multm_reduce_add3b1_maj3b_wy0;
  wire multm_reduce_add3b1_maj3b_wy1;
  wire multm_reduce_add3b1_maj3b_xy0;
  wire multm_reduce_add3b1_maj3b_xy1;
  wire multm_reduce_add3b1_xor3b_wx0;
  wire multm_reduce_add3b1_xor3b_wx1;
  wire multm_reduce_mc4;
  wire multm_reduce_mc5;
  wire multm_reduce_mc6;
  wire multm_reduce_ms5;
  wire multm_reduce_ms6;
  wire multm_reduce_mulb0_add3b_maj3b_or3b_wx1;
  wire multm_reduce_mulb0_add3b_maj3b_or3b_wx2;
  wire multm_reduce_mulb0_add3b_maj3b_or3b_wx4;
  wire multm_reduce_mulb0_add3b_maj3b_wx1;
  wire multm_reduce_mulb0_add3b_maj3b_wx2;
  wire multm_reduce_mulb0_add3b_maj3b_wx4;
  wire multm_reduce_mulb0_add3b_maj3b_wy1;
  wire multm_reduce_mulb0_add3b_maj3b_wy2;
  wire multm_reduce_mulb0_add3b_maj3b_wy4;
  wire multm_reduce_mulb0_add3b_maj3b_xy1;
  wire multm_reduce_mulb0_add3b_maj3b_xy2;
  wire multm_reduce_mulb0_add3b_maj3b_xy4;
  wire multm_reduce_mulb0_add3b_xor3b_wx1;
  wire multm_reduce_mulb0_add3b_xor3b_wx2;
  wire multm_reduce_mulb0_add3b_xor3b_wx4;
  wire multm_reduce_mulb0_cq0;
  wire multm_reduce_mulb0_cq1;
  wire multm_reduce_mulb0_cq2;
  wire multm_reduce_mulb0_cq3;
  wire multm_reduce_mulb0_cq4;
  wire multm_reduce_mulb0_cq5;
  wire multm_reduce_mulb0_cq6;
  wire multm_reduce_mulb0_cq7;
  wire multm_reduce_mulb0_pc0;
  wire multm_reduce_mulb0_pc1;
  wire multm_reduce_mulb0_pc2;
  wire multm_reduce_mulb0_pc3;
  wire multm_reduce_mulb0_pc4;
  wire multm_reduce_mulb0_pc5;
  wire multm_reduce_mulb0_pc6;
  wire multm_reduce_mulb0_pc7;
  wire multm_reduce_mulb0_ps0;
  wire multm_reduce_mulb0_ps1;
  wire multm_reduce_mulb0_ps2;
  wire multm_reduce_mulb0_ps3;
  wire multm_reduce_mulb0_ps4;
  wire multm_reduce_mulb0_ps5;
  wire multm_reduce_mulb0_ps6;
  wire multm_reduce_mulb0_sq0;
  wire multm_reduce_mulb0_sq1;
  wire multm_reduce_mulb0_sq2;
  wire multm_reduce_mulb0_sq3;
  wire multm_reduce_mulb0_sq4;
  wire multm_reduce_mulb0_sq5;
  wire multm_reduce_mulb0_sq6;
  wire multm_reduce_mulb0_sq7;
  wire multm_reduce_mulb1_add3_maj3_or3_wx;
  wire multm_reduce_mulb1_add3_maj3_wx;
  wire multm_reduce_mulb1_add3_maj3_wy;
  wire multm_reduce_mulb1_add3_maj3_xy;
  wire multm_reduce_mulb1_add3_xor3_wx;
  wire multm_reduce_mulb1_add3b_maj3b_or3b_wx0;
  wire multm_reduce_mulb1_add3b_maj3b_or3b_wx2;
  wire multm_reduce_mulb1_add3b_maj3b_or3b_wx3;
  wire multm_reduce_mulb1_add3b_maj3b_wx0;
  wire multm_reduce_mulb1_add3b_maj3b_wx2;
  wire multm_reduce_mulb1_add3b_maj3b_wx3;
  wire multm_reduce_mulb1_add3b_maj3b_wy0;
  wire multm_reduce_mulb1_add3b_maj3b_wy2;
  wire multm_reduce_mulb1_add3b_maj3b_wy3;
  wire multm_reduce_mulb1_add3b_maj3b_xy0;
  wire multm_reduce_mulb1_add3b_maj3b_xy2;
  wire multm_reduce_mulb1_add3b_maj3b_xy3;
  wire multm_reduce_mulb1_add3b_xor3b_wx0;
  wire multm_reduce_mulb1_add3b_xor3b_wx2;
  wire multm_reduce_mulb1_add3b_xor3b_wx3;
  wire multm_reduce_mulb1_cq0;
  wire multm_reduce_mulb1_cq1;
  wire multm_reduce_mulb1_cq2;
  wire multm_reduce_mulb1_cq3;
  wire multm_reduce_mulb1_cq4;
  wire multm_reduce_mulb1_cq5;
  wire multm_reduce_mulb1_pc0;
  wire multm_reduce_mulb1_pc1;
  wire multm_reduce_mulb1_pc2;
  wire multm_reduce_mulb1_pc3;
  wire multm_reduce_mulb1_pc4;
  wire multm_reduce_mulb1_pc5;
  wire multm_reduce_mulb1_ps0;
  wire multm_reduce_mulb1_ps1;
  wire multm_reduce_mulb1_ps2;
  wire multm_reduce_mulb1_ps3;
  wire multm_reduce_mulb1_ps4;
  wire multm_reduce_mulb1_sq0;
  wire multm_reduce_mulb1_sq1;
  wire multm_reduce_mulb1_sq2;
  wire multm_reduce_mulb1_sq3;
  wire multm_reduce_mulb1_sq4;
  wire multm_reduce_mulb1_sq5;
  wire multm_reduce_mulsc_mulb_add3_maj3_or3_wx;
  wire multm_reduce_mulsc_mulb_add3_maj3_wx;
  wire multm_reduce_mulsc_mulb_add3_maj3_wy;
  wire multm_reduce_mulsc_mulb_add3_maj3_xy;
  wire multm_reduce_mulsc_mulb_add3_xor3_wx;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wx5;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy0;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy1;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy2;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy3;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy4;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_wy5;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy0;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy1;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy2;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy3;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy4;
  wire multm_reduce_mulsc_mulb_add3b0_maj3b_xy5;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b0_xor3b_wx5;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wx5;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy0;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy1;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy2;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy3;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy4;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_wy5;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy0;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy1;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy2;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy3;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy4;
  wire multm_reduce_mulsc_mulb_add3b1_maj3b_xy5;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx0;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx1;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx2;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx3;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx4;
  wire multm_reduce_mulsc_mulb_add3b1_xor3b_wx5;
  wire multm_reduce_mulsc_mulb_cq0;
  wire multm_reduce_mulsc_mulb_cq1;
  wire multm_reduce_mulsc_mulb_cq2;
  wire multm_reduce_mulsc_mulb_cq3;
  wire multm_reduce_mulsc_mulb_cq4;
  wire multm_reduce_mulsc_mulb_cq5;
  wire multm_reduce_mulsc_mulb_cq6;
  wire multm_reduce_mulsc_mulb_pc0;
  wire multm_reduce_mulsc_mulb_pc1;
  wire multm_reduce_mulsc_mulb_pc2;
  wire multm_reduce_mulsc_mulb_pc3;
  wire multm_reduce_mulsc_mulb_pc4;
  wire multm_reduce_mulsc_mulb_pc5;
  wire multm_reduce_mulsc_mulb_pc6;
  wire multm_reduce_mulsc_mulb_ps0;
  wire multm_reduce_mulsc_mulb_ps1;
  wire multm_reduce_mulsc_mulb_ps2;
  wire multm_reduce_mulsc_mulb_ps3;
  wire multm_reduce_mulsc_mulb_ps4;
  wire multm_reduce_mulsc_mulb_ps5;
  wire multm_reduce_mulsc_mulb_sq0;
  wire multm_reduce_mulsc_mulb_sq1;
  wire multm_reduce_mulsc_mulb_sq2;
  wire multm_reduce_mulsc_mulb_sq3;
  wire multm_reduce_mulsc_mulb_sq4;
  wire multm_reduce_mulsc_mulb_sq5;
  wire multm_reduce_mulsc_mulb_sq6;
  wire multm_reduce_mulsc_mulb_yoc0;
  wire multm_reduce_mulsc_mulb_yoc1;
  wire multm_reduce_mulsc_mulb_yoc2;
  wire multm_reduce_mulsc_mulb_yoc3;
  wire multm_reduce_mulsc_mulb_yoc4;
  wire multm_reduce_mulsc_mulb_yoc5;
  wire multm_reduce_mulsc_mulb_yoc6;
  wire multm_reduce_mulsc_mulb_yos0;
  wire multm_reduce_mulsc_mulb_yos1;
  wire multm_reduce_mulsc_mulb_yos2;
  wire multm_reduce_mulsc_mulb_yos3;
  wire multm_reduce_mulsc_mulb_yos4;
  wire multm_reduce_mulsc_mulb_yos5;
  wire multm_reduce_mulsc_mulb_yos6;
  wire multm_reduce_mulsc_shrsc_cq0;
  wire multm_reduce_mulsc_shrsc_cq1;
  wire multm_reduce_mulsc_shrsc_cq2;
  wire multm_reduce_mulsc_shrsc_cq3;
  wire multm_reduce_mulsc_shrsc_cq4;
  wire multm_reduce_mulsc_shrsc_cq5;
  wire multm_reduce_mulsc_shrsc_cr0;
  wire multm_reduce_mulsc_shrsc_cr1;
  wire multm_reduce_mulsc_shrsc_cr2;
  wire multm_reduce_mulsc_shrsc_cr3;
  wire multm_reduce_mulsc_shrsc_cr4;
  wire multm_reduce_mulsc_shrsc_cr5;
  wire multm_reduce_mulsc_shrsc_cr6;
  wire multm_reduce_mulsc_shrsc_sq0;
  wire multm_reduce_mulsc_shrsc_sq1;
  wire multm_reduce_mulsc_shrsc_sq2;
  wire multm_reduce_mulsc_shrsc_sq3;
  wire multm_reduce_mulsc_shrsc_sq4;
  wire multm_reduce_mulsc_shrsc_sq5;
  wire multm_reduce_mulsc_shrsc_sr0;
  wire multm_reduce_mulsc_shrsc_sr1;
  wire multm_reduce_mulsc_shrsc_sr2;
  wire multm_reduce_mulsc_shrsc_sr3;
  wire multm_reduce_mulsc_shrsc_sr4;
  wire multm_reduce_mulsc_shrsc_sr5;
  wire multm_reduce_mulsc_xb;
  wire multm_reduce_mw;
  wire multm_reduce_or3_wx;
  wire multm_reduce_pb;
  wire multm_reduce_pc0;
  wire multm_reduce_pc1;
  wire multm_reduce_pc2;
  wire multm_reduce_pc3;
  wire multm_reduce_pc4;
  wire multm_reduce_pc5;
  wire multm_reduce_pc6;
  wire multm_reduce_ps0;
  wire multm_reduce_ps1;
  wire multm_reduce_ps2;
  wire multm_reduce_ps3;
  wire multm_reduce_ps4;
  wire multm_reduce_ps5;
  wire multm_reduce_ps6;
  wire multm_reduce_qb;
  wire multm_reduce_qc0;
  wire multm_reduce_qc1;
  wire multm_reduce_qc2;
  wire multm_reduce_qc3;
  wire multm_reduce_qc4;
  wire multm_reduce_qc5;
  wire multm_reduce_qc6;
  wire multm_reduce_qc7;
  wire multm_reduce_qs0;
  wire multm_reduce_qs1;
  wire multm_reduce_qs2;
  wire multm_reduce_qs3;
  wire multm_reduce_qs4;
  wire multm_reduce_qs5;
  wire multm_reduce_qs6;
  wire multm_reduce_qs7;
  wire multm_reduce_sticky_q;
  wire multm_reduce_vb;
  wire multm_reduce_vc0;
  wire multm_reduce_vc1;
  wire multm_reduce_vc2;
  wire multm_reduce_vc3;
  wire multm_reduce_vc4;
  wire multm_reduce_vc5;
  wire multm_reduce_vs0;
  wire multm_reduce_vs1;
  wire multm_reduce_vs2;
  wire multm_reduce_vs3;
  wire multm_reduce_vs4;
  wire multm_reduce_vs5;
  wire multm_reduce_vt;
  wire nor2_zn;
  wire pcq0;
  wire pcq1;
  wire pcq2;
  wire pcq3;
  wire pcq4;
  wire pcq5;
  wire pcq6;
  wire pcr0;
  wire pcr1;
  wire pcr2;
  wire pcr3;
  wire pcr4;
  wire pcr5;
  wire pcr6;
  wire psq0;
  wire psq1;
  wire psq2;
  wire psq3;
  wire psq4;
  wire psq5;
  wire psq6;
  wire psr0;
  wire psr1;
  wire psr2;
  wire psr3;
  wire psr4;
  wire psr5;
  wire psr6;
  wire qc0;
  wire qc1;
  wire qc2;
  wire qc3;
  wire qc4;
  wire qc5;
  wire qc6;
  wire qs0;
  wire qs1;
  wire qs2;
  wire qs3;
  wire qs4;
  wire qs5;
  wire qs6;
  wire san;
  wire sap;
  wire saq;
  wire sar;
  wire sbp;
  wire sbq;
  wire sbr;
  wire srdd;
  wire xn0;
  wire xn1;
  wire xn2;
  wire xn3;
  wire xn4;
  wire xn5;
  wire xn6;

  assign ctre_cq0 = sadd & ctre_sp0;
  assign ctre_cq1 = ctre_sp1 & ctre_cp0;
  assign ctre_cq2 = ctre_sp2 & ctre_cp1;
  assign ctre_cq3 = ctre_sp3 & ctre_cp2;
  assign ctre_cr0 = xn5 & ctre_cq0;
  assign ctre_cr1 = xn5 & ctre_cq1;
  assign ctre_cr2 = xn5 & ctre_cq2;
  assign ctre_cr3 = xn5 & ctre_cq3;
  assign ctre_dq = ctre_dp | ctre_cp3;
  assign ctre_sq0 = sadd ^ ctre_sp0;
  assign ctre_sq1 = ctre_sp1 ^ ctre_cp0;
  assign ctre_sq2 = ctre_sp2 ^ ctre_cp1;
  assign ctre_sq3 = ctre_sp3 ^ ctre_cp2;
  assign ctre_sr0 = xn5 & ctre_sq0;
  assign ctre_sr1 = srdd | ctre_sq1;
  assign ctre_sr2 = srdd | ctre_sq2;
  assign ctre_sr3 = xn5 & ctre_sq3;
  assign dn_o = ~nor2_zn;
  assign jp = multm_ctrp_ds & multm_ctrp_pulse_xn;
  assign jpn = ~jp;
  assign md = xn5 & ctre_dq;
  assign mdn = ~md;
  assign multm_compress_add3b_maj3b_or3b_wx0 = multm_compress_add3b_maj3b_wx0 | multm_compress_add3b_maj3b_wy0;
  assign multm_compress_add3b_maj3b_or3b_wx1 = multm_compress_add3b_maj3b_wx1 | multm_compress_add3b_maj3b_wy1;
  assign multm_compress_add3b_maj3b_or3b_wx2 = multm_compress_add3b_maj3b_wx2 | multm_compress_add3b_maj3b_wy2;
  assign multm_compress_add3b_maj3b_or3b_wx3 = multm_compress_add3b_maj3b_wx3 | multm_compress_add3b_maj3b_wy3;
  assign multm_compress_add3b_maj3b_or3b_wx4 = multm_compress_add3b_maj3b_wx4 | multm_compress_add3b_maj3b_wy4;
  assign multm_compress_add3b_maj3b_or3b_wx5 = multm_compress_add3b_maj3b_wx5 | multm_compress_add3b_maj3b_wy5;
  assign multm_compress_add3b_maj3b_wx0 = multm_qsp1 & multm_qcp0;
  assign multm_compress_add3b_maj3b_wx1 = multm_qsp2 & multm_qcp1;
  assign multm_compress_add3b_maj3b_wx2 = multm_qsp3 & multm_qcp2;
  assign multm_compress_add3b_maj3b_wx3 = multm_qsp4 & multm_qcp3;
  assign multm_compress_add3b_maj3b_wx4 = multm_qsp5 & multm_qcp4;
  assign multm_compress_add3b_maj3b_wx5 = multm_qsp6 & multm_qcp5;
  assign multm_compress_add3b_maj3b_wy0 = multm_qsp1 & multm_compress_rn1;
  assign multm_compress_add3b_maj3b_wy1 = multm_qsp2 & multm_compress_nsd;
  assign multm_compress_add3b_maj3b_wy2 = multm_qsp3 & multm_compress_rn1;
  assign multm_compress_add3b_maj3b_wy3 = multm_qsp4 & multm_compress_rn4;
  assign multm_compress_add3b_maj3b_wy4 = multm_qsp5 & multm_compress_rn0;
  assign multm_compress_add3b_maj3b_wy5 = multm_qsp6 & multm_compress_rn1;
  assign multm_compress_add3b_maj3b_xy0 = multm_qcp0 & multm_compress_rn1;
  assign multm_compress_add3b_maj3b_xy1 = multm_qcp1 & multm_compress_nsd;
  assign multm_compress_add3b_maj3b_xy2 = multm_qcp2 & multm_compress_rn1;
  assign multm_compress_add3b_maj3b_xy3 = multm_qcp3 & multm_compress_rn4;
  assign multm_compress_add3b_maj3b_xy4 = multm_qcp4 & multm_compress_rn0;
  assign multm_compress_add3b_maj3b_xy5 = multm_qcp5 & multm_compress_rn1;
  assign multm_compress_add3b_xor3b_wx0 = multm_qsp1 ^ multm_qcp0;
  assign multm_compress_add3b_xor3b_wx1 = multm_qsp2 ^ multm_qcp1;
  assign multm_compress_add3b_xor3b_wx2 = multm_qsp3 ^ multm_qcp2;
  assign multm_compress_add3b_xor3b_wx3 = multm_qsp4 ^ multm_qcp3;
  assign multm_compress_add3b_xor3b_wx4 = multm_qsp5 ^ multm_qcp4;
  assign multm_compress_add3b_xor3b_wx5 = multm_qsp6 ^ multm_qcp5;
  assign multm_compress_nc = multm_compress_nct | multm_qcp7;
  assign multm_compress_nct = multm_qsp7 & multm_qcp6;
  assign multm_compress_ns = multm_qsp7 ^ multm_qcp6;
  assign multm_compress_rn0 = xn6 & multm_compress_nsd;
  assign multm_compress_rn1 = multm_compress_ncd & multm_compress_rnh3;
  assign multm_compress_rn4 = multm_compress_ncd & multm_compress_nsd;
  assign multm_compress_rnh3 = ~multm_compress_nsd;
  assign multm_ctrp_ctr_cq0 = ~multm_ctrp_ctr_cp0;
  assign multm_ctrp_ctr_cq1 = multm_ctrp_ctr_sp0 & multm_ctrp_ctr_cp0;
  assign multm_ctrp_ctr_cq2 = multm_ctrp_ctr_sp1 & multm_ctrp_ctr_cp1;
  assign multm_ctrp_ctr_cq3 = multm_ctrp_ctr_sp2 & multm_ctrp_ctr_cp2;
  assign multm_ctrp_ctr_cr0 = xn4 & multm_ctrp_ctr_cq0;
  assign multm_ctrp_ctr_cr1 = xn4 & multm_ctrp_ctr_cq1;
  assign multm_ctrp_ctr_cr2 = xn4 & multm_ctrp_ctr_cq2;
  assign multm_ctrp_ctr_cr3 = xn4 & multm_ctrp_ctr_cq3;
  assign multm_ctrp_ctr_dq = multm_ctrp_ctr_dp | multm_ctrp_ctr_cp3;
  assign multm_ctrp_ctr_sq0 = multm_ctrp_ctr_sp0 ^ multm_ctrp_ctr_cp0;
  assign multm_ctrp_ctr_sq1 = multm_ctrp_ctr_sp1 ^ multm_ctrp_ctr_cp1;
  assign multm_ctrp_ctr_sq2 = multm_ctrp_ctr_sp2 ^ multm_ctrp_ctr_cp2;
  assign multm_ctrp_ctr_sr0 = sadd | multm_ctrp_ctr_sq0;
  assign multm_ctrp_ctr_sr1 = sadd | multm_ctrp_ctr_sq1;
  assign multm_ctrp_ctr_sr2 = xn4 & multm_ctrp_ctr_sq2;
  assign multm_ctrp_ds = xn4 & multm_ctrp_ctr_dq;
  assign multm_ctrp_pulse_xn = ~multm_ctrp_ctr_dp;
  assign multm_pc0 = multm_reduce_add3b0_maj3b_or3b_wx0 | multm_reduce_add3b0_maj3b_xy0;
  assign multm_pc1 = multm_reduce_add3b0_maj3b_or3b_wx1 | multm_reduce_add3b0_maj3b_xy1;
  assign multm_pc2 = multm_reduce_add3b0_maj3b_or3b_wx2 | multm_reduce_add3b0_maj3b_xy2;
  assign multm_pc3 = multm_reduce_add3b0_maj3b_or3b_wx3 | multm_reduce_add3b0_maj3b_xy3;
  assign multm_pc5 = multm_reduce_add3b1_maj3b_or3b_wx0 | multm_reduce_add3b1_maj3b_xy0;
  assign multm_pc6 = multm_reduce_add3b1_maj3b_or3b_wx1 | multm_reduce_add3b1_maj3b_xy1;
  assign multm_pc7 = multm_reduce_or3_wx | multm_reduce_mw;
  assign multm_ps0 = multm_reduce_add3b0_xor3b_wx0 ^ multm_reduce_sd0;
  assign multm_ps1 = multm_reduce_add3b0_xor3b_wx1 ^ multm_reduce_sd1;
  assign multm_ps2 = multm_reduce_add3b0_xor3b_wx2 ^ multm_reduce_sd2;
  assign multm_ps3 = multm_reduce_add3b0_xor3b_wx3 ^ multm_reduce_sd3;
  assign multm_ps4 = multm_reduce_add3b0_xor3b_wx4 ^ multm_reduce_sd4;
  assign multm_ps5 = multm_reduce_add3b1_xor3b_wx0 ^ multm_reduce_mc4;
  assign multm_ps6 = multm_reduce_add3b1_xor3b_wx1 ^ multm_reduce_mc5;
  assign multm_ps7 = multm_reduce_add3_xor3_wx ^ multm_reduce_mc6;
  assign multm_qcr0 = multm_jpd ? multm_pc0 : multm_qcp0;
  assign multm_qcr1 = multm_jpd ? multm_pc1 : multm_qcp1;
  assign multm_qcr2 = multm_jpd ? multm_pc2 : multm_qcp2;
  assign multm_qcr3 = multm_jpd ? multm_pc3 : multm_qcp3;
  assign multm_qcr4 = xn0 & multm_qcp4;
  assign multm_qcr5 = multm_jpd ? multm_pc5 : multm_qcp5;
  assign multm_qcr6 = multm_jpd ? multm_pc6 : multm_qcp6;
  assign multm_qcr7 = multm_jpd ? multm_pc7 : multm_qcp7;
  assign multm_qsr0 = multm_jpd ? multm_ps0 : multm_qsp0;
  assign multm_qsr1 = multm_jpd ? multm_ps1 : multm_qsp1;
  assign multm_qsr2 = multm_jpd ? multm_ps2 : multm_qsp2;
  assign multm_qsr3 = multm_jpd ? multm_ps3 : multm_qsp3;
  assign multm_qsr4 = multm_jpd ? multm_ps4 : multm_qsp4;
  assign multm_qsr5 = multm_jpd ? multm_ps5 : multm_qsp5;
  assign multm_qsr6 = multm_jpd ? multm_ps6 : multm_qsp6;
  assign multm_qsr7 = multm_jpd ? multm_ps7 : multm_qsp7;
  assign multm_reduce_add3_maj3_or3_wx = multm_reduce_add3_maj3_wx | multm_reduce_add3_maj3_wy;
  assign multm_reduce_add3_maj3_wx = multm_reduce_sb2 & multm_reduce_sa7;
  assign multm_reduce_add3_maj3_wy = multm_reduce_sb2 & multm_reduce_mc6;
  assign multm_reduce_add3_maj3_xy = multm_reduce_sa7 & multm_reduce_mc6;
  assign multm_reduce_add3_xor3_wx = multm_reduce_sb2 ^ multm_reduce_sa7;
  assign multm_reduce_add3b0_maj3b_or3b_wx0 = multm_reduce_add3b0_maj3b_wx0 | multm_reduce_add3b0_maj3b_wy0;
  assign multm_reduce_add3b0_maj3b_or3b_wx1 = multm_reduce_add3b0_maj3b_wx1 | multm_reduce_add3b0_maj3b_wy1;
  assign multm_reduce_add3b0_maj3b_or3b_wx2 = multm_reduce_add3b0_maj3b_wx2 | multm_reduce_add3b0_maj3b_wy2;
  assign multm_reduce_add3b0_maj3b_or3b_wx3 = multm_reduce_add3b0_maj3b_wx3 | multm_reduce_add3b0_maj3b_wy3;
  assign multm_reduce_add3b0_maj3b_or3b_wx4 = multm_reduce_add3b0_maj3b_wx4 | multm_reduce_add3b0_maj3b_wy4;
  assign multm_reduce_add3b0_maj3b_or3b_wx5 = multm_reduce_add3b0_maj3b_wx5 | multm_reduce_add3b0_maj3b_wy5;
  assign multm_reduce_add3b0_maj3b_wx0 = multm_reduce_sa0 & multm_reduce_sc0;
  assign multm_reduce_add3b0_maj3b_wx1 = multm_reduce_sa1 & multm_reduce_sc1;
  assign multm_reduce_add3b0_maj3b_wx2 = multm_reduce_sa2 & multm_reduce_sc2;
  assign multm_reduce_add3b0_maj3b_wx3 = multm_reduce_sa3 & multm_reduce_sc3;
  assign multm_reduce_add3b0_maj3b_wx4 = multm_reduce_sa4 & multm_reduce_sc4;
  assign multm_reduce_add3b0_maj3b_wx5 = multm_reduce_sa5 & multm_reduce_sc5;
  assign multm_reduce_add3b0_maj3b_wy0 = multm_reduce_sa0 & multm_reduce_sd0;
  assign multm_reduce_add3b0_maj3b_wy1 = multm_reduce_sa1 & multm_reduce_sd1;
  assign multm_reduce_add3b0_maj3b_wy2 = multm_reduce_sa2 & multm_reduce_sd2;
  assign multm_reduce_add3b0_maj3b_wy3 = multm_reduce_sa3 & multm_reduce_sd3;
  assign multm_reduce_add3b0_maj3b_wy4 = multm_reduce_sa4 & multm_reduce_sd4;
  assign multm_reduce_add3b0_maj3b_wy5 = multm_reduce_sa5 & multm_reduce_sd5;
  assign multm_reduce_add3b0_maj3b_xy0 = multm_reduce_sc0 & multm_reduce_sd0;
  assign multm_reduce_add3b0_maj3b_xy1 = multm_reduce_sc1 & multm_reduce_sd1;
  assign multm_reduce_add3b0_maj3b_xy2 = multm_reduce_sc2 & multm_reduce_sd2;
  assign multm_reduce_add3b0_maj3b_xy3 = multm_reduce_sc3 & multm_reduce_sd3;
  assign multm_reduce_add3b0_maj3b_xy4 = multm_reduce_sc4 & multm_reduce_sd4;
  assign multm_reduce_add3b0_maj3b_xy5 = multm_reduce_sc5 & multm_reduce_sd5;
  assign multm_reduce_add3b0_xor3b_wx0 = multm_reduce_sa0 ^ multm_reduce_sc0;
  assign multm_reduce_add3b0_xor3b_wx1 = multm_reduce_sa1 ^ multm_reduce_sc1;
  assign multm_reduce_add3b0_xor3b_wx2 = multm_reduce_sa2 ^ multm_reduce_sc2;
  assign multm_reduce_add3b0_xor3b_wx3 = multm_reduce_sa3 ^ multm_reduce_sc3;
  assign multm_reduce_add3b0_xor3b_wx4 = multm_reduce_sa4 ^ multm_reduce_sc4;
  assign multm_reduce_add3b0_xor3b_wx5 = multm_reduce_sa5 ^ multm_reduce_sc5;
  assign multm_reduce_add3b1_maj3b_or3b_wx0 = multm_reduce_add3b1_maj3b_wx0 | multm_reduce_add3b1_maj3b_wy0;
  assign multm_reduce_add3b1_maj3b_or3b_wx1 = multm_reduce_add3b1_maj3b_wx1 | multm_reduce_add3b1_maj3b_wy1;
  assign multm_reduce_add3b1_maj3b_wx0 = multm_reduce_sb0 & multm_reduce_ms5;
  assign multm_reduce_add3b1_maj3b_wx1 = multm_reduce_sb1 & multm_reduce_ms6;
  assign multm_reduce_add3b1_maj3b_wy0 = multm_reduce_sb0 & multm_reduce_mc4;
  assign multm_reduce_add3b1_maj3b_wy1 = multm_reduce_sb1 & multm_reduce_mc5;
  assign multm_reduce_add3b1_maj3b_xy0 = multm_reduce_ms5 & multm_reduce_mc4;
  assign multm_reduce_add3b1_maj3b_xy1 = multm_reduce_ms6 & multm_reduce_mc5;
  assign multm_reduce_add3b1_xor3b_wx0 = multm_reduce_sb0 ^ multm_reduce_ms5;
  assign multm_reduce_add3b1_xor3b_wx1 = multm_reduce_sb1 ^ multm_reduce_ms6;
  assign multm_reduce_mc4 = multm_reduce_add3b0_maj3b_or3b_wx4 | multm_reduce_add3b0_maj3b_xy4;
  assign multm_reduce_mc5 = multm_reduce_add3b0_maj3b_or3b_wx5 | multm_reduce_add3b0_maj3b_xy5;
  assign multm_reduce_mc6 = multm_reduce_sa6 & multm_reduce_sd6;
  assign multm_reduce_ms5 = multm_reduce_add3b0_xor3b_wx5 ^ multm_reduce_sd5;
  assign multm_reduce_ms6 = multm_reduce_sa6 ^ multm_reduce_sd6;
  assign multm_reduce_mulb0_add3b_maj3b_or3b_wx1 = multm_reduce_mulb0_add3b_maj3b_wx1 | multm_reduce_mulb0_add3b_maj3b_wy1;
  assign multm_reduce_mulb0_add3b_maj3b_or3b_wx2 = multm_reduce_mulb0_add3b_maj3b_wx2 | multm_reduce_mulb0_add3b_maj3b_wy2;
  assign multm_reduce_mulb0_add3b_maj3b_or3b_wx4 = multm_reduce_mulb0_add3b_maj3b_wx4 | multm_reduce_mulb0_add3b_maj3b_wy4;
  assign multm_reduce_mulb0_add3b_maj3b_wx1 = multm_reduce_mulb0_sq2 & multm_reduce_mulb0_cq1;
  assign multm_reduce_mulb0_add3b_maj3b_wx2 = multm_reduce_mulb0_sq3 & multm_reduce_mulb0_cq2;
  assign multm_reduce_mulb0_add3b_maj3b_wx4 = multm_reduce_mulb0_sq5 & multm_reduce_mulb0_cq4;
  assign multm_reduce_mulb0_add3b_maj3b_wy1 = multm_reduce_mulb0_sq2 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_maj3b_wy2 = multm_reduce_mulb0_sq3 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_maj3b_wy4 = multm_reduce_mulb0_sq5 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_maj3b_xy1 = multm_reduce_mulb0_cq1 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_maj3b_xy2 = multm_reduce_mulb0_cq2 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_maj3b_xy4 = multm_reduce_mulb0_cq4 & multm_reduce_sa2;
  assign multm_reduce_mulb0_add3b_xor3b_wx1 = multm_reduce_mulb0_sq2 ^ multm_reduce_mulb0_cq1;
  assign multm_reduce_mulb0_add3b_xor3b_wx2 = multm_reduce_mulb0_sq3 ^ multm_reduce_mulb0_cq2;
  assign multm_reduce_mulb0_add3b_xor3b_wx4 = multm_reduce_mulb0_sq5 ^ multm_reduce_mulb0_cq4;
  assign multm_reduce_mulb0_cq0 = xn1 & multm_reduce_mulb0_cp0;
  assign multm_reduce_mulb0_cq1 = xn1 & multm_reduce_mulb0_cp1;
  assign multm_reduce_mulb0_cq2 = xn1 & multm_reduce_mulb0_cp2;
  assign multm_reduce_mulb0_cq3 = xn1 & multm_reduce_mulb0_cp3;
  assign multm_reduce_mulb0_cq4 = xn1 & multm_reduce_mulb0_cp4;
  assign multm_reduce_mulb0_cq5 = xn1 & multm_reduce_mulb0_cp5;
  assign multm_reduce_mulb0_cq6 = xn1 & multm_reduce_mulb0_cp6;
  assign multm_reduce_mulb0_cq7 = xn1 & multm_reduce_mulb0_cp7;
  assign multm_reduce_mulb0_pc0 = multm_reduce_mulb0_sq0 & multm_reduce_sa2;
  assign multm_reduce_mulb0_pc1 = multm_reduce_mulb0_sq1 & multm_reduce_mulb0_cq0;
  assign multm_reduce_mulb0_pc2 = multm_reduce_mulb0_add3b_maj3b_or3b_wx1 | multm_reduce_mulb0_add3b_maj3b_xy1;
  assign multm_reduce_mulb0_pc3 = multm_reduce_mulb0_add3b_maj3b_or3b_wx2 | multm_reduce_mulb0_add3b_maj3b_xy2;
  assign multm_reduce_mulb0_pc4 = multm_reduce_mulb0_sq4 & multm_reduce_mulb0_cq3;
  assign multm_reduce_mulb0_pc5 = multm_reduce_mulb0_add3b_maj3b_or3b_wx4 | multm_reduce_mulb0_add3b_maj3b_xy4;
  assign multm_reduce_mulb0_pc6 = multm_reduce_mulb0_sq6 & multm_reduce_mulb0_cq5;
  assign multm_reduce_mulb0_pc7 = multm_reduce_mulb0_sq7 & multm_reduce_mulb0_cq6;
  assign multm_reduce_mulb0_ps0 = multm_reduce_mulb0_sq1 ^ multm_reduce_mulb0_cq0;
  assign multm_reduce_mulb0_ps1 = multm_reduce_mulb0_add3b_xor3b_wx1 ^ multm_reduce_sa2;
  assign multm_reduce_mulb0_ps2 = multm_reduce_mulb0_add3b_xor3b_wx2 ^ multm_reduce_sa2;
  assign multm_reduce_mulb0_ps3 = multm_reduce_mulb0_sq4 ^ multm_reduce_mulb0_cq3;
  assign multm_reduce_mulb0_ps4 = multm_reduce_mulb0_add3b_xor3b_wx4 ^ multm_reduce_sa2;
  assign multm_reduce_mulb0_ps5 = multm_reduce_mulb0_sq6 ^ multm_reduce_mulb0_cq5;
  assign multm_reduce_mulb0_ps6 = multm_reduce_mulb0_sq7 ^ multm_reduce_mulb0_cq6;
  assign multm_reduce_mulb0_sq0 = xn1 & multm_reduce_mulb0_sp0;
  assign multm_reduce_mulb0_sq1 = xn1 & multm_reduce_mulb0_sp1;
  assign multm_reduce_mulb0_sq2 = xn1 & multm_reduce_mulb0_sp2;
  assign multm_reduce_mulb0_sq3 = xn1 & multm_reduce_mulb0_sp3;
  assign multm_reduce_mulb0_sq4 = xn1 & multm_reduce_mulb0_sp4;
  assign multm_reduce_mulb0_sq5 = xn1 & multm_reduce_mulb0_sp5;
  assign multm_reduce_mulb0_sq6 = xn1 & multm_reduce_mulb0_sp6;
  assign multm_reduce_mulb0_sq7 = xn1 & multm_reduce_mulb0_sp7;
  assign multm_reduce_mulb1_add3_maj3_or3_wx = multm_reduce_mulb1_add3_maj3_wx | multm_reduce_mulb1_add3_maj3_wy;
  assign multm_reduce_mulb1_add3_maj3_wx = multm_reduce_qb2 & multm_reduce_mulb1_cq5;
  assign multm_reduce_mulb1_add3_maj3_wy = multm_reduce_qb2 & multm_reduce_mulb1_pc5;
  assign multm_reduce_mulb1_add3_maj3_xy = multm_reduce_mulb1_cq5 & multm_reduce_mulb1_pc5;
  assign multm_reduce_mulb1_add3_xor3_wx = multm_reduce_qb2 ^ multm_reduce_mulb1_cq5;
  assign multm_reduce_mulb1_add3b_maj3b_or3b_wx0 = multm_reduce_mulb1_add3b_maj3b_wx0 | multm_reduce_mulb1_add3b_maj3b_wy0;
  assign multm_reduce_mulb1_add3b_maj3b_or3b_wx2 = multm_reduce_mulb1_add3b_maj3b_wx2 | multm_reduce_mulb1_add3b_maj3b_wy2;
  assign multm_reduce_mulb1_add3b_maj3b_or3b_wx3 = multm_reduce_mulb1_add3b_maj3b_wx3 | multm_reduce_mulb1_add3b_maj3b_wy3;
  assign multm_reduce_mulb1_add3b_maj3b_wx0 = multm_reduce_mulb1_sq1 & multm_reduce_mulb1_cq0;
  assign multm_reduce_mulb1_add3b_maj3b_wx2 = multm_reduce_mulb1_sq3 & multm_reduce_mulb1_cq2;
  assign multm_reduce_mulb1_add3b_maj3b_wx3 = multm_reduce_mulb1_sq4 & multm_reduce_mulb1_cq3;
  assign multm_reduce_mulb1_add3b_maj3b_wy0 = multm_reduce_mulb1_sq1 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_maj3b_wy2 = multm_reduce_mulb1_sq3 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_maj3b_wy3 = multm_reduce_mulb1_sq4 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_maj3b_xy0 = multm_reduce_mulb1_cq0 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_maj3b_xy2 = multm_reduce_mulb1_cq2 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_maj3b_xy3 = multm_reduce_mulb1_cq3 & multm_reduce_qb2;
  assign multm_reduce_mulb1_add3b_xor3b_wx0 = multm_reduce_mulb1_sq1 ^ multm_reduce_mulb1_cq0;
  assign multm_reduce_mulb1_add3b_xor3b_wx2 = multm_reduce_mulb1_sq3 ^ multm_reduce_mulb1_cq2;
  assign multm_reduce_mulb1_add3b_xor3b_wx3 = multm_reduce_mulb1_sq4 ^ multm_reduce_mulb1_cq3;
  assign multm_reduce_mulb1_cq0 = xn2 & multm_reduce_sd1;
  assign multm_reduce_mulb1_cq1 = xn2 & multm_reduce_sd2;
  assign multm_reduce_mulb1_cq2 = xn2 & multm_reduce_sd3;
  assign multm_reduce_mulb1_cq3 = xn2 & multm_reduce_sd4;
  assign multm_reduce_mulb1_cq4 = xn2 & multm_reduce_sd5;
  assign multm_reduce_mulb1_cq5 = xn2 & multm_reduce_sd6;
  assign multm_reduce_mulb1_pc0 = multm_reduce_mulb1_sq0 & multm_reduce_qb2;
  assign multm_reduce_mulb1_pc1 = multm_reduce_mulb1_add3b_maj3b_or3b_wx0 | multm_reduce_mulb1_add3b_maj3b_xy0;
  assign multm_reduce_mulb1_pc2 = multm_reduce_mulb1_sq2 & multm_reduce_mulb1_cq1;
  assign multm_reduce_mulb1_pc3 = multm_reduce_mulb1_add3b_maj3b_or3b_wx2 | multm_reduce_mulb1_add3b_maj3b_xy2;
  assign multm_reduce_mulb1_pc4 = multm_reduce_mulb1_add3b_maj3b_or3b_wx3 | multm_reduce_mulb1_add3b_maj3b_xy3;
  assign multm_reduce_mulb1_pc5 = multm_reduce_mulb1_sq5 & multm_reduce_mulb1_cq4;
  assign multm_reduce_mulb1_ps0 = multm_reduce_mulb1_add3b_xor3b_wx0 ^ multm_reduce_qb2;
  assign multm_reduce_mulb1_ps1 = multm_reduce_mulb1_sq2 ^ multm_reduce_mulb1_cq1;
  assign multm_reduce_mulb1_ps2 = multm_reduce_mulb1_add3b_xor3b_wx2 ^ multm_reduce_qb2;
  assign multm_reduce_mulb1_ps3 = multm_reduce_mulb1_add3b_xor3b_wx3 ^ multm_reduce_qb2;
  assign multm_reduce_mulb1_ps4 = multm_reduce_mulb1_sq5 ^ multm_reduce_mulb1_cq4;
  assign multm_reduce_mulb1_sq0 = xn2 & multm_reduce_sc0;
  assign multm_reduce_mulb1_sq1 = xn2 & multm_reduce_sc1;
  assign multm_reduce_mulb1_sq2 = xn2 & multm_reduce_sc2;
  assign multm_reduce_mulb1_sq3 = xn2 & multm_reduce_sc3;
  assign multm_reduce_mulb1_sq4 = xn2 & multm_reduce_sc4;
  assign multm_reduce_mulb1_sq5 = xn2 & multm_reduce_sc5;
  assign multm_reduce_mulsc_mulb_add3_maj3_or3_wx = multm_reduce_mulsc_mulb_add3_maj3_wx | multm_reduce_mulsc_mulb_add3_maj3_wy;
  assign multm_reduce_mulsc_mulb_add3_maj3_wx = multm_reduce_mulsc_mulb_yoc6 & multm_reduce_mulsc_mulb_cq6;
  assign multm_reduce_mulsc_mulb_add3_maj3_wy = multm_reduce_mulsc_mulb_yoc6 & multm_reduce_mulsc_mulb_pc6;
  assign multm_reduce_mulsc_mulb_add3_maj3_xy = multm_reduce_mulsc_mulb_cq6 & multm_reduce_mulsc_mulb_pc6;
  assign multm_reduce_mulsc_mulb_add3_xor3_wx = multm_reduce_mulsc_mulb_yoc6 ^ multm_reduce_mulsc_mulb_cq6;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx0 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy0;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx1 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy1;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx2 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy2;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx3 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy3;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx4 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy4;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5 = multm_reduce_mulsc_mulb_add3b0_maj3b_wx5 | multm_reduce_mulsc_mulb_add3b0_maj3b_wy5;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx0 = multm_reduce_mulsc_mulb_sq1 & multm_reduce_mulsc_mulb_cq0;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx1 = multm_reduce_mulsc_mulb_sq2 & multm_reduce_mulsc_mulb_cq1;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx2 = multm_reduce_mulsc_mulb_sq3 & multm_reduce_mulsc_mulb_cq2;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx3 = multm_reduce_mulsc_mulb_sq4 & multm_reduce_mulsc_mulb_cq3;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx4 = multm_reduce_mulsc_mulb_sq5 & multm_reduce_mulsc_mulb_cq4;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wx5 = multm_reduce_mulsc_mulb_sq6 & multm_reduce_mulsc_mulb_cq5;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy0 = multm_reduce_mulsc_mulb_sq1 & multm_reduce_mulsc_mulb_yos1;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy1 = multm_reduce_mulsc_mulb_sq2 & multm_reduce_mulsc_mulb_yos2;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy2 = multm_reduce_mulsc_mulb_sq3 & multm_reduce_mulsc_mulb_yos3;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy3 = multm_reduce_mulsc_mulb_sq4 & multm_reduce_mulsc_mulb_yos4;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy4 = multm_reduce_mulsc_mulb_sq5 & multm_reduce_mulsc_mulb_yos5;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_wy5 = multm_reduce_mulsc_mulb_sq6 & multm_reduce_mulsc_mulb_yos6;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy0 = multm_reduce_mulsc_mulb_cq0 & multm_reduce_mulsc_mulb_yos1;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy1 = multm_reduce_mulsc_mulb_cq1 & multm_reduce_mulsc_mulb_yos2;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy2 = multm_reduce_mulsc_mulb_cq2 & multm_reduce_mulsc_mulb_yos3;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy3 = multm_reduce_mulsc_mulb_cq3 & multm_reduce_mulsc_mulb_yos4;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy4 = multm_reduce_mulsc_mulb_cq4 & multm_reduce_mulsc_mulb_yos5;
  assign multm_reduce_mulsc_mulb_add3b0_maj3b_xy5 = multm_reduce_mulsc_mulb_cq5 & multm_reduce_mulsc_mulb_yos6;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx0 = multm_reduce_mulsc_mulb_sq1 ^ multm_reduce_mulsc_mulb_cq0;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx1 = multm_reduce_mulsc_mulb_sq2 ^ multm_reduce_mulsc_mulb_cq1;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx2 = multm_reduce_mulsc_mulb_sq3 ^ multm_reduce_mulsc_mulb_cq2;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx3 = multm_reduce_mulsc_mulb_sq4 ^ multm_reduce_mulsc_mulb_cq3;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx4 = multm_reduce_mulsc_mulb_sq5 ^ multm_reduce_mulsc_mulb_cq4;
  assign multm_reduce_mulsc_mulb_add3b0_xor3b_wx5 = multm_reduce_mulsc_mulb_sq6 ^ multm_reduce_mulsc_mulb_cq5;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx0 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy0;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx1 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy1;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx2 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy2;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx3 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy3;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx4 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy4;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5 = multm_reduce_mulsc_mulb_add3b1_maj3b_wx5 | multm_reduce_mulsc_mulb_add3b1_maj3b_wy5;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx0 = multm_reduce_mulsc_mulb_yoc0 & multm_reduce_mulsc_mulb_ps0;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx1 = multm_reduce_mulsc_mulb_yoc1 & multm_reduce_mulsc_mulb_ps1;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx2 = multm_reduce_mulsc_mulb_yoc2 & multm_reduce_mulsc_mulb_ps2;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx3 = multm_reduce_mulsc_mulb_yoc3 & multm_reduce_mulsc_mulb_ps3;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx4 = multm_reduce_mulsc_mulb_yoc4 & multm_reduce_mulsc_mulb_ps4;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wx5 = multm_reduce_mulsc_mulb_yoc5 & multm_reduce_mulsc_mulb_ps5;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy0 = multm_reduce_mulsc_mulb_yoc0 & multm_reduce_mulsc_mulb_pc0;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy1 = multm_reduce_mulsc_mulb_yoc1 & multm_reduce_mulsc_mulb_pc1;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy2 = multm_reduce_mulsc_mulb_yoc2 & multm_reduce_mulsc_mulb_pc2;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy3 = multm_reduce_mulsc_mulb_yoc3 & multm_reduce_mulsc_mulb_pc3;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy4 = multm_reduce_mulsc_mulb_yoc4 & multm_reduce_mulsc_mulb_pc4;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_wy5 = multm_reduce_mulsc_mulb_yoc5 & multm_reduce_mulsc_mulb_pc5;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy0 = multm_reduce_mulsc_mulb_ps0 & multm_reduce_mulsc_mulb_pc0;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy1 = multm_reduce_mulsc_mulb_ps1 & multm_reduce_mulsc_mulb_pc1;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy2 = multm_reduce_mulsc_mulb_ps2 & multm_reduce_mulsc_mulb_pc2;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy3 = multm_reduce_mulsc_mulb_ps3 & multm_reduce_mulsc_mulb_pc3;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy4 = multm_reduce_mulsc_mulb_ps4 & multm_reduce_mulsc_mulb_pc4;
  assign multm_reduce_mulsc_mulb_add3b1_maj3b_xy5 = multm_reduce_mulsc_mulb_ps5 & multm_reduce_mulsc_mulb_pc5;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx0 = multm_reduce_mulsc_mulb_yoc0 ^ multm_reduce_mulsc_mulb_ps0;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx1 = multm_reduce_mulsc_mulb_yoc1 ^ multm_reduce_mulsc_mulb_ps1;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx2 = multm_reduce_mulsc_mulb_yoc2 ^ multm_reduce_mulsc_mulb_ps2;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx3 = multm_reduce_mulsc_mulb_yoc3 ^ multm_reduce_mulsc_mulb_ps3;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx4 = multm_reduce_mulsc_mulb_yoc4 ^ multm_reduce_mulsc_mulb_ps4;
  assign multm_reduce_mulsc_mulb_add3b1_xor3b_wx5 = multm_reduce_mulsc_mulb_yoc5 ^ multm_reduce_mulsc_mulb_ps5;
  assign multm_reduce_mulsc_mulb_cq0 = xn3 & multm_reduce_sb0;
  assign multm_reduce_mulsc_mulb_cq1 = xn3 & multm_reduce_sb1;
  assign multm_reduce_mulsc_mulb_cq2 = xn3 & multm_reduce_sb2;
  assign multm_reduce_mulsc_mulb_cq3 = xn3 & multm_reduce_sb3;
  assign multm_reduce_mulsc_mulb_cq4 = xn3 & multm_reduce_mulsc_mulb_cp4;
  assign multm_reduce_mulsc_mulb_cq5 = xn3 & multm_reduce_mulsc_mulb_cp5;
  assign multm_reduce_mulsc_mulb_cq6 = xn3 & multm_reduce_mulsc_mulb_cp6;
  assign multm_reduce_mulsc_mulb_pc0 = multm_reduce_mulsc_mulb_sq0 & multm_reduce_mulsc_mulb_yos0;
  assign multm_reduce_mulsc_mulb_pc1 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx0 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy0;
  assign multm_reduce_mulsc_mulb_pc2 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx1 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy1;
  assign multm_reduce_mulsc_mulb_pc3 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx2 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy2;
  assign multm_reduce_mulsc_mulb_pc4 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx3 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy3;
  assign multm_reduce_mulsc_mulb_pc5 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx4 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy4;
  assign multm_reduce_mulsc_mulb_pc6 = multm_reduce_mulsc_mulb_add3b0_maj3b_or3b_wx5 | multm_reduce_mulsc_mulb_add3b0_maj3b_xy5;
  assign multm_reduce_mulsc_mulb_ps0 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx0 ^ multm_reduce_mulsc_mulb_yos1;
  assign multm_reduce_mulsc_mulb_ps1 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx1 ^ multm_reduce_mulsc_mulb_yos2;
  assign multm_reduce_mulsc_mulb_ps2 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx2 ^ multm_reduce_mulsc_mulb_yos3;
  assign multm_reduce_mulsc_mulb_ps3 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx3 ^ multm_reduce_mulsc_mulb_yos4;
  assign multm_reduce_mulsc_mulb_ps4 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx4 ^ multm_reduce_mulsc_mulb_yos5;
  assign multm_reduce_mulsc_mulb_ps5 = multm_reduce_mulsc_mulb_add3b0_xor3b_wx5 ^ multm_reduce_mulsc_mulb_yos6;
  assign multm_reduce_mulsc_mulb_sq0 = xn3 & multm_reduce_sa4;
  assign multm_reduce_mulsc_mulb_sq1 = xn3 & multm_reduce_sa5;
  assign multm_reduce_mulsc_mulb_sq2 = xn3 & multm_reduce_sa6;
  assign multm_reduce_mulsc_mulb_sq3 = xn3 & multm_reduce_sa7;
  assign multm_reduce_mulsc_mulb_sq4 = xn3 & multm_reduce_sa8;
  assign multm_reduce_mulsc_mulb_sq5 = xn3 & multm_reduce_mulsc_mulb_sp5;
  assign multm_reduce_mulsc_mulb_sq6 = xn3 & multm_reduce_mulsc_mulb_sp6;
  assign multm_reduce_mulsc_mulb_yoc0 = multm_reduce_mulsc_xbd & yc0_o;
  assign multm_reduce_mulsc_mulb_yoc1 = multm_reduce_mulsc_xbd & yc1_o;
  assign multm_reduce_mulsc_mulb_yoc2 = multm_reduce_mulsc_xbd & yc2_o;
  assign multm_reduce_mulsc_mulb_yoc3 = multm_reduce_mulsc_xbd & yc3_o;
  assign multm_reduce_mulsc_mulb_yoc4 = multm_reduce_mulsc_xbd & yc4_o;
  assign multm_reduce_mulsc_mulb_yoc5 = multm_reduce_mulsc_xbd & yc5_o;
  assign multm_reduce_mulsc_mulb_yoc6 = multm_reduce_mulsc_xbd & yc6_o;
  assign multm_reduce_mulsc_mulb_yos0 = multm_reduce_mulsc_xbd & ys0_o;
  assign multm_reduce_mulsc_mulb_yos1 = multm_reduce_mulsc_xbd & ys1_o;
  assign multm_reduce_mulsc_mulb_yos2 = multm_reduce_mulsc_xbd & ys2_o;
  assign multm_reduce_mulsc_mulb_yos3 = multm_reduce_mulsc_xbd & ys3_o;
  assign multm_reduce_mulsc_mulb_yos4 = multm_reduce_mulsc_xbd & ys4_o;
  assign multm_reduce_mulsc_mulb_yos5 = multm_reduce_mulsc_xbd & ys5_o;
  assign multm_reduce_mulsc_mulb_yos6 = multm_reduce_mulsc_xbd & ys6_o;
  assign multm_reduce_mulsc_shrsc_cq0 = multm_reduce_mulsc_shrsc_sp0 & multm_reduce_mulsc_shrsc_cp0;
  assign multm_reduce_mulsc_shrsc_cq1 = multm_reduce_mulsc_shrsc_sp1 & multm_reduce_mulsc_shrsc_cp1;
  assign multm_reduce_mulsc_shrsc_cq2 = multm_reduce_mulsc_shrsc_sp2 & multm_reduce_mulsc_shrsc_cp2;
  assign multm_reduce_mulsc_shrsc_cq3 = multm_reduce_mulsc_shrsc_sp3 & multm_reduce_mulsc_shrsc_cp3;
  assign multm_reduce_mulsc_shrsc_cq4 = multm_reduce_mulsc_shrsc_sp4 & multm_reduce_mulsc_shrsc_cp4;
  assign multm_reduce_mulsc_shrsc_cq5 = multm_reduce_mulsc_shrsc_sp5 & multm_reduce_mulsc_shrsc_cp5;
  assign multm_reduce_mulsc_shrsc_cr0 = sadd ? yc0_o : multm_reduce_mulsc_shrsc_cq0;
  assign multm_reduce_mulsc_shrsc_cr1 = sadd ? yc1_o : multm_reduce_mulsc_shrsc_cq1;
  assign multm_reduce_mulsc_shrsc_cr2 = sadd ? yc2_o : multm_reduce_mulsc_shrsc_cq2;
  assign multm_reduce_mulsc_shrsc_cr3 = sadd ? yc3_o : multm_reduce_mulsc_shrsc_cq3;
  assign multm_reduce_mulsc_shrsc_cr4 = sadd ? yc4_o : multm_reduce_mulsc_shrsc_cq4;
  assign multm_reduce_mulsc_shrsc_cr5 = sadd ? yc5_o : multm_reduce_mulsc_shrsc_cq5;
  assign multm_reduce_mulsc_shrsc_cr6 = sadd & yc6_o;
  assign multm_reduce_mulsc_shrsc_sq0 = multm_reduce_mulsc_shrsc_sp0 ^ multm_reduce_mulsc_shrsc_cp0;
  assign multm_reduce_mulsc_shrsc_sq1 = multm_reduce_mulsc_shrsc_sp1 ^ multm_reduce_mulsc_shrsc_cp1;
  assign multm_reduce_mulsc_shrsc_sq2 = multm_reduce_mulsc_shrsc_sp2 ^ multm_reduce_mulsc_shrsc_cp2;
  assign multm_reduce_mulsc_shrsc_sq3 = multm_reduce_mulsc_shrsc_sp3 ^ multm_reduce_mulsc_shrsc_cp3;
  assign multm_reduce_mulsc_shrsc_sq4 = multm_reduce_mulsc_shrsc_sp4 ^ multm_reduce_mulsc_shrsc_cp4;
  assign multm_reduce_mulsc_shrsc_sq5 = multm_reduce_mulsc_shrsc_sp5 ^ multm_reduce_mulsc_shrsc_cp5;
  assign multm_reduce_mulsc_shrsc_sr0 = sadd ? ys1_o : multm_reduce_mulsc_shrsc_sq1;
  assign multm_reduce_mulsc_shrsc_sr1 = sadd ? ys2_o : multm_reduce_mulsc_shrsc_sq2;
  assign multm_reduce_mulsc_shrsc_sr2 = sadd ? ys3_o : multm_reduce_mulsc_shrsc_sq3;
  assign multm_reduce_mulsc_shrsc_sr3 = sadd ? ys4_o : multm_reduce_mulsc_shrsc_sq4;
  assign multm_reduce_mulsc_shrsc_sr4 = sadd ? ys5_o : multm_reduce_mulsc_shrsc_sq5;
  assign multm_reduce_mulsc_shrsc_sr5 = sadd ? ys6_o : multm_reduce_mulsc_shrsc_cp6;
  assign multm_reduce_mulsc_xb = sadd ? ys0_o : multm_reduce_mulsc_shrsc_sq0;
  assign multm_reduce_mw = multm_reduce_add3_maj3_or3_wx | multm_reduce_add3_maj3_xy;
  assign multm_reduce_or3_wx = multm_reduce_sb3 | multm_reduce_sa8;
  assign multm_reduce_pb = multm_reduce_mulsc_mulb_sq0 ^ multm_reduce_mulsc_mulb_yos0;
  assign multm_reduce_pc0 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx0 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy0;
  assign multm_reduce_pc1 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx1 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy1;
  assign multm_reduce_pc2 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx2 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy2;
  assign multm_reduce_pc3 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx3 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy3;
  assign multm_reduce_pc4 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx4 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy4;
  assign multm_reduce_pc5 = multm_reduce_mulsc_mulb_add3b1_maj3b_or3b_wx5 | multm_reduce_mulsc_mulb_add3b1_maj3b_xy5;
  assign multm_reduce_pc6 = multm_reduce_mulsc_mulb_add3_maj3_or3_wx | multm_reduce_mulsc_mulb_add3_maj3_xy;
  assign multm_reduce_ps0 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx0 ^ multm_reduce_mulsc_mulb_pc0;
  assign multm_reduce_ps1 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx1 ^ multm_reduce_mulsc_mulb_pc1;
  assign multm_reduce_ps2 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx2 ^ multm_reduce_mulsc_mulb_pc2;
  assign multm_reduce_ps3 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx3 ^ multm_reduce_mulsc_mulb_pc3;
  assign multm_reduce_ps4 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx4 ^ multm_reduce_mulsc_mulb_pc4;
  assign multm_reduce_ps5 = multm_reduce_mulsc_mulb_add3b1_xor3b_wx5 ^ multm_reduce_mulsc_mulb_pc5;
  assign multm_reduce_ps6 = multm_reduce_mulsc_mulb_add3_xor3_wx ^ multm_reduce_mulsc_mulb_pc6;
  assign multm_reduce_qb = multm_reduce_mulb0_sq0 ^ multm_reduce_sa2;
  assign multm_reduce_qc0 = multm_reduce_mulb0_ps0 & multm_reduce_mulb0_pc0;
  assign multm_reduce_qc1 = multm_reduce_mulb0_ps1 & multm_reduce_mulb0_pc1;
  assign multm_reduce_qc2 = multm_reduce_mulb0_ps2 & multm_reduce_mulb0_pc2;
  assign multm_reduce_qc3 = multm_reduce_mulb0_ps3 & multm_reduce_mulb0_pc3;
  assign multm_reduce_qc4 = multm_reduce_mulb0_ps4 & multm_reduce_mulb0_pc4;
  assign multm_reduce_qc5 = multm_reduce_mulb0_ps5 & multm_reduce_mulb0_pc5;
  assign multm_reduce_qc6 = multm_reduce_mulb0_ps6 & multm_reduce_mulb0_pc6;
  assign multm_reduce_qc7 = multm_reduce_mulb0_cq7 & multm_reduce_mulb0_pc7;
  assign multm_reduce_qs0 = multm_reduce_mulb0_ps0 ^ multm_reduce_mulb0_pc0;
  assign multm_reduce_qs1 = multm_reduce_mulb0_ps1 ^ multm_reduce_mulb0_pc1;
  assign multm_reduce_qs2 = multm_reduce_mulb0_ps2 ^ multm_reduce_mulb0_pc2;
  assign multm_reduce_qs3 = multm_reduce_mulb0_ps3 ^ multm_reduce_mulb0_pc3;
  assign multm_reduce_qs4 = multm_reduce_mulb0_ps4 ^ multm_reduce_mulb0_pc4;
  assign multm_reduce_qs5 = multm_reduce_mulb0_ps5 ^ multm_reduce_mulb0_pc5;
  assign multm_reduce_qs6 = multm_reduce_mulb0_ps6 ^ multm_reduce_mulb0_pc6;
  assign multm_reduce_qs7 = multm_reduce_mulb0_cq7 ^ multm_reduce_mulb0_pc7;
  assign multm_reduce_sticky_q = xn2 & multm_reduce_sd0;
  assign multm_reduce_vb = multm_reduce_mulb1_sq0 ^ multm_reduce_qb2;
  assign multm_reduce_vc0 = multm_reduce_mulb1_ps0 & multm_reduce_mulb1_pc0;
  assign multm_reduce_vc1 = multm_reduce_mulb1_ps1 & multm_reduce_mulb1_pc1;
  assign multm_reduce_vc2 = multm_reduce_mulb1_ps2 & multm_reduce_mulb1_pc2;
  assign multm_reduce_vc3 = multm_reduce_mulb1_ps3 & multm_reduce_mulb1_pc3;
  assign multm_reduce_vc4 = multm_reduce_mulb1_ps4 & multm_reduce_mulb1_pc4;
  assign multm_reduce_vc5 = multm_reduce_mulb1_add3_maj3_or3_wx | multm_reduce_mulb1_add3_maj3_xy;
  assign multm_reduce_vs0 = multm_reduce_mulb1_ps0 ^ multm_reduce_mulb1_pc0;
  assign multm_reduce_vs1 = multm_reduce_mulb1_ps1 ^ multm_reduce_mulb1_pc1;
  assign multm_reduce_vs2 = multm_reduce_mulb1_ps2 ^ multm_reduce_mulb1_pc2;
  assign multm_reduce_vs3 = multm_reduce_mulb1_ps3 ^ multm_reduce_mulb1_pc3;
  assign multm_reduce_vs4 = multm_reduce_mulb1_ps4 ^ multm_reduce_mulb1_pc4;
  assign multm_reduce_vs5 = multm_reduce_mulb1_add3_xor3_wx ^ multm_reduce_mulb1_pc5;
  assign multm_reduce_vt = multm_reduce_vb | multm_reduce_sticky_q;
  assign nor2_zn = sad | sbd;
  assign pcq0 = sbd ? xc[0] : qc0;
  assign pcq1 = sbd ? xc[1] : qc1;
  assign pcq2 = sbd ? xc[2] : qc2;
  assign pcq3 = sbd ? xc[3] : qc3;
  assign pcq4 = sbd ? xc[4] : qc4;
  assign pcq5 = sbd ? xc[5] : qc5;
  assign pcq6 = sbd ? xc[6] : qc6;
  assign pcr0 = sad ? pcq0 : yc0_o;
  assign pcr1 = sad ? pcq1 : yc1_o;
  assign pcr2 = sad ? pcq2 : yc2_o;
  assign pcr3 = sad ? pcq3 : yc3_o;
  assign pcr4 = sad ? pcq4 : yc4_o;
  assign pcr5 = sad ? pcq5 : yc5_o;
  assign pcr6 = sad ? pcq6 : yc6_o;
  assign psq0 = sbd ? xs[0] : qs0;
  assign psq1 = sbd ? xs[1] : qs1;
  assign psq2 = sbd ? xs[2] : qs2;
  assign psq3 = sbd ? xs[3] : qs3;
  assign psq4 = sbd ? xs[4] : qs4;
  assign psq5 = sbd ? xs[5] : qs5;
  assign psq6 = sbd ? xs[6] : qs6;
  assign psr0 = sad ? psq0 : ys0_o;
  assign psr1 = sad ? psq1 : ys1_o;
  assign psr2 = sad ? psq2 : ys2_o;
  assign psr3 = sad ? psq3 : ys3_o;
  assign psr4 = sad ? psq4 : ys4_o;
  assign psr5 = sad ? psq5 : ys5_o;
  assign psr6 = sad ? psq6 : ys6_o;
  assign qc0 = multm_qsp0 & multm_compress_rn0;
  assign qc1 = multm_compress_add3b_maj3b_or3b_wx0 | multm_compress_add3b_maj3b_xy0;
  assign qc2 = multm_compress_add3b_maj3b_or3b_wx1 | multm_compress_add3b_maj3b_xy1;
  assign qc3 = multm_compress_add3b_maj3b_or3b_wx2 | multm_compress_add3b_maj3b_xy2;
  assign qc4 = multm_compress_add3b_maj3b_or3b_wx3 | multm_compress_add3b_maj3b_xy3;
  assign qc5 = multm_compress_add3b_maj3b_or3b_wx4 | multm_compress_add3b_maj3b_xy4;
  assign qc6 = multm_compress_add3b_maj3b_or3b_wx5 | multm_compress_add3b_maj3b_xy5;
  assign qs0 = multm_qsp0 ^ multm_compress_rn0;
  assign qs1 = multm_compress_add3b_xor3b_wx0 ^ multm_compress_rn1;
  assign qs2 = multm_compress_add3b_xor3b_wx1 ^ multm_compress_nsd;
  assign qs3 = multm_compress_add3b_xor3b_wx2 ^ multm_compress_rn1;
  assign qs4 = multm_compress_add3b_xor3b_wx3 ^ multm_compress_rn4;
  assign qs5 = multm_compress_add3b_xor3b_wx4 ^ multm_compress_rn0;
  assign qs6 = multm_compress_add3b_xor3b_wx5 ^ multm_compress_rn1;
  assign san = ~sa;
  assign sap = sb & jp;
  assign saq = san & sap;
  assign sar = ld | saq;
  assign sbp = sa & mdn;
  assign sbq = sb ? jpn : sbp;
  assign sbr = ld | sbq;
  assign srdd = sadd & sbdd;
  assign xn0 = ~multm_jpd;
  assign xn1 = ~multm_reduce_ld1;
  assign xn2 = ~multm_reduce_ld2;
  assign xn3 = ~multm_reduce_pipe0_x2;
  assign xn4 = ~sadd;
  assign xn5 = ~srdd;
  assign xn6 = ~multm_compress_ncd;
  assign dn = dn_o;
  assign ys[0] = ys0_o;
  assign ys[1] = ys1_o;
  assign ys[2] = ys2_o;
  assign ys[3] = ys3_o;
  assign ys[4] = ys4_o;
  assign ys[5] = ys5_o;
  assign ys[6] = ys6_o;
  assign yc[0] = yc0_o;
  assign yc[1] = yc1_o;
  assign yc[2] = yc2_o;
  assign yc[3] = yc3_o;
  assign yc[4] = yc4_o;
  assign yc[5] = yc5_o;
  assign yc[6] = yc6_o;

  always @(posedge clk)
    begin
      ctre_cp0 <= ctre_cr0;
      ctre_cp1 <= ctre_cr1;
      ctre_cp2 <= ctre_cr2;
      ctre_cp3 <= ctre_cr3;
      ctre_dp <= md;
      ctre_sp0 <= ctre_sr0;
      ctre_sp1 <= ctre_sr1;
      ctre_sp2 <= ctre_sr2;
      ctre_sp3 <= ctre_sr3;
      multm_compress_ncd <= multm_compress_pipe1_x1;
      multm_compress_nsd <= multm_compress_pipe0_x1;
      multm_compress_pipe0_x1 <= multm_compress_ns;
      multm_compress_pipe1_x1 <= multm_compress_nc;
      multm_ctrp_ctr_cp0 <= multm_ctrp_ctr_cr0;
      multm_ctrp_ctr_cp1 <= multm_ctrp_ctr_cr1;
      multm_ctrp_ctr_cp2 <= multm_ctrp_ctr_cr2;
      multm_ctrp_ctr_cp3 <= multm_ctrp_ctr_cr3;
      multm_ctrp_ctr_dp <= multm_ctrp_ds;
      multm_ctrp_ctr_sp0 <= multm_ctrp_ctr_sr0;
      multm_ctrp_ctr_sp1 <= multm_ctrp_ctr_sr1;
      multm_ctrp_ctr_sp2 <= multm_ctrp_ctr_sr2;
      multm_jpd <= multm_pipe_x1;
      multm_pipe_x1 <= jp;
      multm_qcp0 <= multm_qcr0;
      multm_qcp1 <= multm_qcr1;
      multm_qcp2 <= multm_qcr2;
      multm_qcp3 <= multm_qcr3;
      multm_qcp4 <= multm_qcr4;
      multm_qcp5 <= multm_qcr5;
      multm_qcp6 <= multm_qcr6;
      multm_qcp7 <= multm_qcr7;
      multm_qsp0 <= multm_qsr0;
      multm_qsp1 <= multm_qsr1;
      multm_qsp2 <= multm_qsr2;
      multm_qsp3 <= multm_qsr3;
      multm_qsp4 <= multm_qsr4;
      multm_qsp5 <= multm_qsr5;
      multm_qsp6 <= multm_qsr6;
      multm_qsp7 <= multm_qsr7;
      multm_reduce_ld1 <= multm_reduce_pipe0_x3;
      multm_reduce_ld2 <= multm_reduce_pipe1_x1;
      multm_reduce_mulb0_cp0 <= multm_reduce_qc0;
      multm_reduce_mulb0_cp1 <= multm_reduce_qc1;
      multm_reduce_mulb0_cp2 <= multm_reduce_qc2;
      multm_reduce_mulb0_cp3 <= multm_reduce_qc3;
      multm_reduce_mulb0_cp4 <= multm_reduce_qc4;
      multm_reduce_mulb0_cp5 <= multm_reduce_qc5;
      multm_reduce_mulb0_cp6 <= multm_reduce_qc6;
      multm_reduce_mulb0_cp7 <= multm_reduce_qc7;
      multm_reduce_mulb0_sp0 <= multm_reduce_qs0;
      multm_reduce_mulb0_sp1 <= multm_reduce_qs1;
      multm_reduce_mulb0_sp2 <= multm_reduce_qs2;
      multm_reduce_mulb0_sp3 <= multm_reduce_qs3;
      multm_reduce_mulb0_sp4 <= multm_reduce_qs4;
      multm_reduce_mulb0_sp5 <= multm_reduce_qs5;
      multm_reduce_mulb0_sp6 <= multm_reduce_qs6;
      multm_reduce_mulb0_sp7 <= multm_reduce_qs7;
      multm_reduce_mulsc_mulb_cp4 <= multm_reduce_pc4;
      multm_reduce_mulsc_mulb_cp5 <= multm_reduce_pc5;
      multm_reduce_mulsc_mulb_cp6 <= multm_reduce_pc6;
      multm_reduce_mulsc_mulb_sp5 <= multm_reduce_ps5;
      multm_reduce_mulsc_mulb_sp6 <= multm_reduce_ps6;
      multm_reduce_mulsc_pipe_x1 <= multm_reduce_mulsc_xb;
      multm_reduce_mulsc_shrsc_cp0 <= multm_reduce_mulsc_shrsc_cr0;
      multm_reduce_mulsc_shrsc_cp1 <= multm_reduce_mulsc_shrsc_cr1;
      multm_reduce_mulsc_shrsc_cp2 <= multm_reduce_mulsc_shrsc_cr2;
      multm_reduce_mulsc_shrsc_cp3 <= multm_reduce_mulsc_shrsc_cr3;
      multm_reduce_mulsc_shrsc_cp4 <= multm_reduce_mulsc_shrsc_cr4;
      multm_reduce_mulsc_shrsc_cp5 <= multm_reduce_mulsc_shrsc_cr5;
      multm_reduce_mulsc_shrsc_cp6 <= multm_reduce_mulsc_shrsc_cr6;
      multm_reduce_mulsc_shrsc_sp0 <= multm_reduce_mulsc_shrsc_sr0;
      multm_reduce_mulsc_shrsc_sp1 <= multm_reduce_mulsc_shrsc_sr1;
      multm_reduce_mulsc_shrsc_sp2 <= multm_reduce_mulsc_shrsc_sr2;
      multm_reduce_mulsc_shrsc_sp3 <= multm_reduce_mulsc_shrsc_sr3;
      multm_reduce_mulsc_shrsc_sp4 <= multm_reduce_mulsc_shrsc_sr4;
      multm_reduce_mulsc_shrsc_sp5 <= multm_reduce_mulsc_shrsc_sr5;
      multm_reduce_mulsc_xbd <= multm_reduce_mulsc_pipe_x1;
      multm_reduce_pipe0_x1 <= sadd;
      multm_reduce_pipe0_x2 <= multm_reduce_pipe0_x1;
      multm_reduce_pipe0_x3 <= multm_reduce_pipe0_x2;
      multm_reduce_pipe1_x1 <= multm_reduce_ld1;
      multm_reduce_pipe2_x1 <= multm_reduce_qb;
      multm_reduce_qb2 <= multm_reduce_pipe2_x1;
      multm_reduce_sa0 <= multm_reduce_sa1;
      multm_reduce_sa1 <= multm_reduce_sa2;
      multm_reduce_sa2 <= multm_reduce_sa3;
      multm_reduce_sa3 <= multm_reduce_pb;
      multm_reduce_sa4 <= multm_reduce_ps0;
      multm_reduce_sa5 <= multm_reduce_ps1;
      multm_reduce_sa6 <= multm_reduce_ps2;
      multm_reduce_sa7 <= multm_reduce_ps3;
      multm_reduce_sa8 <= multm_reduce_ps4;
      multm_reduce_sb0 <= multm_reduce_pc0;
      multm_reduce_sb1 <= multm_reduce_pc1;
      multm_reduce_sb2 <= multm_reduce_pc2;
      multm_reduce_sb3 <= multm_reduce_pc3;
      multm_reduce_sc0 <= multm_reduce_vs0;
      multm_reduce_sc1 <= multm_reduce_vs1;
      multm_reduce_sc2 <= multm_reduce_vs2;
      multm_reduce_sc3 <= multm_reduce_vs3;
      multm_reduce_sc4 <= multm_reduce_vs4;
      multm_reduce_sc5 <= multm_reduce_vs5;
      multm_reduce_sd0 <= multm_reduce_vt;
      multm_reduce_sd1 <= multm_reduce_vc0;
      multm_reduce_sd2 <= multm_reduce_vc1;
      multm_reduce_sd3 <= multm_reduce_vc2;
      multm_reduce_sd4 <= multm_reduce_vc3;
      multm_reduce_sd5 <= multm_reduce_vc4;
      multm_reduce_sd6 <= multm_reduce_vc5;
      pipe0_x1 <= sa;
      pipe0_x2 <= pipe0_x1;
      pipe0_x3 <= pipe0_x2;
      pipe1_x1 <= sb;
      pipe1_x2 <= pipe1_x1;
      pipe1_x3 <= pipe1_x2;
      sa <= sar;
      sad <= pipe0_x3;
      sadd <= sad;
      sb <= sbr;
      sbd <= pipe1_x3;
      sbdd <= sbd;
      yc0_o <= pcr0;
      yc1_o <= pcr1;
      yc2_o <= pcr2;
      yc3_o <= pcr3;
      yc4_o <= pcr4;
      yc5_o <= pcr5;
      yc6_o <= pcr6;
      ys0_o <= psr0;
      ys1_o <= psr1;
      ys2_o <= psr2;
      ys3_o <= psr3;
      ys4_o <= psr4;
      ys5_o <= psr5;
      ys6_o <= psr6;
    end

endmodule  // double_exp_91

/*----------------------------------------------------------------------------+
| Primary inputs: 15                                                          |
| Primary outputs: 15                                                         |
| Registers: 135                                                              |
| Gates: 485                                                                  |
| Fan-in: 25%=1 50%=4 75%=6 90%=8 95%=9 99%=9 max=9 (multm_qcp5)              |
| Fan-in cone: 25%=0 50%=4 75%=9 90%=13 95%=17 99%=20                         |
|   max=20 (multm_reduce_mulsc_mulb_cp5)                                      |
| Fan-out: 25%=2 50%=3 75%=5 90%=8 95%=14 99%=16 max=35 (sadd)                |
| Duplication: 25%=1 50%=1 75%=1 90%=2 95%=3 99%=5 max=8 (sadd)               |
| Fan-out load: 25%=2 50%=3 75%=5 90%=6 95%=7 99%=8 max=8 (multm_reduce_sa5)  |
+----------------------------------------------------------------------------*/

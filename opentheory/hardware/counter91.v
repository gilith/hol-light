/*----------------------------------------------------------------------------+
| module counter91 satisfies the following property:                          |
|                                                                             |
| !t k.                                                                       |
|     (!i. i <= k ==> (signal ld (t + i) <=> i = 0))                          |
|     ==> (signal dn (t + k) <=> 91 < k)                                      |
+----------------------------------------------------------------------------*/

module counter91(clk,ld,dn);
  input clk;
  input ld;

  output dn;

  reg counter_cp0;
  reg counter_cp1;
  reg counter_cp2;
  reg counter_cp3;
  reg counter_cp4;
  reg counter_cp5;
  reg counter_cp6;
  reg counter_dp;
  reg counter_sp0;
  reg counter_sp1;
  reg counter_sp2;
  reg counter_sp3;
  reg counter_sp4;
  reg counter_sp5;

  wire counter_cq0;
  wire counter_cq1;
  wire counter_cq2;
  wire counter_cq3;
  wire counter_cq4;
  wire counter_cq5;
  wire counter_cq6;
  wire counter_cr0;
  wire counter_cr1;
  wire counter_cr2;
  wire counter_cr3;
  wire counter_cr4;
  wire counter_cr5;
  wire counter_cr6;
  wire counter_dq;
  wire counter_sq0;
  wire counter_sq1;
  wire counter_sq2;
  wire counter_sq3;
  wire counter_sq4;
  wire counter_sq5;
  wire counter_sr0;
  wire counter_sr1;
  wire counter_sr2;
  wire counter_sr3;
  wire counter_sr4;
  wire counter_sr5;
  wire counter_xn;
  wire dn_o;

  assign counter_cq0 = ~counter_cp0;
  assign counter_cq1 = counter_sp0 & counter_cp0;
  assign counter_cq2 = counter_sp1 & counter_cp1;
  assign counter_cq3 = counter_sp2 & counter_cp2;
  assign counter_cq4 = counter_sp3 & counter_cp3;
  assign counter_cq5 = counter_sp4 & counter_cp4;
  assign counter_cq6 = counter_sp5 & counter_cp5;
  assign counter_cr0 = counter_xn & counter_cq0;
  assign counter_cr1 = counter_xn & counter_cq1;
  assign counter_cr2 = counter_xn & counter_cq2;
  assign counter_cr3 = counter_xn & counter_cq3;
  assign counter_cr4 = counter_xn & counter_cq4;
  assign counter_cr5 = counter_xn & counter_cq5;
  assign counter_cr6 = counter_xn & counter_cq6;
  assign counter_dq = counter_dp | counter_cp6;
  assign counter_sq0 = counter_sp0 ^ counter_cp0;
  assign counter_sq1 = counter_sp1 ^ counter_cp1;
  assign counter_sq2 = counter_sp2 ^ counter_cp2;
  assign counter_sq3 = counter_sp3 ^ counter_cp3;
  assign counter_sq4 = counter_sp4 ^ counter_cp4;
  assign counter_sq5 = counter_sp5 ^ counter_cp5;
  assign counter_sr0 = ld | counter_sq0;
  assign counter_sr1 = counter_xn & counter_sq1;
  assign counter_sr2 = ld | counter_sq2;
  assign counter_sr3 = counter_xn & counter_sq3;
  assign counter_sr4 = ld | counter_sq4;
  assign counter_sr5 = counter_xn & counter_sq5;
  assign counter_xn = ~ld;
  assign dn_o = counter_xn & counter_dq;
  assign dn = dn_o;

  always @(posedge clk)
    begin
      counter_cp0 <= counter_cr0;
      counter_cp1 <= counter_cr1;
      counter_cp2 <= counter_cr2;
      counter_cp3 <= counter_cr3;
      counter_cp4 <= counter_cr4;
      counter_cp5 <= counter_cr5;
      counter_cp6 <= counter_cr6;
      counter_dp <= dn_o;
      counter_sp0 <= counter_sr0;
      counter_sp1 <= counter_sr1;
      counter_sp2 <= counter_sr2;
      counter_sp3 <= counter_sr3;
      counter_sp4 <= counter_sr4;
      counter_sp5 <= counter_sr5;
    end

endmodule // counter91

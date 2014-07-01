/*----------------------------------------------------------------------------+
| module counter_91 satisfies the following property:                         |
|                                                                             |
| !t k.                                                                       |
|     (!i. i <= k ==> (signal ld (t + i) <=> i = 0))                          |
|     ==> (signal dn (t + k) <=> 91 < k)                                      |
|                                                                             |
| Copyright (c) 2014 Joe Leslie-Hurd, distributed under the MIT license       |
+----------------------------------------------------------------------------*/

module counter_91(clk,ld,dn);
  input clk;
  input ld;

  output dn;

  reg ctr_cp0;  // 2:3|3/1=3
  reg ctr_cp1;  // 3:3|2/1=2
  reg ctr_cp2;  // 3:3|2/1=2
  reg ctr_cp3;  // 3:3|2/1=2
  reg ctr_cp4;  // 3:3|2/1=2
  reg ctr_cp5;  // 3:3|2/1=2
  reg ctr_cp6;  // 3:3|2/1=2
  reg ctr_dp;  // 3:3|2/1=2
  reg ctr_sp0;  // 3:2|2/1=2
  reg ctr_sp1;  // 3:3|2/1=2
  reg ctr_sp2;  // 3:2|2/1=2
  reg ctr_sp3;  // 3:3|2/1=2
  reg ctr_sp4;  // 3:2|2/1=2
  reg ctr_sp5;  // 3:3|2/1=2

  wire ctr_cq0;
  wire ctr_cq1;
  wire ctr_cq2;
  wire ctr_cq3;
  wire ctr_cq4;
  wire ctr_cq5;
  wire ctr_cq6;
  wire ctr_cr0;
  wire ctr_cr1;
  wire ctr_cr2;
  wire ctr_cr3;
  wire ctr_cr4;
  wire ctr_cr5;
  wire ctr_cr6;
  wire ctr_dq;
  wire ctr_sq0;
  wire ctr_sq1;
  wire ctr_sq2;
  wire ctr_sq3;
  wire ctr_sq4;
  wire ctr_sq5;
  wire ctr_sr0;
  wire ctr_sr1;
  wire ctr_sr2;
  wire ctr_sr3;
  wire ctr_sr4;
  wire ctr_sr5;
  wire dn_o;
  wire xn;

  assign ctr_cq0 = ~ctr_cp0;
  assign ctr_cq1 = ctr_sp0 & ctr_cp0;
  assign ctr_cq2 = ctr_sp1 & ctr_cp1;
  assign ctr_cq3 = ctr_sp2 & ctr_cp2;
  assign ctr_cq4 = ctr_sp3 & ctr_cp3;
  assign ctr_cq5 = ctr_sp4 & ctr_cp4;
  assign ctr_cq6 = ctr_sp5 & ctr_cp5;
  assign ctr_cr0 = xn & ctr_cq0;
  assign ctr_cr1 = xn & ctr_cq1;
  assign ctr_cr2 = xn & ctr_cq2;
  assign ctr_cr3 = xn & ctr_cq3;
  assign ctr_cr4 = xn & ctr_cq4;
  assign ctr_cr5 = xn & ctr_cq5;
  assign ctr_cr6 = xn & ctr_cq6;
  assign ctr_dq = ctr_dp | ctr_cp6;
  assign ctr_sq0 = ctr_sp0 ^ ctr_cp0;
  assign ctr_sq1 = ctr_sp1 ^ ctr_cp1;
  assign ctr_sq2 = ctr_sp2 ^ ctr_cp2;
  assign ctr_sq3 = ctr_sp3 ^ ctr_cp3;
  assign ctr_sq4 = ctr_sp4 ^ ctr_cp4;
  assign ctr_sq5 = ctr_sp5 ^ ctr_cp5;
  assign ctr_sr0 = ld | ctr_sq0;
  assign ctr_sr1 = xn & ctr_sq1;
  assign ctr_sr2 = ld | ctr_sq2;
  assign ctr_sr3 = xn & ctr_sq3;
  assign ctr_sr4 = ld | ctr_sq4;
  assign ctr_sr5 = xn & ctr_sq5;
  assign dn_o = xn & ctr_dq;
  assign xn = ~ld;
  assign dn = dn_o;

  always @(posedge clk)
    begin
      ctr_cp0 <= ctr_cr0;
      ctr_cp1 <= ctr_cr1;
      ctr_cp2 <= ctr_cr2;
      ctr_cp3 <= ctr_cr3;
      ctr_cp4 <= ctr_cr4;
      ctr_cp5 <= ctr_cr5;
      ctr_cp6 <= ctr_cr6;
      ctr_dp <= dn_o;
      ctr_sp0 <= ctr_sr0;
      ctr_sp1 <= ctr_sr1;
      ctr_sp2 <= ctr_sr2;
      ctr_sp3 <= ctr_sr3;
      ctr_sp4 <= ctr_sr4;
      ctr_sp5 <= ctr_sr5;
    end

endmodule  // counter_91

/*----------------------------------------------------------------------------+
| Primary inputs: 1                                                           |
| Primary outputs: 1                                                          |
| Registers: 14                                                               |
| Gates: 29                                                                   |
| Fan-in: 25%=3 50%=3 75%=3 90%=3 95%=3 99%=3 max=3 (ctr_cp4)                 |
| Fan-in cone: 25%=3 50%=3 75%=3 90%=3 95%=3 99%=3 max=3 (ctr_cp4)            |
| Fan-out: 25%=2 50%=2 75%=2 90%=2 95%=3 99%=3 max=15 (ld)                    |
| Duplication: 25%=1 50%=1 75%=1 90%=1 95%=1 99%=1 max=1 (ctr_sp0)            |
| Fan-out load: 25%=2 50%=2 75%=2 90%=2 95%=3 99%=3 max=15 (ld)               |
+----------------------------------------------------------------------------*/

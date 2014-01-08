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

  reg r0;
  reg r1;
  reg r2;
  reg r3;
  reg r4;
  reg r5;
  reg r6;
  reg r7;
  reg r8;
  reg r9;
  reg r10;
  reg r11;
  reg r12;
  reg r13;

  wire w0;
  wire w1;
  wire w2;
  wire w3;
  wire w4;
  wire w5;
  wire w6;
  wire w7;
  wire w8;
  wire w9;
  wire w10;
  wire w11;
  wire w12;
  wire w13;
  wire w14;
  wire w15;
  wire w16;
  wire w17;
  wire w18;
  wire w19;
  wire w20;
  wire w21;
  wire w22;
  wire w23;
  wire w24;
  wire w25;
  wire w26;
  wire w27;
  wire w28;

  assign w0 = r1 ^ r0;
  assign w1 = r3 ^ r2;
  assign w2 = r5 ^ r4;
  assign w3 = r7 ^ r6;
  assign w4 = r9 ^ r8;
  assign w5 = r11 ^ r10;
  assign w6 = ld | w1;
  assign w7 = ld | w3;
  assign w8 = ld | w5;
  assign w9 = r13 | r12;
  assign w10 = w12 & w11;
  assign w11 = r1 & r0;
  assign w12 = ~ld;
  assign w13 = w12 & w14;
  assign w14 = r3 & r2;
  assign w15 = w12 & w16;
  assign w16 = r5 & r4;
  assign w17 = w12 & w18;
  assign w18 = r7 & r6;
  assign w19 = w12 & w20;
  assign w20 = r9 & r8;
  assign w21 = w12 & w22;
  assign w22 = r11 & r10;
  assign w23 = w12 & w24;
  assign w24 = ~r10;
  assign w25 = w12 & w0;
  assign w26 = w12 & w2;
  assign w27 = w12 & w4;
  assign w28 = w12 & w9;
  assign dn = w28;

  always @(posedge clk)
    begin
      r0 <= w13;
      r1 <= w25;
      r2 <= w15;
      r3 <= w6;
      r4 <= w17;
      r5 <= w26;
      r6 <= w19;
      r7 <= w7;
      r8 <= w21;
      r9 <= w27;
      r10 <= w23;
      r11 <= w8;
      r12 <= w10;
      r13 <= w28;
    end

endmodule // counter91

`include "double_exp_221_1000.v"

module main;
  reg [0:7] xs;
  reg [0:7] xc;
  reg [0:7] ys;
  reg [0:7] yc;

  reg clk;
  reg ld;
  reg [0:7] ps;
  reg [0:7] pc;
  wire dn;
  wire [0:7] qs;
  wire [0:7] qc;

  integer seed;

  double_exp_221_1000
    root
    (.clk (clk),
     .ld (ld),
     .xs (ps),
     .xc (pc),
     .dn (dn),
     .ys (qs),
     .yc (qc));

  initial
    begin
      seed = `SEED;
      xs = $random(seed);
      xc = $random(seed);
      $display("+-----------------------------+");
      $display("| Testing double_exp_221_1000 |");
      $display("+-----------------------------+");
      $display("Random seed = %0d", seed);
      $display("");
      clk = 1'b0;
      @(posedge clk);
      // Time 0
      ld = 1'b1;
      repeat(8) @(posedge clk);
      // Time 8
      ld = 1'b0;
      repeat(6) @(posedge clk);
      // Time 14
      ps = xs;
      pc = xc;
      @(posedge clk);
      // Time 15
      ps = 7'bx;
      pc = 7'bx;
      @(posedge dn);
      #1 ys = qs; yc = qc;
      $display("Inputs: xs = %0d, xc = %0d", xs, xc);
      $display("Outputs: ys = %0d, yc = %0d", ys, yc);
      $display("");
      $display("Test complete at time %0t.", $time);
      $finish;
    end

  always
    #5 clk = ~clk;

endmodule // main

`include "double_exp_91.v"

module main;
   reg [0:7] t;
   reg clk;
   reg ld;
   reg [0:6] xs;
   reg [0:6] xc;
   wire sa;
   wire sb;
   wire [6:0] ps;
   wire [6:0] pc;
   wire dn;
   wire [0:6] ys;
   wire [0:6] yc;

   integer x;
   integer y;
   integer spec;
   integer ckt;
   integer seed;

   double_exp_91
     root
     (.clk (clk),
      .ld (ld),
      .xs (xs),
      .xc (xc),
      .dn (dn),
      .ys (ys),
      .yc (yc));

   assign sa = root.pipe0_x0;
   assign sb = root.pipe1_x0;
   assign ps[0] = root.qs0;
   assign ps[1] = root.qs1;
   assign ps[2] = root.qs2;
   assign ps[3] = root.qs3;
   assign ps[4] = root.qs4;
   assign ps[5] = root.qs5;
   assign ps[6] = root.qs6;
   assign pc[0] = root.qc0;
   assign pc[1] = root.qc1;
   assign pc[2] = root.qc2;
   assign pc[3] = root.qc3;
   assign pc[4] = root.qc4;
   assign pc[5] = root.qc5;
   assign pc[6] = root.qc6;

   initial
     begin
        seed = `SEED;
        $display("+--------------------------------------+");
        $display("| Test bench for double_exp_91 circuit |");
        $display("+--------------------------------------+");
        $display("random seed = %0d", seed);
        $display("");
        $display("+-----+----+-----+-----+-------+-----+-----+----+-----+-----+");
        $display("|   t | ld |  xs |  xc | state |  qs |  qc | dn |  ys |  yc |");
        $display("+-----+----+-----+-----+-------+-----+-----+----+-----+-----+");
        $monitor("| %d |  %b | %d | %d | (%b,%b) | %d | %d |  %b | %d | %d |",
                  t, ld, xs, xc, sb, sa, ps, pc, dn, ys, yc);
        clk = 1'b0;
        repeat(10) @(posedge clk);
        @(posedge clk);
        // Time 0
        t = 8'h00;
        ld = 1'b1;
        repeat(10) @(posedge clk);
        // Time ??
        ld = 1'b0;
        xs = $random(seed);
        xc = $random(seed);
        x = xs + 2 * xc;
        repeat(10) @(posedge clk);
        // Time ??
        xs = 7'bx;
        xc = 7'bx;
        @(posedge dn);
        // Time ??
        #1 y = ys + 2 * yc;
        repeat(3) @(posedge clk);
        $monitoroff;
        @(posedge clk);
        spec = x % 91;
        repeat(11) spec = (spec * spec) % 91;
        spec = (spec * 8) % 91;
        ckt = y % 91;
        $display("+-----+----+-----+-----+-------+-----+-----+----+-----+-----+");
        $display("");
        $display("Inputs: x = %0d", x);
        $display("Outputs: y = %0d", y);
        $display("Spec: (x^2^11 * 8) %% 91 = %0d", spec);
        $display("Circuit: y %% 91         = %0d", ckt);
        if (ckt == spec)
          begin
             $display("TEST PASSED: Circuit computed the correct result");
          end
        else
          begin
             $display("TEST FAILED: Circuit computed an incorrect result");
          end
        $display("");
        $display("Test complete at time %0t.", $time);
        $finish;
     end

   always
     #5 clk = ~clk;

   always @(posedge clk)
     t = t + 1;

endmodule // main

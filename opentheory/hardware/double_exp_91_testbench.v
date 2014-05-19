`include "double_exp_91.v"

module main;
   reg [0:7] t;
   reg clk;
   reg ld;
   reg [0:6] xs;
   reg [0:6] xc;
   wire sa;
   wire sb;
   wire jp;
   wire [6:0] qs;
   wire [6:0] qc;
   wire dn;
   wire [0:6] ys;
   wire [0:6] yc;

   reg too_early;
   reg on_time;
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

   assign sa = root.sa;
   assign sb = root.sb;
   assign jp = root.jp;
   assign qs[0] = root.qs0;
   assign qs[1] = root.qs1;
   assign qs[2] = root.qs2;
   assign qs[3] = root.qs3;
   assign qs[4] = root.qs4;
   assign qs[5] = root.qs5;
   assign qs[6] = root.qs6;
   assign qc[0] = root.qc0;
   assign qc[1] = root.qc1;
   assign qc[2] = root.qc2;
   assign qc[3] = root.qc3;
   assign qc[4] = root.qc4;
   assign qc[5] = root.qc5;
   assign qc[6] = root.qc6;

   initial
     begin
        seed = `SEED;
        $display("+-----------------------+");
        $display("| Testing double_exp_91 |");
        $display("+-----------------------+");
        $display("random seed = %0d", seed);
        $display("");
        $display("+-----+----+-----+-----+-------+----+-----+-----+----+-----+-----+");
        $display("|   t | ld |  xs |  xc | state | jp |  qs |  qc | dn |  ys |  yc |");
        $display("+-----+----+-----+-----+-------+----+-----+-----+----+-----+-----+");
        $monitor("| %d |  %b | %d | %d | (%b,%b) |  %b | %d | %d |  %b | %d | %d |",
                  t, ld, xs, xc, sb, sa, jp, qs, qc, dn, ys, yc);
        clk = 1'b0;
        repeat(10) @(posedge clk);
        @(posedge clk);
        // Time 0
        t = 8'h00;
        ld = 1'b1;
        repeat(6) @(posedge clk);
        // Time 6
        ld = 1'b0;
        repeat(4) @(posedge clk);
        // Time 10
        xs = $random(seed);
        xc = $random(seed);
        x = xs + 2 * xc;
        @(posedge clk);
        // Time 11
        xs = 7'bx;
        xc = 7'bx;
        repeat(205) @(posedge clk);
        // Time 216
        ld = 1'bx;
        repeat(3) @(posedge clk);
        // Time 219
        #1 too_early = dn;
        @(posedge clk);
        // Time 220
        #1 on_time = dn; y = ys + 2 * yc;
        repeat(3) @(posedge clk);
        $monitoroff;
        @(posedge clk);
        spec = (x * 8) % 91;
        repeat(11) spec = (spec * spec) % 91;
        ckt = (y * 8) % 91;
        $display("+-----+----+-----+-----+-------+----+-----+-----+----+-----+-----+");
        $display("");
        $display("Inputs: x = %0d", x);
        $display("Outputs: y = %0d", y);
        $display("Spec: ((x * 8) ^ 2 ^ 11) %% 91 = %0d", spec);
        $display("Circuit: (y * 8) %% 91         = %0d", ckt);
        if (on_time)
          begin
             if (!too_early)
               begin
                  if (ckt == spec)
                    begin
                       $display("TEST PASSED: Circuit computed the correct result");
                    end
                  else
                    begin
                       $display("TEST FAILED: Circuit computed an incorrect result");
                    end
               end
             else
               begin
                  $display("TEST FAILED: dn asserted too early");
               end
          end
        else
          begin
             $display("TEST FAILED: dn not asserted on time");
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

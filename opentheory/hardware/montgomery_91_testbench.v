`include "montgomery_91.v"

module main;
   reg [0:7] t;
   reg clk;
   reg ld;
   reg [0:6] xs;
   reg [0:6] xc;
   reg [0:6] ys;
   reg [0:6] yc;
   wire [0:6] zs;
   wire [0:6] zc;

   integer x;
   integer y;
   integer z;
   integer spec;
   integer ckt;
   integer seed;

   montgomery_91
     root
     (.clk (clk),
      .ld (ld),
      .xs (xs),
      .xc (xc),
      .ys (ys),
      .yc (yc),
      .zs (zs),
      .zc (zc));

   initial
     begin
        seed = `SEED;
        $display("+--------------------------------------+");
        $display("| Test bench for montgomery_91 circuit |");
        $display("+--------------------------------------+");
        $display("random seed = %0d", seed);
        $display("");
        $display("+----+----+-----+-----+-----+-----+-----+-----+");
        $display("|  t | ld |  xs |  xc |  ys |  yc |  zs |  zc |");
        $display("+----+----+-----+-----+-----+-----+-----+-----+");
        $monitor("|%d |  %b | %d | %d | %d | %d | %d | %d | ",
                  t, ld, xs, xc, ys, yc, zs, zc);
        clk = 1'b0;
        repeat(10) @(posedge clk);
        @(posedge clk);
        // Time 0
        t = 8'h00;
        ld = 1'b1;
        xs = $random(seed);
        xc = $random(seed);
        x = xs + 2 * xc;
        @(posedge clk);
        // Time 1
        ld = 1'b0;
        xs = 7'bx;
        xc = 7'bx;
        @(posedge clk);
        // Time 2
        ys = $random(seed);
        yc = $random(seed);
        y = ys + 2 * yc;
        repeat(9) @(posedge clk);
        // Time 11
        ys = 7'bx;
        yc = 7'bx;
        repeat(7) @(posedge clk);
        // Time 18
        ld = 1'bx;
        #1 z = zs + 2 * zc;
        repeat(3) @(posedge clk);
        $monitoroff;
        @(posedge clk);
        spec = (x * y * 8) % 91;
        ckt = z % 91;
        $display("+----+----+-----+-----+-----+-----+-----+-----+");
        $display("");
        $display("Inputs: x = %0d, y = %0d", x, y);
        $display("Outputs: z = %0d", z);
        $display("Spec: (x * y * 8) %% 91 = %0d", spec);
        $display("Circuit: z %% 91        = %0d", ckt);
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

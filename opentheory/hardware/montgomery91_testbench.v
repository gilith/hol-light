`include "montgomery91.v"

module main;
   reg [0:7] t;
   reg clk;
   reg ld;
   reg [0:6] xs;
   reg [0:6] xc;
   reg [0:6] ys;
   reg [0:6] yc;
   wire [0:7] zs;
   wire [0:7] zc;

   montgomery91
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
        $display("+-----------------------------+");
        $display("| Test bench for montgomery91 |");
        $display("+-----------------------------+");
        $display("");
        $display("  t | ld |  xs |  xc |  ys |  yc |  zs |  zc |");
        $display("----+----+-----+-----+-----+-----+-----+-----+");
        $monitor("%d |  %b | %d | %d | %d | %d | %d | %d | %b",
                  t, ld, xs, xc, ys, yc, zs, zc, root.w318);
        clk = 1'b0;
        repeat(10) @(posedge clk);
        // Time 0
        t = 8'd255;
        ld = 1'b1;
        xs = 7'd111;
        xc = 7'd73;
        //$display("x = %d", xs + 2 * xc);
        @(posedge clk);
        // Time 1
        ld = 1'b0;
        //xs = 7'bx;
        //xc = 7'bx;
        @(posedge clk);
        // Time 2
        ys = 7'd111;
        yc = 7'd73;
        //$display("y = %d", ys + 2 * yc);
        repeat(9) @(posedge clk);
        // Time 11
        //ys = 7'bx;
        //yc = 7'bx;
        repeat(2) @(posedge clk);
        // Time 13
        //ld = 1'bx;
        repeat(2) @(posedge clk);
        // Time 15
        //$display("z = %d", zs + 2 * zc);
        if (0)
          begin
             $display("ERROR: montomgery91 finished too soon");
          end
        repeat(5) @(posedge clk);
        $monitoroff;
        $display("Test complete at time %0t.", $time);
        $finish;
     end

   always
     #5 clk = !clk;

   always @(posedge clk)
     t = t + 1;

endmodule // main

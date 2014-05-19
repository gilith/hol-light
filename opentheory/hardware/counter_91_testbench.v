`include "counter_91.v"

module main;
   reg clk;
   reg rst;
   wire out;

   counter_91
     root
     (.clk (clk),
      .ld (rst),
      .dn (out));

   initial
     begin
        $display("+--------------------+");
        $display("| Testing counter_91 |");
        $display("+--------------------+");
        $monitor("ld = %b, dn = %b",
                  root.ld, root.dn);
        clk = 0;
        repeat(10) @(posedge clk);
        rst = 1;
        @(posedge clk);
        rst = 0;
        repeat(91) @(posedge clk);
        if (out)
          begin
             $display("ERROR: counter_91 finished too soon");
          end
        @(posedge clk);
        if (!out)
          begin
             $display("ERROR: counter_91 did not finish on time");
          end
        repeat(5) @(posedge clk);
        $monitoroff;
        $display("Test complete at time %0t.", $time);
        $finish;
     end

   always
     #5 clk = !clk;

endmodule // main

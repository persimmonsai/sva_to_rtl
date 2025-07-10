module multi_delay_checker_rtl_tb;

    // Clock and reset
    logic clk = 0;
    logic rst = 1;

    // Input signals
    logic a = 0;
    logic b = 0;

    // Output signals
    logic assertion_pass;
    logic assertion_fail;
    logic assertion_active;

    // DUT instantiation
    multi_delay_checker_rtl dut (
        .clk(clk),
        .rst(rst),
        .a(a),
        .b(b),
        .assertion_pass(assertion_pass),
        .assertion_fail(assertion_fail),
        .assertion_active(assertion_active)
    );

    // Clock generation
    always #5 clk = ~clk;

    // Test stimulus
    initial begin
        $dumpfile("waves.vcd");
        $dumpvars(0, dut);

        // Reset
        rst = 1;
        #20;
        rst = 0;
        #10;

        // Add test cases here
        #100;

        $finish;
    end

    // Monitoring
    always @(posedge clk) begin
        if (assertion_pass)
            $display("Time %t: Assertion PASSED", $time);
        if (assertion_fail)
            $display("Time %t: Assertion FAILED", $time);
    end

endmodule
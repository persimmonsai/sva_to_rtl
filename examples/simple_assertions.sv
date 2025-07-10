// Simple SVA examples for testing
module simple_assertions;

    logic clk, rst_n;
    logic a, b, c;
    
    // Basic implication
    basic_assert: assert property (@(posedge clk) a |-> b);
    
    // Delayed implication
    delay_assert: assert property (@(posedge clk) a |-> ##1 b);
    
    // Multiple delay
    multi_delay: assert property (@(posedge clk) a |-> ##3 b);
    
    // Cover property
    cover_example: cover property (@(posedge clk) a && b);
    
    // Assumption
    assume_example: assume property (@(posedge clk) a |-> ##1 b);

endmodule

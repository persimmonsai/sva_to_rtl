// Complex SVA examples for demonstrating advanced features
module complex_assertions (
    input logic clk,
    input logic rst_n,
    input logic start,
    input logic done,
    input logic [7:0] data_in,
    input logic [7:0] data_out,
    input logic valid_in,
    input logic valid_out,
    input logic ready,
    input logic error
);

    // Multi-step protocol assertion
    protocol_check: assert property (@(posedge clk) 
        disable iff (!rst_n) 
        start |-> ##1 valid_in |-> ##[1:3] valid_out);
    
    // Data integrity check
    data_integrity: assert property (@(posedge clk) 
        (valid_in && (data_in == 8'hAB)) |-> 
        ##3 (valid_out && (data_out == 8'hAB)));
    
    // Error condition coverage
    error_coverage: cover property (@(posedge clk) error && ready);
    
    // Assumption about input behavior
    input_assumption: assume property (@(posedge clk) 
        start |-> ##1 !start);
    
    // Complex conditional assertion
    conditional_check: assert property (@(posedge clk) 
        (start && ready) |-> ##2 (done || error));

endmodule

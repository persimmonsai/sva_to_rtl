// Example SystemVerilog file with SVA assertions
// This file demonstrates various SVA constructs that can be translated to RTL

module example_design (
    input logic clk,
    input logic rst_n,
    input logic req,
    input logic ack,
    input logic [7:0] data,
    input logic valid,
    input logic ready,
    output logic [7:0] out_data,
    output logic out_valid
);

    // Simple immediate assertion
    req_ack_check: assert property (@(posedge clk) req |-> ##1 ack);
    
    // Assertion with delay
    data_valid_check: assert property (@(posedge clk) valid |-> ##2 ready);
    
    // Sequence with throughout
    // req_throughout: assert property (@(posedge clk) req throughout (##1 data[0] ##1 data[1]));
    
    // Assertion with disable condition
    reset_check: assert property (@(posedge clk) disable iff (!rst_n) 
                                 valid |-> ##1 out_valid);
    
    // Cover property
    handshake_cover: cover property (@(posedge clk) req && ack);
    
    // Assumption
    input_assumption: assume property (@(posedge clk) req |-> ##[1:3] ack);
    
    // More complex assertion
    data_sequence: assert property (@(posedge clk) 
                                   (valid && data == 8'hAA) |-> ##1 (ready && out_data == 8'hAA));

    // Simple design logic
    always_ff @(posedge clk) begin
        if (!rst_n) begin
            out_data <= 8'h00;
            out_valid <= 1'b0;
        end else begin
            out_data <= data;
            out_valid <= valid;
        end
    end

endmodule

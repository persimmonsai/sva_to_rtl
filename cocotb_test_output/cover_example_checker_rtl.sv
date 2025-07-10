module cover_example_checker_rtl (
    input logic clk,
    input logic a,
    input logic b,
    output logic assertion_pass,
    output logic assertion_fail,
    output logic assertion_active
);

    parameter STATE_BITS = 2;
    parameter IDLE = 2'd0;
    parameter S1 = 2'd1;
    parameter S2 = 2'd2;

    logic [STATE_BITS-1:0] current_state, next_state;

    // State register
    always_ff @(posedge clk) begin
        else begin
            current_state <= next_state;
        end
    end
    
    // Next state logic
    always_comb begin
        next_state = current_state;
    
        case (current_state)
            IDLE: begin
                if (a) begin
                    next_state = S1;
                end
            end
    
            S1: begin
                if (b) begin
                    next_state = S2;
                end
            end
    
            S2: begin
            end
    
            default: begin
                next_state = IDLE;
            end
        endcase
    end
    
    // Output logic
    always_comb begin
        assertion_pass = 1'b0;
        assertion_fail = 1'b0;
        assertion_active = 1'b0;
    
        case (current_state)
            S1: begin
                assertion_active = 1'b1;
            end
            S2: begin
                assertion_active = 1'b1;
            end
            IDLE: begin
            end
            default: begin
                // Default outputs
            end
        endcase
    end
    

endmodule
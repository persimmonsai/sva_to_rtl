module multi_delay_checker_rtl (
    input logic clk,
    input logic a,
    input logic b,
    output logic assertion_pass,
    output logic assertion_fail,
    output logic assertion_active
);

    parameter STATE_BITS = 3;
    parameter FAILURE = 3'd0;
    parameter IDLE = 3'd1;
    parameter S1 = 3'd2;
    parameter S2 = 3'd3;
    parameter SUCCESS = 3'd4;

    logic [STATE_BITS-1:0] current_state, next_state;
    logic cond_not_##;

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
            FAILURE: begin
            end
    
            IDLE: begin
                if (a) begin
                    next_state = S1;
                end
            end
    
            S1: begin
                if (##) begin
                    next_state = SUCCESS;
                end
                if (cond_not_##) begin
                    next_state = FAILURE;
                end
                if (b) begin
                    next_state = S2;
                end
            end
    
            S2: begin
            end
    
            SUCCESS: begin
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
            SUCCESS: begin
                assertion_pass = 1'b1;
            end
            FAILURE: begin
                assertion_fail = 1'b1;
            end
            default: begin
                // Default outputs
            end
        endcase
    end
    
    // Condition assignments
    assign cond_not_## = cond_not_##;
    

endmodule
# SVA to RTL Translation Tool - Tutorial

This tutorial will guide you through using the SVA to RTL Translation Tool to convert SystemVerilog Assertions into synthesizable RTL state machines.

## Table of Contents

1. [Quick Start](#quick-start)
2. [Basic Usage](#basic-usage)
3. [Advanced Features](#advanced-features)
4. [Understanding Generated RTL](#understanding-generated-rtl)
5. [Examples](#examples)
6. [Troubleshooting](#troubleshooting)

## Quick Start

### Installation

1. Ensure you have Python 3.8 or higher installed
2. Install required packages:
   ```bash
   pip install click pyparsing jinja2
   ```

### Basic Usage

1. **Translate an SVA file to RTL:**
   ```bash
   python -m sva_to_rtl.cli translate examples/simple_assertions.sv
   ```

2. **Generate with testbenches:**
   ```bash
   python -m sva_to_rtl.cli translate examples/simple_assertions.sv -t -o output_dir
   ```

3. **Analyze assertions in a file:**
   ```bash
   python -m sva_to_rtl.cli analyze examples/simple_assertions.sv -v
   ```

## Basic Usage

### Command Line Interface

The tool provides three main commands:

#### 1. `translate` - Convert SVA to RTL

```bash
python -m sva_to_rtl.cli translate <input_file> [options]
```

**Options:**
- `-o, --output-dir`: Output directory (default: output)
- `-t, --generate-testbench`: Generate testbench files
- `--optimize`: Optimize generated state machines
- `-v, --verbose`: Enable verbose output
- `-l, --list-assertions`: List assertions without generating RTL

**Example:**
```bash
python -m sva_to_rtl.cli translate design.sv -o generated_rtl -t -v
```

#### 2. `text` - Translate single assertion

```bash
python -m sva_to_rtl.cli text "assertion_text" [options]
```

**Example:**
```bash
python -m sva_to_rtl.cli text "req_ack: assert property (@(posedge clk) req |-> ##1 ack);" -o output
```

#### 3. `analyze` - Analyze assertions

```bash
python -m sva_to_rtl.cli analyze <input_file> [options]
```

**Example:**
```bash
python -m sva_to_rtl.cli analyze design.sv -v
```

### Python API

```python
from sva_to_rtl.parser import SVAParser
from sva_to_rtl.state_machine import StateMachineGenerator
from sva_to_rtl.rtl_generator import RTLGenerator

# Parse SVA assertions
parser = SVAParser()
assertions = parser.parse_file("design.sv")

# Generate state machines
sm_generator = StateMachineGenerator()
state_machines = sm_generator.generate_multiple(assertions)

# Generate RTL
rtl_generator = RTLGenerator()
rtl_modules = rtl_generator.generate_multiple(state_machines)

# Save RTL files
for name, module in rtl_modules.items():
    rtl_generator.save_module(module, f"{name}.sv")
```

## Advanced Features

### Supported SVA Constructs

#### Basic Assertions
```systemverilog
// Assert property
basic_assert: assert property (@(posedge clk) req |-> ack);

// Assume property
input_assume: assume property (@(posedge clk) start |-> ##1 valid);

// Cover property
scenario_cover: cover property (@(posedge clk) req && ack);
```

#### Temporal Operators
```systemverilog
// Immediate implication
immediate: assert property (@(posedge clk) a |-> b);

// Delayed implication
delayed: assert property (@(posedge clk) a |-> ##1 b);

// Multiple cycle delay
multi_delay: assert property (@(posedge clk) start |-> ##3 done);
```

#### Clock and Reset
```systemverilog
// Posedge clock
posedge_clk: assert property (@(posedge clk) a |-> b);

// Negedge clock
negedge_clk: assert property (@(negedge clk_n) a |-> b);

// With disable condition
with_disable: assert property (@(posedge clk) disable iff (!rst_n) a |-> b);
```

### State Machine Optimization

Enable optimization to reduce state machine complexity:

```bash
python -m sva_to_rtl.cli translate design.sv --optimize
```

This removes unreachable states and simplifies transitions.

## Understanding Generated RTL

### Module Structure

Each generated RTL module has:

1. **Input Ports:**
   - Clock signal
   - Reset signal (if present)
   - Assertion input signals
   - Disable condition signals

2. **Output Ports:**
   - `assertion_pass`: High when assertion succeeds
   - `assertion_fail`: High when assertion fails
   - `assertion_active`: High when assertion is being evaluated

3. **Internal Logic:**
   - State register with clock and reset
   - Next-state combinational logic
   - Output generation logic

### Example Generated RTL

**Input SVA:**
```systemverilog
req_ack: assert property (@(posedge clk) req |-> ##1 ack);
```

**Generated RTL:**
```systemverilog
module req_ack_checker_rtl (
    input logic clk,
    input logic req,
    input logic ack,
    output logic assertion_pass,
    output logic assertion_fail,
    output logic assertion_active
);

    parameter STATE_BITS = 3;
    parameter IDLE = 3'd0;
    parameter WAIT_ACK = 3'd1;
    parameter SUCCESS = 3'd2;
    parameter FAILURE = 3'd3;

    logic [STATE_BITS-1:0] current_state, next_state;

    // State register
    always_ff @(posedge clk) begin
        current_state <= next_state;
    end

    // Next state logic
    always_comb begin
        next_state = current_state;
        
        case (current_state)
            IDLE: begin
                if (req) begin
                    next_state = WAIT_ACK;
                end
            end
            
            WAIT_ACK: begin
                if (ack) begin
                    next_state = SUCCESS;
                end else begin
                    next_state = FAILURE;
                end
            end
            
            SUCCESS, FAILURE: begin
                next_state = IDLE;
            end
        endcase
    end

    // Output logic
    always_comb begin
        assertion_pass = (current_state == SUCCESS);
        assertion_fail = (current_state == FAILURE);
        assertion_active = (current_state == WAIT_ACK);
    end

endmodule
```

## Examples

### Example 1: Simple Handshake Protocol

**SVA Input:**
```systemverilog
handshake: assert property (@(posedge clk) req |-> ##1 ack);
```

**Command:**
```bash
python -m sva_to_rtl.cli text "handshake: assert property (@(posedge clk) req |-> ##1 ack);" -o output -v
```

### Example 2: Data Valid Check

**SVA Input:**
```systemverilog
data_check: assert property (@(posedge clk) valid |-> ##2 ready);
```

**Command:**
```bash
python -m sva_to_rtl.cli text "data_check: assert property (@(posedge clk) valid |-> ##2 ready);" -o output -t
```

### Example 3: Multiple Assertions

**SVA File (protocol.sv):**
```systemverilog
module protocol_checker;
    req_ack: assert property (@(posedge clk) req |-> ##1 ack);
    data_valid: assert property (@(posedge clk) valid |-> ##2 ready);
    error_check: cover property (@(posedge clk) error);
endmodule
```

**Command:**
```bash
python -m sva_to_rtl.cli translate protocol.sv -o rtl_output -t -v --optimize
```

## Troubleshooting

### Common Issues

1. **Parse Errors:**
   - Check SVA syntax matches supported constructs
   - Ensure proper parentheses and semicolons
   - Verify clock expressions are correct

2. **Import Errors:**
   - Ensure all required packages are installed
   - Check Python path is set correctly

3. **Generation Errors:**
   - Verify assertions were parsed correctly
   - Check for complex expressions that may not be supported

### Debug Mode

Use verbose output to debug issues:

```bash
python -m sva_to_rtl.cli translate design.sv -v
```

This shows:
- Parsed assertions
- Generated state machines
- RTL generation steps
- Any warnings or errors

### Getting Help

Use the `--help` flag for command information:

```bash
python -m sva_to_rtl.cli --help
python -m sva_to_rtl.cli translate --help
```

## Best Practices

1. **Start Simple:** Begin with basic assertions and gradually add complexity
2. **Use Verbose Mode:** Enable verbose output to understand the translation process
3. **Generate Testbenches:** Use the `-t` flag to create testbenches for verification
4. **Optimize:** Use the `--optimize` flag for cleaner state machines
5. **Review Output:** Always review generated RTL for correctness

## Limitations

- Complex SVA constructs may not be fully supported
- Generated RTL may not be optimal for all cases
- Parser handles a subset of SystemVerilog syntax
- Error handling could be improved for edge cases

## Next Steps

1. Try the examples in the `examples/` directory
2. Experiment with your own SVA assertions
3. Use the generated RTL in your verification environment
4. Contribute improvements to the tool

For more information, see the README.md file and source code documentation.

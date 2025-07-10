# SVA to RTL Translation Tool

A Python tool for translating SystemVerilog Assertions (SVA) into synthesizable SystemVerilog RTL state machines that implement assertion checks at simulation time.

## Features

- **SVA Parser**: Parses SystemVerilog assertion syntax including:
  - Assert, assume, and cover properties
  - Immediate and temporal assertions
  - Clock and reset specifications
  - Disable conditions
  - Sequence and property definitions

- **State Machine Generator**: Converts SVA logic into finite state machines:
  - Handles implication operators (`|->`, `|=>`)
  - Supports delay operators (`##n`)
  - Manages sequential logic
  - Optimizes state machines by removing unreachable states

- **RTL Generator**: Produces synthesizable SystemVerilog code:
  - Generates complete RTL modules with ports and parameters
  - Creates state registers and combinational logic
  - Includes assertion status outputs (pass/fail/active)
  - Produces testbenches for verification

- **Command Line Interface**: Easy-to-use CLI with multiple modes:
  - File-based translation
  - Text-based translation
  - Analysis mode for assertion inspection

## Installation

### Prerequisites

- Python 3.8 or higher
- Required Python packages (see requirements.txt)

### Install from Source

```bash
git clone <repository-url>
cd sva_to_rtl
pip install -r requirements.txt
pip install -e .
```

### Install Required Packages

```bash
pip install click pyparsing jinja2
```

## Usage

### Command Line Interface

The tool provides several commands:

#### 1. Translate SVA File to RTL

```bash
python -m sva_to_rtl.cli translate input_file.sv
```

Options:
- `--output-dir, -o`: Output directory for generated files (default: output)
- `--generate-testbench, -t`: Generate testbench files
- `--optimize`: Optimize generated state machines
- `--verbose, -v`: Enable verbose output
- `--list-assertions, -l`: List found assertions without generating RTL

Example:
```bash
python -m sva_to_rtl.cli translate examples/example_design.sv -o generated_rtl -t -v
```

#### 2. Translate Single Assertion Text

```bash
python -m sva_to_rtl.cli text "assert property (@(posedge clk) req |-> ##1 ack);"
```

#### 3. Analyze SVA File

```bash
python -m sva_to_rtl.cli analyze input_file.sv -v
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

## Supported SVA Constructs

### Currently Supported

- **Assert Properties**: `assert property (...)`
- **Assume Properties**: `assume property (...)`
- **Cover Properties**: `cover property (...)`
- **Implication Operators**: `|->` (overlapping), `|=>` (non-overlapping)
- **Delay Operators**: `##n` (fixed delay)
- **Clock Expressions**: `@(posedge clk)`, `@(negedge clk)`
- **Disable Conditions**: `disable iff (...)`
- **Basic Boolean Expressions**: `&&`, `||`, `!`

### Planned for Future Versions

- **Repetition Operators**: `[*n]`, `[->n]`, `[=n]`
- **Sequence Operators**: `throughout`, `within`, `intersect`
- **Complex Temporal Operators**: `until`, `s_until`, `eventually`
- **Sequence Definitions**: Named sequences
- **Property Definitions**: Named properties
- **Variable Delays**: `##[m:n]`

## Examples

### Example 1: Basic Request-Acknowledge

```systemverilog
// Input SVA
req_ack_check: assert property (@(posedge clk) req |-> ##1 ack);

// Generated RTL (simplified)
module req_ack_check_checker_rtl (
    input logic clk,
    input logic req,
    input logic ack,
    output logic assertion_pass,
    output logic assertion_fail,
    output logic assertion_active
);
    // State machine implementation
    // ...
endmodule
```

### Example 2: Data Validation

```systemverilog
// Input SVA
data_valid_check: assert property (@(posedge clk) valid |-> ##2 ready);

// Generated state machine tracks the 2-cycle delay
// and checks ready signal at the correct time
```

### Example 3: With Disable Condition

```systemverilog
// Input SVA
reset_check: assert property (@(posedge clk) disable iff (!rst_n) 
                             valid |-> ##1 out_valid);

// Generated RTL includes reset handling
```

## Project Structure

```
sva_to_rtl/
├── sva_to_rtl/           # Main package
│   ├── __init__.py       # Package initialization
│   ├── parser.py         # SVA parser implementation
│   ├── state_machine.py  # State machine generator
│   ├── rtl_generator.py  # RTL code generator
│   └── cli.py            # Command line interface
├── examples/             # Example SVA files
│   ├── example_design.sv
│   └── simple_assertions.sv
├── tests/                # Test suite
│   ├── test_parser.py
│   ├── test_state_machine.py
│   ├── test_rtl_generator.py
│   └── run_tests.py
├── requirements.txt      # Python dependencies
├── setup.py             # Package setup
├── main.py              # Main entry point
└── README.md            # This file
```

## Generated RTL Structure

Each generated RTL module includes:

1. **Input Ports**:
   - Clock and reset signals
   - Assertion input signals
   - Disable condition signals

2. **Output Ports**:
   - `assertion_pass`: High when assertion succeeds
   - `assertion_fail`: High when assertion fails
   - `assertion_active`: High when assertion is being checked

3. **Internal Logic**:
   - State machine registers
   - Next-state combinational logic
   - Output generation logic

4. **Parameters**:
   - State encoding definitions
   - State bit width calculations

## Testing

Run the test suite:

```bash
# Using the simple test runner
python tests/run_tests.py

# Or with pytest (if installed)
pytest tests/
```

## Limitations

- Complex SVA constructs are not yet fully supported
- Parser handles a subset of SystemVerilog syntax
- Generated RTL may not be optimal for all use cases
- Error handling could be improved for edge cases

## Contributing

1. Fork the repository
2. Create a feature branch
3. Implement your changes
4. Add tests for new functionality
5. Run the test suite
6. Submit a pull request

## License

This project is licensed under the MIT License - see the LICENSE file for details.

## Future Enhancements

- Support for more complex SVA constructs
- Better optimization of generated state machines
- Integration with formal verification tools
- Support for SystemVerilog interfaces and modports
- GUI interface for easier use
- Support for assertion libraries

## Troubleshooting

### Common Issues

1. **Import Errors**: Ensure all dependencies are installed
2. **Parse Errors**: Check SVA syntax matches supported constructs
3. **RTL Generation Errors**: Verify state machine generation succeeded

### Debug Mode

Use the `--verbose` flag to get detailed information about the translation process:

```bash
python -m sva_to_rtl.cli translate file.sv --verbose
```

This will show:
- Parsed assertions
- Generated state machines
- RTL generation steps
- Any warnings or errors

## Contact

For questions, issues, or contributions, please open an issue on the project repository.

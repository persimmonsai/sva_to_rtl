# Cocotb Integration Guide

This guide explains how to use the cocotb integration features of the SVA to RTL Translation Tool.

## Overview

The tool now generates cocotb-compatible Python test code from SVA assertions, enabling runtime verification of digital designs using Python-based testbenches.

## Key Features

### Cocotb Assertion Generation
- Converts SVA assertions into Python cocotb test classes
- Implements assertion checking as coroutines
- Supports implication operators (`|->`, `|=>`)
- Handles delay operators (`##n`)
- Provides runtime verification capabilities

### Generated Test Structure
Each cocotb assertion generates:
- A Python class with assertion checking logic
- Coroutines for runtime monitoring
- Signal evaluation helpers
- Error handling and reporting

## Usage

### Command Line Interface

Generate cocotb tests along with RTL:
```bash
python -m sva_to_rtl.cli translate design.sv --cocotb -o output_dir
```

Generate only cocotb tests:
```bash
python -m sva_to_rtl.cli translate design.sv --cocotb -o cocotb_tests
```

### Python API

```python
from sva_to_rtl.cocotb_generator import CocotbGenerator

# After parsing assertions and generating state machines
cocotb_generator = CocotbGenerator()
cocotb_assertions = cocotb_generator.generate_multiple(assertions, state_machines)

# Save test file
cocotb_generator.save_test_file(list(cocotb_assertions.values()), "test_assertions.py")
```

## Generated Code Structure

### Example Input SVA
```systemverilog
handshake: assert property (@(posedge clk) req |-> ##1 ack);
```

### Generated Cocotb Test
```python
class HandshakeChecker:
    """Cocotb assertion checker for: req |-> ##1 ack"""
    
    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger('cocotb.HandshakeChecker')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.req = dut.req
        self.ack = dut.ack
    
    @cocotb.coroutine
    async def check_assertion(self):
        """Main assertion checking coroutine"""
        while True:
            try:
                await self._check_assertion_logic()
            except TestFailure as e:
                self.fail_count += 1
                self.logger.error(f'Assertion failed: {e}')
                if self.fail_count >= 10:
                    raise
            except Exception as e:
                self.logger.error(f'Unexpected error: {e}')
                raise
            await RisingEdge(self.clock)
    
    @cocotb.coroutine
    async def _check_assertion_logic(self):
        """Core assertion checking logic"""
        if self._evaluate_condition('req'):
            self.assertion_count += 1
            self.logger.debug('Antecedent triggered: req')
            
            # Wait 1 clock cycles
            await self._wait_cycles(1)
            
            # Check consequent: ack
            if not self._evaluate_condition('ack'):
                self.fail_count += 1
                raise TestFailure('Assertion handshake failed: consequent not satisfied')
            else:
                self.pass_count += 1
                self.logger.info('Assertion handshake passed')
```

## Supported SVA Constructs

### Implication Assertions
- `|->` (overlapping implication)
- `|=>` (non-overlapping implication)
- Delay operators (`##n`)
- Boolean expressions (`&&`, `||`, `!`)

### Property Types
- **assert**: Generates failure on violation
- **assume**: Generates warnings on violation
- **cover**: Tracks coverage hits

### Clock and Reset
- Clock expressions: `@(posedge clk)`, `@(negedge clk)`
- Reset handling (when specified)
- Disable conditions support

## Running Cocotb Tests

### Prerequisites
```bash
pip install cocotb
```

### Test Execution
```bash
# Using make (requires Makefile)
make

# Using cocotb directly
cocotb-run --module test_assertions --toplevel dut design.sv
```

### Example Makefile
```makefile
SIM ?= icarus
TOPLEVEL = dut
MODULE = test_sva_assertions
VERILOG_SOURCES = design.sv

include $(shell cocotb-config --makefiles)/Makefile.sim
```

## Advanced Features

### Signal Evaluation
The generated code includes helper functions for evaluating SystemVerilog expressions:
- Automatic signal name resolution
- SystemVerilog to Python operator conversion
- Error handling for invalid expressions

### Logging and Reporting
- Configurable logging levels
- Pass/fail counters
- Detailed error messages
- Integration with cocotb's logging system

### State Machine Integration
For complex assertions, the cocotb generator uses state machine information to:
- Optimize checking logic
- Handle multi-cycle sequences
- Manage assertion state

## Best Practices

### Test Organization
1. Use descriptive assertion names
2. Group related assertions in separate files
3. Include proper documentation strings
4. Handle expected failures gracefully

### Performance Considerations
1. Limit assertion checking frequency for complex designs
2. Use appropriate logging levels
3. Consider disabling non-critical assertions in long tests
4. Monitor memory usage for large designs

### Debugging Tips
1. Enable verbose logging for debugging
2. Use cocotb's built-in debugging features
3. Check signal connectivity and naming
4. Verify clock and reset behavior

## Integration with Existing Flows

### With Traditional Verification
- Use cocotb assertions alongside SystemVerilog testbenches
- Integrate with existing test infrastructure
- Combine with formal verification tools

### With CI/CD Pipelines
- Include cocotb tests in automated testing
- Generate reports for assertion coverage
- Integrate with regression testing frameworks

## Limitations and Future Work

### Current Limitations
- Complex SVA temporal operators not yet supported
- Limited SystemVerilog expression parsing
- No support for SystemVerilog interfaces

### Planned Enhancements
- Support for more temporal operators
- Better expression parsing
- Integration with formal verification
- Performance optimizations

## Examples

See the `examples/` directory for:
- Basic cocotb test examples
- Complex assertion patterns
- Integration with RTL designs
- Makefile templates

## Troubleshooting

### Common Issues
1. **Import errors**: Ensure cocotb is properly installed
2. **Signal not found**: Check signal naming in DUT
3. **Clock issues**: Verify clock signal connectivity
4. **Assertion failures**: Review assertion logic and timing

### Getting Help
- Check the cocotb documentation
- Review generated code for issues
- Use verbose logging for debugging
- Consult the tool's issue tracker

<!-- Use this file to provide workspace-specific custom instructions to Copilot. For more details, visit https://code.visualstudio.com/docs/copilot/copilot-customization#_use-a-githubcopilotinstructionsmd-file -->

# SVA to RTL Translation Tool - Copilot Instructions

This is a Python project that translates SystemVerilog Assertions (SVA) into synthesizable SystemVerilog RTL state machines.

## Project Structure

- `sva_to_rtl/parser.py`: SVA parser that handles SystemVerilog assertion syntax
- `sva_to_rtl/state_machine.py`: State machine generator that converts SVA logic to finite state machines
- `sva_to_rtl/rtl_generator.py`: RTL code generator that produces synthesizable SystemVerilog
- `sva_to_rtl/cli.py`: Command-line interface for the tool
- `examples/`: Example SystemVerilog files with SVA assertions
- `tests/`: Test suite for all components

## Key Concepts

### SVA (SystemVerilog Assertions)
- Temporal assertions that specify expected behavior over time
- Common operators: `|->` (implication), `##n` (delay), `@(posedge clk)` (clock)
- Property types: assert, assume, cover

### State Machine Generation
- Each SVA assertion is converted to a finite state machine
- States represent different phases of the assertion check
- Transitions are based on signal conditions and timing

### RTL Generation
- State machines are converted to synthesizable SystemVerilog modules
- Includes clock, reset, and disable condition handling
- Outputs assertion status (pass/fail/active)

## Coding Guidelines

1. **Error Handling**: Always include proper error handling for parsing and generation
2. **Documentation**: Document all complex logic, especially parser rules
3. **Testing**: Add tests for new SVA constructs or generation features
4. **SystemVerilog Compliance**: Generated RTL should be synthesizable and follow best practices
5. **Modularity**: Keep parser, state machine, and RTL generation separate and well-defined

## Common Patterns

### Parser Extensions
When adding new SVA constructs:
1. Add regex patterns for new syntax
2. Extend the AST classes if needed
3. Update the tokenizer and expression parser
4. Add corresponding tests

### State Machine Extensions
When adding new temporal operators:
1. Add new state types if needed
2. Update transition generation logic
3. Consider optimization opportunities
4. Test with various signal combinations

### RTL Generation Extensions
When enhancing RTL output:
1. Maintain synthesizable code standards
2. Add proper clock and reset handling
3. Include appropriate comments in generated code
4. Generate corresponding testbenches

## Testing Strategy

- Unit tests for each component (parser, state machine, RTL generator)
- Integration tests for complete SVA to RTL flow
- Example-based testing with real SystemVerilog files
- Generated RTL should be testable with standard simulation tools

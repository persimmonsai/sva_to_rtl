"""
RTL Generator for SVA State Machines

This module generates synthesizable SystemVerilog RTL code from state machines.
"""

from typing import Dict, List, Set, Optional, Any
from dataclasses import dataclass
import re

from .state_machine import StateMachine, State, Transition, StateType


@dataclass
class RTLModule:
    """Represents a generated RTL module"""
    name: str
    ports: List[str]
    signals: List[str]
    parameters: List[str]
    logic: List[str]
    
    def to_string(self) -> str:
        """Convert module to SystemVerilog string"""
        lines = []
        
        # Module header
        lines.append(f"module {self.name} (")
        
        # Ports
        if self.ports:
            for i, port in enumerate(self.ports):
                comma = "," if i < len(self.ports) - 1 else ""
                lines.append(f"    {port}{comma}")
        
        lines.append(");")
        lines.append("")
        
        # Parameters
        if self.parameters:
            for param in self.parameters:
                lines.append(f"    {param}")
            lines.append("")
        
        # Signal declarations
        if self.signals:
            for signal in self.signals:
                lines.append(f"    {signal}")
            lines.append("")
        
        # Logic
        if self.logic:
            for logic_line in self.logic:
                lines.append(f"    {logic_line}")
        
        lines.append("")
        lines.append("endmodule")
        
        return "\n".join(lines)


class RTLGenerator:
    """Generates synthesizable SystemVerilog RTL from state machines"""
    
    def __init__(self):
        self.modules: Dict[str, RTLModule] = {}
    
    def generate(self, sm: StateMachine) -> RTLModule:
        """Generate RTL module from state machine"""
        module_name = f"{sm.name}_rtl"
        
        # Generate ports
        ports = self._generate_ports(sm)
        
        # Generate parameters
        parameters = self._generate_parameters(sm)
        
        # Generate internal signals
        signals = self._generate_signals(sm)
        
        # Generate logic
        logic = self._generate_logic(sm)
        
        # Create RTL module
        module = RTLModule(
            name=module_name,
            ports=ports,
            signals=signals,
            parameters=parameters,
            logic=logic
        )
        
        self.modules[module_name] = module
        return module
    
    def _generate_ports(self, sm: StateMachine) -> List[str]:
        """Generate module ports"""
        ports = []
        
        # Clock and reset
        ports.append(f"input logic {sm.clock}")
        
        if sm.reset:
            ports.append(f"input logic {sm.reset}")
        
        # Disable condition
        if sm.disable_condition:
            # Extract signals from disable condition
            disable_signals = self._extract_signals_from_condition(sm.disable_condition)
            for signal in disable_signals:
                ports.append(f"input logic {signal}")
        
        # Input signals from assertion
        for signal in sorted(sm.signals):
            if not self._is_internal_signal(signal):
                ports.append(f"input logic {signal}")
        
        # Output signals
        ports.append("output logic assertion_pass")
        ports.append("output logic assertion_fail")
        ports.append("output logic assertion_active")
        
        return ports
    
    def _generate_parameters(self, sm: StateMachine) -> List[str]:
        """Generate module parameters"""
        parameters = []
        
        # State encoding parameters
        state_bits = self._calculate_state_bits(len(sm.states))
        parameters.append(f"parameter STATE_BITS = {state_bits};")
        
        # State definitions
        for i, state_name in enumerate(sorted(sm.states.keys())):
            parameters.append(f"parameter {state_name} = {state_bits}'d{i};")
        
        return parameters
    
    def _generate_signals(self, sm: StateMachine) -> List[str]:
        """Generate internal signals"""
        signals = []
        
        # State register
        state_bits = self._calculate_state_bits(len(sm.states))
        signals.append(f"logic [STATE_BITS-1:0] current_state, next_state;")
        
        # Internal condition signals
        for transition in sm.transitions:
            if self._is_complex_condition(transition.condition):
                signal_name = f"cond_{self._condition_to_signal_name(transition.condition)}"
                signals.append(f"logic {signal_name};")
        
        return signals
    
    def _generate_logic(self, sm: StateMachine) -> List[str]:
        """Generate module logic"""
        logic = []
        
        # State register
        logic.extend(self._generate_state_register(sm))
        
        # Next state logic
        logic.extend(self._generate_next_state_logic(sm))
        
        # Output logic
        logic.extend(self._generate_output_logic(sm))
        
        # Condition assignments
        logic.extend(self._generate_condition_assignments(sm))
        
        return logic
    
    def _generate_state_register(self, sm: StateMachine) -> List[str]:
        """Generate state register logic"""
        logic = []
        
        logic.append("// State register")
        logic.append(f"always_ff @(posedge {sm.clock}) begin")
        
        if sm.reset:
            logic.append(f"    if ({sm.reset}) begin")
            logic.append(f"        current_state <= {sm.initial_state};")
            logic.append("    end")
        
        if sm.disable_condition:
            logic.append(f"    else if ({sm.disable_condition}) begin")
            logic.append(f"        current_state <= {sm.initial_state};")
            logic.append("    end")
        
        logic.append("    else begin")
        logic.append("        current_state <= next_state;")
        logic.append("    end")
        logic.append("end")
        logic.append("")
        
        return logic
    
    def _generate_next_state_logic(self, sm: StateMachine) -> List[str]:
        """Generate next state combinational logic"""
        logic = []
        
        logic.append("// Next state logic")
        logic.append("always_comb begin")
        logic.append("    next_state = current_state;")
        logic.append("")
        logic.append("    case (current_state)")
        
        # Group transitions by source state
        state_transitions = {}
        for transition in sm.transitions:
            if transition.from_state not in state_transitions:
                state_transitions[transition.from_state] = []
            state_transitions[transition.from_state].append(transition)
        
        for state_name in sorted(sm.states.keys()):
            logic.append(f"        {state_name}: begin")
            
            if state_name in state_transitions:
                for transition in state_transitions[state_name]:
                    condition = self._format_condition(transition.condition)
                    logic.append(f"            if ({condition}) begin")
                    logic.append(f"                next_state = {transition.to_state};")
                    logic.append("            end")
            
            logic.append("        end")
            logic.append("")
        
        logic.append("        default: begin")
        logic.append(f"            next_state = {sm.initial_state};")
        logic.append("        end")
        logic.append("    endcase")
        logic.append("end")
        logic.append("")
        
        return logic
    
    def _generate_output_logic(self, sm: StateMachine) -> List[str]:
        """Generate output logic"""
        logic = []
        
        logic.append("// Output logic")
        logic.append("always_comb begin")
        logic.append("    assertion_pass = 1'b0;")
        logic.append("    assertion_fail = 1'b0;")
        logic.append("    assertion_active = 1'b0;")
        logic.append("")
        logic.append("    case (current_state)")
        
        for state_name, state in sm.states.items():
            logic.append(f"        {state_name}: begin")
            
            if state.state_type == StateType.SUCCESS:
                logic.append("            assertion_pass = 1'b1;")
            elif state.state_type == StateType.FAILURE:
                logic.append("            assertion_fail = 1'b1;")
            elif state.state_type == StateType.ACTIVE:
                logic.append("            assertion_active = 1'b1;")
            
            logic.append("        end")
        
        logic.append("        default: begin")
        logic.append("            // Default outputs")
        logic.append("        end")
        logic.append("    endcase")
        logic.append("end")
        logic.append("")
        
        return logic
    
    def _generate_condition_assignments(self, sm: StateMachine) -> List[str]:
        """Generate condition signal assignments"""
        logic = []
        
        # Find complex conditions that need separate signals
        complex_conditions = set()
        for transition in sm.transitions:
            if self._is_complex_condition(transition.condition):
                complex_conditions.add(transition.condition)
        
        if complex_conditions:
            logic.append("// Condition assignments")
            for condition in sorted(complex_conditions):
                signal_name = f"cond_{self._condition_to_signal_name(condition)}"
                formatted_condition = self._format_condition(condition)
                logic.append(f"assign {signal_name} = {formatted_condition};")
            logic.append("")
        
        return logic
    
    def _calculate_state_bits(self, num_states: int) -> int:
        """Calculate number of bits needed for state encoding"""
        if num_states <= 1:
            return 1
        
        bits = 0
        while (1 << bits) < num_states:
            bits += 1
        
        return bits
    
    def _is_internal_signal(self, signal: str) -> bool:
        """Check if signal is internal (not a port)"""
        # Simple heuristic - can be enhanced
        internal_prefixes = ["temp_", "internal_", "state_"]
        return any(signal.startswith(prefix) for prefix in internal_prefixes)
    
    def _is_complex_condition(self, condition: str) -> bool:
        """Check if condition is complex and needs a separate signal"""
        # Consider parentheses, multiple operators, etc.
        return ("(" in condition and ")" in condition) or \
               any(op in condition for op in ["&&", "||", "==", "!=", ">=", "<=", ">", "<"])
    
    def _condition_to_signal_name(self, condition: str) -> str:
        """Convert condition to valid signal name"""
        # Replace operators and special characters
        name = condition.replace("&&", "_and_")
        name = name.replace("||", "_or_")
        name = name.replace("==", "_eq_")
        name = name.replace("!=", "_neq_")
        name = name.replace(">=", "_gte_")
        name = name.replace("<=", "_lte_")
        name = name.replace(">", "_gt_")
        name = name.replace("<", "_lt_")
        name = name.replace("!", "_not_")
        name = name.replace("(", "_")
        name = name.replace(")", "_")
        name = name.replace(" ", "_")
        name = name.replace("[", "_")
        name = name.replace("]", "_")
        
        # Remove multiple underscores
        name = re.sub(r'_+', '_', name)
        name = name.strip('_')
        
        # Ensure valid identifier
        if not name or not name[0].isalpha():
            name = f"sig_{name}"
        
        return name
    
    def _format_condition(self, condition: str) -> str:
        """Format condition for SystemVerilog"""
        # Handle special cases
        if condition == "1'b1":
            return "1'b1"
        if condition == "1'b0":
            return "1'b0"
        
        # For complex conditions, use the signal name
        if self._is_complex_condition(condition):
            return f"cond_{self._condition_to_signal_name(condition)}"
        
        # Simple conditions
        return condition
    
    def _extract_signals_from_condition(self, condition: str) -> Set[str]:
        """Extract signal names from a condition"""
        signals = set()
        
        # Simple regex to find identifiers
        identifiers = re.findall(r'[a-zA-Z_][a-zA-Z0-9_]*', condition)
        
        for identifier in identifiers:
            # Filter out SystemVerilog keywords
            if identifier not in ['and', 'or', 'not', 'begin', 'end', 'if', 'else']:
                signals.add(identifier)
        
        return signals
    
    def generate_multiple(self, state_machines: Dict[str, StateMachine]) -> Dict[str, RTLModule]:
        """Generate RTL modules for multiple state machines"""
        result = {}
        
        for sm_name, sm in state_machines.items():
            try:
                module = self.generate(sm)
                result[module.name] = module
            except Exception as e:
                print(f"Warning: Failed to generate RTL for {sm_name}: {e}")
        
        return result
    
    def generate_testbench(self, module: RTLModule) -> str:
        """Generate a simple testbench for the RTL module"""
        lines = []
        
        # Testbench module header
        tb_name = f"{module.name}_tb"
        lines.append(f"module {tb_name};")
        lines.append("")
        
        # Signal declarations
        lines.append("    // Clock and reset")
        lines.append("    logic clk = 0;")
        lines.append("    logic rst = 1;")
        lines.append("")
        
        # Input signals
        lines.append("    // Input signals")
        for port in module.ports:
            if "input" in port and "clk" not in port and "rst" not in port:
                signal_name = port.split()[-1]
                lines.append(f"    logic {signal_name} = 0;")
        lines.append("")
        
        # Output signals
        lines.append("    // Output signals")
        for port in module.ports:
            if "output" in port:
                signal_name = port.split()[-1]
                lines.append(f"    logic {signal_name};")
        lines.append("")
        
        # DUT instantiation
        lines.append("    // DUT instantiation")
        lines.append(f"    {module.name} dut (")
        lines.append("        .clk(clk),")
        lines.append("        .rst(rst),")
        
        for port in module.ports:
            if "input" in port and "clk" not in port and "rst" not in port:
                signal_name = port.split()[-1]
                lines.append(f"        .{signal_name}({signal_name}),")
            elif "output" in port:
                signal_name = port.split()[-1]
                lines.append(f"        .{signal_name}({signal_name}),")
        
        # Remove last comma
        if lines[-1].endswith(","):
            lines[-1] = lines[-1][:-1]
        
        lines.append("    );")
        lines.append("")
        
        # Clock generation
        lines.append("    // Clock generation")
        lines.append("    always #5 clk = ~clk;")
        lines.append("")
        
        # Test stimulus
        lines.append("    // Test stimulus")
        lines.append("    initial begin")
        lines.append("        $dumpfile(\"waves.vcd\");")
        lines.append("        $dumpvars(0, dut);")
        lines.append("")
        lines.append("        // Reset")
        lines.append("        rst = 1;")
        lines.append("        #20;")
        lines.append("        rst = 0;")
        lines.append("        #10;")
        lines.append("")
        lines.append("        // Add test cases here")
        lines.append("        #100;")
        lines.append("")
        lines.append("        $finish;")
        lines.append("    end")
        lines.append("")
        
        # Monitoring
        lines.append("    // Monitoring")
        lines.append("    always @(posedge clk) begin")
        lines.append("        if (assertion_pass)")
        lines.append("            $display(\"Time %t: Assertion PASSED\", $time);")
        lines.append("        if (assertion_fail)")
        lines.append("            $display(\"Time %t: Assertion FAILED\", $time);")
        lines.append("    end")
        lines.append("")
        
        lines.append("endmodule")
        
        return "\n".join(lines)
    
    def save_module(self, module: RTLModule, filename: str):
        """Save RTL module to file"""
        with open(filename, 'w') as f:
            f.write(module.to_string())
    
    def get_modules(self) -> Dict[str, RTLModule]:
        """Get all generated modules"""
        return self.modules

"""
Cocotb Generator for SVA to Python Runtime Assertions

This module generates cocotb-compatible Python test code from SVA assertions
that can be used for runtime verification of digital designs.
"""

from typing import Dict, List, Set, Optional, Any
from dataclasses import dataclass
import re

from .parser import SVAAssertion, SVASequence, SVAProperty, SVAOperator
from .state_machine import StateMachine, State, Transition, StateType


@dataclass
class CocotbAssertion:
    """Represents a cocotb assertion implementation"""
    name: str
    class_name: str
    code: str
    imports: Set[str]
    signals: Set[str]
    clock_name: str
    reset_name: Optional[str] = None
    disable_condition: Optional[str] = None


class CocotbGenerator:
    """Generates cocotb Python assertions from SVA assertions"""
    
    def __init__(self):
        self.assertions: Dict[str, CocotbAssertion] = {}
    
    def generate(self, assertion: SVAAssertion, sm: StateMachine) -> CocotbAssertion:
        """Generate cocotb assertion from SVA assertion and state machine"""
        
        # Create assertion class name
        class_name = f"{assertion.name.title()}Checker"
        
        # Extract clock and reset
        clock_name = self._get_clock_name(assertion)
        reset_name = self._get_reset_name(assertion)
        disable_condition = self._get_disable_condition(assertion)
        
        # Generate imports
        imports = self._generate_imports(assertion, sm)
        
        # Generate the assertion class code
        code = self._generate_assertion_class(
            assertion, sm, class_name, clock_name, reset_name, disable_condition
        )
        
        # Create cocotb assertion
        cocotb_assertion = CocotbAssertion(
            name=assertion.name,
            class_name=class_name,
            code=code,
            imports=imports,
            signals=sm.signals,
            clock_name=clock_name,
            reset_name=reset_name,
            disable_condition=disable_condition
        )
        
        self.assertions[assertion.name] = cocotb_assertion
        return cocotb_assertion
    
    def _generate_imports(self, assertion: SVAAssertion, sm: StateMachine) -> Set[str]:
        """Generate required imports for cocotb assertion"""
        imports = set()
        
        # Standard cocotb imports
        imports.add("import cocotb")
        imports.add("from cocotb.triggers import RisingEdge, FallingEdge, Timer")
        imports.add("from cocotb.clock import Clock")
        imports.add("from cocotb.result import TestFailure")
        imports.add("import logging")
        
        # Additional imports based on assertion type
        if assertion.property.property_type == "cover":
            imports.add("from cocotb.result import TestSuccess")
        
        # Import for state machine if complex
        if len(sm.states) > 3:
            imports.add("from enum import Enum")
        
        return imports
    
    def _generate_assertion_class(self, assertion: SVAAssertion, sm: StateMachine, 
                                class_name: str, clock_name: str, 
                                reset_name: Optional[str], 
                                disable_condition: Optional[str]) -> str:
        """Generate the main assertion class code"""
        
        lines = []
        
        # Class header
        lines.append(f"class {class_name}:")
        lines.append(f'    """Cocotb assertion checker for: {assertion.property.sequence.expression}"""')
        lines.append("")
        
        # Constructor
        lines.append("    def __init__(self, dut):")
        lines.append("        self.dut = dut")
        lines.append(f"        self.clock = dut.{clock_name}")
        
        if reset_name:
            lines.append(f"        self.reset = dut.{reset_name}")
        
        lines.append("        self.logger = logging.getLogger(f'cocotb.{class_name}')")
        lines.append("        self.assertion_count = 0")
        lines.append("        self.pass_count = 0")
        lines.append("        self.fail_count = 0")
        
        # Add signal references
        for signal in sorted(sm.signals):
            lines.append(f"        self.{signal} = dut.{signal}")
        
        lines.append("")
        
        # Generate state machine if needed
        if len(sm.states) > 3:
            lines.extend(self._generate_state_enum(sm))
            lines.append("")
        
        # Generate main check method
        lines.extend(self._generate_check_method(assertion, sm))
        lines.append("")
        
        # Generate helper methods
        lines.extend(self._generate_helper_methods(assertion, sm))
        
        return "\n".join(lines)
    
    def _generate_state_enum(self, sm: StateMachine) -> List[str]:
        """Generate state enumeration"""
        lines = []
        
        lines.append("    class State(Enum):")
        for i, state_name in enumerate(sorted(sm.states.keys())):
            lines.append(f"        {state_name} = {i}")
        lines.append("")
        lines.append("        self.current_state = self.State.IDLE")
        
        return lines
    
    def _generate_check_method(self, assertion: SVAAssertion, sm: StateMachine) -> List[str]:
        """Generate the main assertion check method"""
        lines = []
        
        # Method signature
        lines.append("    @cocotb.coroutine")
        lines.append("    async def check_assertion(self):")
        lines.append('        """Main assertion checking coroutine"""')
        lines.append("")
        
        # Reset handling
        if assertion.property.reset or assertion.property.sequence.reset:
            lines.append("        # Wait for reset deassertion")
            lines.append("        while self.reset.value == 0:")
            lines.append("            await RisingEdge(self.clock)")
            lines.append("")
        
        # Main checking loop
        lines.append("        while True:")
        lines.append("            try:")
        lines.append("                await self._check_assertion_logic()")
        lines.append("            except TestFailure as e:")
        lines.append("                self.fail_count += 1")
        lines.append("                self.logger.error(f'Assertion failed: {e}')")
        lines.append("                if self.fail_count >= 10:  # Configurable threshold")
        lines.append("                    raise")
        lines.append("            except Exception as e:")
        lines.append("                self.logger.error(f'Unexpected error: {e}')")
        lines.append("                raise")
        lines.append("")
        lines.append("            await RisingEdge(self.clock)")
        
        return lines
    
    def _generate_helper_methods(self, assertion: SVAAssertion, sm: StateMachine) -> List[str]:
        """Generate helper methods for assertion checking"""
        lines = []
        
        # Generate assertion logic method
        lines.append("    @cocotb.coroutine")
        lines.append("    async def _check_assertion_logic(self):")
        lines.append('        """Core assertion checking logic"""')
        lines.append("")
        
        # Parse the assertion expression
        expression = assertion.property.sequence.expression
        
        if "|=>" in expression or "|->" in expression:
            # Implication-based assertion
            lines.extend(self._generate_implication_check(expression, assertion))
        elif "&&" in expression or "||" in expression:
            # Boolean expression (typically for cover)
            lines.extend(self._generate_boolean_check(expression, assertion))
        else:
            # Simple signal check
            lines.extend(self._generate_simple_check(expression, assertion))
        
        lines.append("")
        
        # Generate delay helper if needed
        if "##" in expression:
            lines.extend(self._generate_delay_helper())
            lines.append("")
        
        # Generate condition evaluation helper
        lines.extend(self._generate_condition_helper())
        
        return lines
    
    def _generate_implication_check(self, expression: str, assertion: SVAAssertion) -> List[str]:
        """Generate implication checking logic"""
        lines = []
        
        # Parse implication
        if "|->" in expression:
            parts = expression.split("|->")
            antecedent = parts[0].strip()
            consequent = parts[1].strip()
            overlap = True
        else:  # |=>
            parts = expression.split("|=>")
            antecedent = parts[0].strip()
            consequent = parts[1].strip()
            overlap = False
        
        # Generate the checking logic
        lines.append(f"        # Check implication: {expression}")
        lines.append(f"        if self._evaluate_condition('{antecedent}'):")
        lines.append("            self.assertion_count += 1")
        lines.append(f"            self.logger.debug(f'Antecedent triggered: {antecedent}')")
        lines.append("")
        
        # Handle delay in consequent
        if "##" in consequent:
            delay_match = re.search(r'##(\d+)', consequent)
            if delay_match:
                delay = int(delay_match.group(1))
                consequent_condition = re.sub(r'##\d+\s*', '', consequent).strip()
                
                lines.append(f"            # Wait {delay} clock cycles")
                lines.append(f"            await self._wait_cycles({delay})")
                lines.append("")
                lines.append(f"            # Check consequent: {consequent_condition}")
                lines.append(f"            if not self._evaluate_condition('{consequent_condition}'):")
                
                if assertion.property.property_type == "assert":
                    lines.append("                self.fail_count += 1")
                    lines.append(f"                raise TestFailure(f'Assertion {assertion.name} failed: consequent not satisfied')")
                else:
                    lines.append("                self.logger.warning(f'Consequent not satisfied: {consequent_condition}')")
                
                lines.append("            else:")
                lines.append("                self.pass_count += 1")
                lines.append(f"                self.logger.info(f'Assertion {assertion.name} passed')")
        else:
            # No delay in consequent
            if not overlap:
                lines.append("            await RisingEdge(self.clock)")
            
            lines.append(f"            # Check consequent: {consequent}")
            lines.append(f"            if not self._evaluate_condition('{consequent}'):")
            
            if assertion.property.property_type == "assert":
                lines.append("                self.fail_count += 1")
                lines.append(f"                raise TestFailure(f'Assertion {assertion.name} failed: consequent not satisfied')")
            else:
                lines.append("                self.logger.warning(f'Consequent not satisfied: {consequent}')")
            
            lines.append("            else:")
            lines.append("                self.pass_count += 1")
            lines.append(f"                self.logger.info(f'Assertion {assertion.name} passed')")
        
        return lines
    
    def _generate_boolean_check(self, expression: str, assertion: SVAAssertion) -> List[str]:
        """Generate boolean expression checking logic"""
        lines = []
        
        lines.append(f"        # Check boolean expression: {expression}")
        lines.append(f"        if self._evaluate_condition('{expression}'):")
        
        if assertion.property.property_type == "cover":
            lines.append("            self.pass_count += 1")
            lines.append(f"            self.logger.info(f'Cover point {assertion.name} hit')")
        else:
            lines.append("            self.pass_count += 1")
            lines.append(f"            self.logger.debug(f'Condition {assertion.name} satisfied')")
        
        return lines
    
    def _generate_simple_check(self, expression: str, assertion: SVAAssertion) -> List[str]:
        """Generate simple signal checking logic"""
        lines = []
        
        lines.append(f"        # Check simple condition: {expression}")
        lines.append(f"        if self._evaluate_condition('{expression}'):")
        lines.append("            self.pass_count += 1")
        lines.append(f"            self.logger.debug(f'Condition {assertion.name} satisfied')")
        
        return lines
    
    def _generate_delay_helper(self) -> List[str]:
        """Generate delay helper method"""
        lines = []
        
        lines.append("    @cocotb.coroutine")
        lines.append("    async def _wait_cycles(self, cycles):")
        lines.append('        """Wait for specified number of clock cycles"""')
        lines.append("        for _ in range(cycles):")
        lines.append("            await RisingEdge(self.clock)")
        
        return lines
    
    def _generate_condition_helper(self) -> List[str]:
        """Generate condition evaluation helper"""
        lines = []
        
        lines.append("    def _evaluate_condition(self, condition):")
        lines.append('        """Evaluate a condition string against DUT signals"""')
        lines.append("        try:")
        lines.append("            # Replace signal names with actual values")
        lines.append("            eval_str = condition")
        lines.append("            ")
        lines.append("            # Handle common signal operations")
        lines.append("            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):")
        lines.append("                if signal_name in eval_str:")
        lines.append("                    signal_value = getattr(self.dut, signal_name).value")
        lines.append("                    eval_str = eval_str.replace(signal_name, str(int(signal_value)))")
        lines.append("            ")
        lines.append("            # Handle SystemVerilog operators")
        lines.append("            eval_str = eval_str.replace('&&', ' and ')")
        lines.append("            eval_str = eval_str.replace('||', ' or ')")
        lines.append("            eval_str = eval_str.replace('!', ' not ')")
        lines.append("            ")
        lines.append("            # Evaluate the condition")
        lines.append("            return eval(eval_str)")
        lines.append("            ")
        lines.append("        except Exception as e:")
        lines.append("            self.logger.error(f'Error evaluating condition \"{condition}\": {e}')")
        lines.append("            return False")
        
        return lines
    
    def _get_clock_name(self, assertion: SVAAssertion) -> str:
        """Extract clock name from assertion"""
        if assertion.property.clock:
            return assertion.property.clock.replace("~", "")
        if assertion.property.sequence.clock:
            return assertion.property.sequence.clock.replace("~", "")
        return "clk"
    
    def _get_reset_name(self, assertion: SVAAssertion) -> Optional[str]:
        """Extract reset name from assertion"""
        if assertion.property.reset:
            return assertion.property.reset
        if assertion.property.sequence.reset:
            return assertion.property.sequence.reset
        return None
    
    def _get_disable_condition(self, assertion: SVAAssertion) -> Optional[str]:
        """Extract disable condition from assertion"""
        if assertion.property.disable_condition:
            return assertion.property.disable_condition
        if assertion.property.sequence.disable_condition:
            return assertion.property.sequence.disable_condition
        return None
    
    def generate_test_file(self, assertions: List[CocotbAssertion], 
                          module_name: str = "dut") -> str:
        """Generate a complete cocotb test file"""
        lines = []
        
        # File header
        lines.append('"""')
        lines.append('Cocotb test file generated from SVA assertions')
        lines.append('"""')
        lines.append("")
        
        # Collect all imports
        all_imports = set()
        for assertion in assertions:
            all_imports.update(assertion.imports)
        
        # Add imports
        for import_line in sorted(all_imports):
            lines.append(import_line)
        
        lines.append("")
        lines.append("")
        
        # Add assertion classes
        for assertion in assertions:
            lines.append(assertion.code)
            lines.append("")
            lines.append("")
        
        # Generate main test function
        lines.append("@cocotb.test()")
        lines.append(f"async def test_sva_assertions({module_name}):")
        lines.append('    """Main test function that runs all SVA assertions"""')
        lines.append("")
        
        # Initialize clock
        lines.append("    # Initialize clock")
        lines.append(f"    clock = Clock({module_name}.clk, 10, units='ns')")
        lines.append("    cocotb.start_soon(clock.start())")
        lines.append("")
        
        # Reset sequence
        lines.append("    # Reset sequence")
        lines.append(f"    {module_name}.rst_n.value = 0")
        lines.append("    await Timer(100, units='ns')")
        lines.append(f"    {module_name}.rst_n.value = 1")
        lines.append("    await Timer(100, units='ns')")
        lines.append("")
        
        # Create assertion checkers
        lines.append("    # Create assertion checkers")
        checker_names = []
        for assertion in assertions:
            checker_name = f"{assertion.name}_checker"
            checker_names.append(checker_name)
            lines.append(f"    {checker_name} = {assertion.class_name}({module_name})")
        
        lines.append("")
        
        # Start assertion checking
        lines.append("    # Start assertion checking")
        lines.append("    checker_tasks = []")
        for checker_name in checker_names:
            lines.append(f"    checker_tasks.append(cocotb.start_soon({checker_name}.check_assertion()))")
        
        lines.append("")
        
        # Test stimulus (placeholder)
        lines.append("    # Test stimulus - customize as needed")
        lines.append("    await Timer(1000, units='ns')")
        lines.append("")
        
        # Report results
        lines.append("    # Report results")
        for i, assertion in enumerate(assertions):
            checker_name = checker_names[i]
            lines.append(f"    {module_name}._log.info(f'{assertion.name}: {{{checker_name}.pass_count}} passed, {{{checker_name}.fail_count}} failed')")
        
        return "\n".join(lines)
    
    def generate_multiple(self, assertions: List[SVAAssertion], 
                         state_machines: Dict[str, StateMachine]) -> Dict[str, CocotbAssertion]:
        """Generate cocotb assertions for multiple SVA assertions"""
        result = {}
        
        for assertion in assertions:
            sm_name = f"{assertion.name}_checker"
            if sm_name in state_machines:
                sm = state_machines[sm_name]
                try:
                    cocotb_assertion = self.generate(assertion, sm)
                    result[assertion.name] = cocotb_assertion
                except Exception as e:
                    print(f"Warning: Failed to generate cocotb assertion for {assertion.name}: {e}")
        
        return result
    
    def save_test_file(self, assertions: List[CocotbAssertion], 
                      filename: str, module_name: str = "dut"):
        """Save cocotb test file"""
        test_content = self.generate_test_file(assertions, module_name)
        with open(filename, 'w') as f:
            f.write(test_content)
    
    def get_assertions(self) -> Dict[str, CocotbAssertion]:
        """Get all generated cocotb assertions"""
        return self.assertions

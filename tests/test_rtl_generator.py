"""
Test cases for RTL Generator
"""

import pytest
import sys
import os

# Add the parent directory to the path so we can import our modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from sva_to_rtl.parser import SVAParser
from sva_to_rtl.state_machine import StateMachineGenerator
from sva_to_rtl.rtl_generator import RTLGenerator


class TestRTLGenerator:
    def setup_method(self):
        """Setup test fixtures"""
        self.parser = SVAParser()
        self.sm_generator = StateMachineGenerator()
        self.rtl_generator = RTLGenerator()
    
    def test_generate_simple_rtl(self):
        """Test generating RTL from simple assertion"""
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        rtl_module = self.rtl_generator.generate(sm)
        
        assert rtl_module.name == "basic_assert_checker_rtl"
        assert len(rtl_module.ports) > 0
        assert any("clk" in port for port in rtl_module.ports)
        assert any("assertion_pass" in port for port in rtl_module.ports)
        assert any("assertion_fail" in port for port in rtl_module.ports)
    
    def test_generate_ports(self):
        """Test port generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) signal_a |-> signal_b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        ports = self.rtl_generator._generate_ports(sm)
        
        # Check for required ports
        port_strings = " ".join(ports)
        assert "input logic clk" in port_strings
        assert "output logic assertion_pass" in port_strings
        assert "output logic assertion_fail" in port_strings
        assert "output logic assertion_active" in port_strings
    
    def test_generate_parameters(self):
        """Test parameter generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        parameters = self.rtl_generator._generate_parameters(sm)
        
        # Check for state parameters
        param_strings = " ".join(parameters)
        assert "STATE_BITS" in param_strings
        assert "IDLE" in param_strings
    
    def test_generate_signals(self):
        """Test internal signal generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        signals = self.rtl_generator._generate_signals(sm)
        
        # Check for state signals
        signal_strings = " ".join(signals)
        assert "current_state" in signal_strings
        assert "next_state" in signal_strings
    
    def test_calculate_state_bits(self):
        """Test state bit calculation"""
        assert self.rtl_generator._calculate_state_bits(1) == 1
        assert self.rtl_generator._calculate_state_bits(2) == 1
        assert self.rtl_generator._calculate_state_bits(3) == 2
        assert self.rtl_generator._calculate_state_bits(4) == 2
        assert self.rtl_generator._calculate_state_bits(5) == 3
        assert self.rtl_generator._calculate_state_bits(8) == 3
        assert self.rtl_generator._calculate_state_bits(9) == 4
    
    def test_condition_formatting(self):
        """Test condition formatting"""
        assert self.rtl_generator._format_condition("1'b1") == "1'b1"
        assert self.rtl_generator._format_condition("1'b0") == "1'b0"
        assert self.rtl_generator._format_condition("simple_signal") == "simple_signal"
    
    def test_condition_to_signal_name(self):
        """Test converting conditions to signal names"""
        condition = "(a && b) || c"
        signal_name = self.rtl_generator._condition_to_signal_name(condition)
        
        assert signal_name.isidentifier()  # Valid identifier
        assert "and" in signal_name or "or" in signal_name
    
    def test_generate_testbench(self):
        """Test testbench generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        rtl_module = self.rtl_generator.generate(sm)
        
        testbench = self.rtl_generator.generate_testbench(rtl_module)
        
        assert "module" in testbench
        assert "_tb" in testbench
        assert "clk" in testbench
        assert "dut" in testbench
        assert "$finish" in testbench
    
    def test_module_to_string(self):
        """Test RTL module string generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        rtl_module = self.rtl_generator.generate(sm)
        
        module_string = rtl_module.to_string()
        
        assert "module" in module_string
        assert "endmodule" in module_string
        assert rtl_module.name in module_string
    
    def test_generate_multiple_rtl(self):
        """Test generating multiple RTL modules"""
        text = """
        assert1: assert property (@(posedge clk) a |-> b);
        assert2: assert property (@(posedge clk) c |-> d);
        """
        
        assertions = self.parser.parse_text(text)
        state_machines = self.sm_generator.generate_multiple(assertions)
        rtl_modules = self.rtl_generator.generate_multiple(state_machines)
        
        assert len(rtl_modules) == 2
        assert all("_rtl" in name for name in rtl_modules.keys())


if __name__ == "__main__":
    pytest.main([__file__])

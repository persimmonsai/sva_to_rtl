"""
Test cases for Cocotb Generator
"""

import pytest
import sys
import os

# Add the parent directory to the path so we can import our modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from sva_to_rtl.parser import SVAParser
from sva_to_rtl.state_machine import StateMachineGenerator
from sva_to_rtl.cocotb_generator import CocotbGenerator


class TestCocotbGenerator:
    def setup_method(self):
        """Setup test fixtures"""
        self.parser = SVAParser()
        self.sm_generator = StateMachineGenerator()
        self.cocotb_generator = CocotbGenerator()
    
    def test_generate_simple_cocotb_assertion(self):
        """Test generating cocotb assertion from simple SVA"""
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        cocotb_assertion = self.cocotb_generator.generate(assertion, sm)
        
        assert cocotb_assertion.name == "basic_assert"
        assert cocotb_assertion.class_name == "Basic_assertChecker"
        assert cocotb_assertion.clock_name == "clk"
        assert len(cocotb_assertion.signals) >= 2
        assert "a" in cocotb_assertion.signals
        assert "b" in cocotb_assertion.signals
    
    def test_generate_delayed_cocotb_assertion(self):
        """Test generating cocotb assertion with delay"""
        assertion_text = "delay_assert: assert property (@(posedge clk) req |-> ##1 ack);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        cocotb_assertion = self.cocotb_generator.generate(assertion, sm)
        
        assert cocotb_assertion.name == "delay_assert"
        assert "req" in cocotb_assertion.signals
        assert "ack" in cocotb_assertion.signals
        assert "##1" in cocotb_assertion.code or "_wait_cycles" in cocotb_assertion.code
    
    def test_generate_cover_cocotb_assertion(self):
        """Test generating cocotb assertion for cover property"""
        assertion_text = "cover_example: cover property (@(posedge clk) a && b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        cocotb_assertion = self.cocotb_generator.generate(assertion, sm)
        
        assert cocotb_assertion.name == "cover_example"
        assert "cover" in cocotb_assertion.code.lower()
    
    def test_generate_imports(self):
        """Test import generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        imports = self.cocotb_generator._generate_imports(assertion, sm)
        
        assert "import cocotb" in imports
        assert "from cocotb.triggers import RisingEdge, FallingEdge, Timer" in imports
        assert "from cocotb.clock import Clock" in imports
    
    def test_generate_test_file(self):
        """Test generating complete test file"""
        assertions_text = """
        assert1: assert property (@(posedge clk) a |-> b);
        assert2: cover property (@(posedge clk) c && d);
        """
        
        assertions = self.parser.parse_text(assertions_text)
        state_machines = self.sm_generator.generate_multiple(assertions)
        cocotb_assertions = self.cocotb_generator.generate_multiple(assertions, state_machines)
        
        test_file = self.cocotb_generator.generate_test_file(list(cocotb_assertions.values()))
        
        assert "import cocotb" in test_file
        assert "@cocotb.test()" in test_file
        assert "async def test_sva_assertions" in test_file
        assert "Clock" in test_file
        assert "checker" in test_file
    
    def test_generate_multiple_cocotb_assertions(self):
        """Test generating multiple cocotb assertions"""
        text = """
        assert1: assert property (@(posedge clk) req |-> ack);
        assert2: cover property (@(posedge clk) valid && ready);
        """
        
        assertions = self.parser.parse_text(text)
        state_machines = self.sm_generator.generate_multiple(assertions)
        cocotb_assertions = self.cocotb_generator.generate_multiple(assertions, state_machines)
        
        assert len(cocotb_assertions) == 2
        assert "assert1" in cocotb_assertions
        assert "assert2" in cocotb_assertions
    
    def test_condition_evaluation_helper(self):
        """Test condition evaluation helper generation"""
        assertion_text = "test_assert: assert property (@(posedge clk) (a && b) |-> c);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        cocotb_assertion = self.cocotb_generator.generate(assertion, sm)
        
        assert "_evaluate_condition" in cocotb_assertion.code
        assert "&&" in cocotb_assertion.code or "and" in cocotb_assertion.code
    
    def test_clock_and_reset_extraction(self):
        """Test clock and reset extraction"""
        assertion_text = "test_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        clock_name = self.cocotb_generator._get_clock_name(assertion)
        reset_name = self.cocotb_generator._get_reset_name(assertion)
        
        assert clock_name == "clk"
        assert reset_name is None  # No reset specified
    
    def test_implication_check_generation(self):
        """Test implication checking logic generation"""
        assertion_text = "impl_test: assert property (@(posedge clk) start |-> ##2 done);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.sm_generator.generate(assertion)
        cocotb_assertion = self.cocotb_generator.generate(assertion, sm)
        
        # Check that implication logic is generated
        assert "antecedent" in cocotb_assertion.code.lower() or "|->" in cocotb_assertion.code
        assert "consequent" in cocotb_assertion.code.lower()


if __name__ == "__main__":
    pytest.main([__file__])

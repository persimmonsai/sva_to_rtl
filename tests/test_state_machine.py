"""
Test cases for State Machine Generator
"""

import pytest
import sys
import os

# Add the parent directory to the path so we can import our modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from sva_to_rtl.parser import SVAParser
from sva_to_rtl.state_machine import StateMachineGenerator, StateType


class TestStateMachineGenerator:
    def setup_method(self):
        """Setup test fixtures"""
        self.parser = SVAParser()
        self.generator = StateMachineGenerator()
    
    def test_generate_simple_state_machine(self):
        """Test generating state machine from simple assertion"""
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.generator.generate(assertion)
        
        assert sm.name == "basic_assert_checker"
        assert sm.clock == "clk"
        assert sm.initial_state == "IDLE"
        assert "IDLE" in sm.states
        assert "SUCCESS" in sm.states
        assert "FAILURE" in sm.states
    
    def test_generate_delayed_state_machine(self):
        """Test generating state machine with delays"""
        assertion_text = "delay_assert: assert property (@(posedge clk) a |-> ##1 b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.generator.generate(assertion)
        
        # Should have more states due to delay
        assert len(sm.states) >= 3  # At least IDLE, SUCCESS, FAILURE
    
    def test_extract_signals(self):
        """Test signal extraction from assertions"""
        assertion_text = "multi_sig: assert property (@(posedge clk) (sig1 && sig2) |-> sig3);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.generator.generate(assertion)
        
        # Check that signals are extracted
        assert len(sm.signals) > 0
    
    def test_optimize_state_machine(self):
        """Test state machine optimization"""
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        assertion = self.parser.parse_assertion(assertion_text)
        
        sm = self.generator.generate(assertion)
        optimized_sm = self.generator.optimize_state_machine(sm)
        
        # Optimized version should have same or fewer states
        assert len(optimized_sm.states) <= len(sm.states)
    
    def test_generate_multiple_state_machines(self):
        """Test generating multiple state machines"""
        text = """
        assert1: assert property (@(posedge clk) a |-> b);
        assert2: assert property (@(posedge clk) c |-> d);
        """
        
        assertions = self.parser.parse_text(text)
        state_machines = self.generator.generate_multiple(assertions)
        
        assert len(state_machines) == 2
        assert all(sm.clock == "clk" for sm in state_machines.values())
    
    def test_tokenize_expression(self):
        """Test expression tokenization"""
        expression = "a |-> ##1 b"
        tokens = self.generator._tokenize_expression(expression)
        
        assert "a" in tokens
        assert "|->" in tokens
        assert "##1" in tokens
        assert "b" in tokens
    
    def test_signal_detection(self):
        """Test signal detection in tokens"""
        assert self.generator._is_signal("signal_name") == True
        assert self.generator._is_signal("signal[0]") == True
        assert self.generator._is_signal("(a && b)") == True
        assert self.generator._is_signal("|->") == False
        assert self.generator._is_signal("##1") == False


if __name__ == "__main__":
    pytest.main([__file__])

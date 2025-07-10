"""
Test cases for SVA Parser
"""

import pytest
import sys
import os

# Add the parent directory to the path so we can import our modules
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))

from sva_to_rtl.parser import SVAParser, SVAAssertion, SVAProperty, SVASequence


class TestSVAParser:
    def setup_method(self):
        """Setup test fixtures"""
        self.parser = SVAParser()
    
    def test_parse_simple_assertion(self):
        """Test parsing a simple assertion"""
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        
        assertion = self.parser.parse_assertion(assertion_text)
        
        assert assertion.name == "basic_assert"
        assert assertion.property.property_type == "assert"
        assert assertion.property.sequence.expression == "a |-> b"
        assert assertion.property.sequence.clock == "clk"
    
    def test_parse_delayed_assertion(self):
        """Test parsing assertion with delay"""
        assertion_text = "delay_assert: assert property (@(posedge clk) a |-> ##1 b);"
        
        assertion = self.parser.parse_assertion(assertion_text)
        
        assert assertion.name == "delay_assert"
        assert "##1" in assertion.property.sequence.expression
    
    def test_parse_cover_property(self):
        """Test parsing cover property"""
        assertion_text = "cover_example: cover property (@(posedge clk) a && b);"
        
        assertion = self.parser.parse_assertion(assertion_text)
        
        assert assertion.name == "cover_example"
        assert assertion.property.property_type == "cover"
        assert assertion.property.sequence.expression == "a && b"
    
    def test_parse_assume_property(self):
        """Test parsing assume property"""
        assertion_text = "assume_example: assume property (@(posedge clk) a |-> ##1 b);"
        
        assertion = self.parser.parse_assertion(assertion_text)
        
        assert assertion.name == "assume_example"
        assert assertion.property.property_type == "assume"
    
    def test_parse_multiple_assertions(self):
        """Test parsing multiple assertions from text"""
        text = """
        basic_assert: assert property (@(posedge clk) a |-> b);
        cover_example: cover property (@(posedge clk) a && b);
        assume_example: assume property (@(posedge clk) a |-> ##1 b);
        """
        
        assertions = self.parser.parse_text(text)
        
        assert len(assertions) == 3
        assert assertions[0].property.property_type == "assert"
        assert assertions[1].property.property_type == "cover"
        assert assertions[2].property.property_type == "assume"
    
    def test_parse_with_disable_condition(self):
        """Test parsing assertion with disable condition"""
        assertion_text = "reset_check: assert property (@(posedge clk) disable iff (!rst_n) valid |-> ##1 out_valid);"
        
        assertion = self.parser.parse_assertion(assertion_text)
        
        assert assertion.name == "reset_check"
        # Note: disable condition parsing needs to be implemented in the parser
    
    def test_clean_text(self):
        """Test text cleaning functionality"""
        text_with_comments = """
        // This is a comment
        basic_assert: assert property (@(posedge clk) a |-> b); // inline comment
        /* multi-line
           comment */
        """
        
        cleaned = self.parser._clean_text(text_with_comments)
        
        assert "//" not in cleaned
        assert "/*" not in cleaned
        assert "basic_assert" in cleaned
    
    def test_extract_clock(self):
        """Test clock extraction"""
        text = "@(posedge clk) a |-> b"
        clock = self.parser._extract_clock(text)
        assert clock == "clk"
        
        text = "@(negedge clk_n) a |-> b"
        clock = self.parser._extract_clock(text)
        assert clock == "~clk_n"
    
    def test_invalid_assertion(self):
        """Test handling of invalid assertion syntax"""
        invalid_text = "invalid syntax here"
        
        with pytest.raises(ValueError):
            self.parser.parse_assertion(invalid_text)


if __name__ == "__main__":
    pytest.main([__file__])

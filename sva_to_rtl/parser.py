"""
SystemVerilog Assertion (SVA) Parser

This module parses SystemVerilog assertion syntax and converts it into
an abstract syntax tree (AST) for further processing.
"""

import re
from typing import Dict, List, Optional, Union, Any
from dataclasses import dataclass
from enum import Enum


class SVAOperator(Enum):
    """SVA sequence operators"""
    IMPLICATION = "|->"
    OVERLAY_IMPLICATION = "|=>"
    THROUGHOUT = "throughout"
    WITHIN = "within"
    INTERSECT = "intersect"
    FIRST_MATCH = "first_match"
    AND = "and"
    OR = "or"
    NOT = "not"
    DELAY = "##"
    CONSECUTIVE_REPEAT = "[*]"
    GOTO_REPEAT = "[->]"
    NON_CONSECUTIVE_REPEAT = "[=]"


@dataclass
class SVASequence:
    """Represents an SVA sequence"""
    name: str
    expression: str
    clock: Optional[str] = None
    reset: Optional[str] = None
    disable_condition: Optional[str] = None


@dataclass
class SVAProperty:
    """Represents an SVA property"""
    name: str
    sequence: SVASequence
    property_type: str = "assert"  # assert, assume, cover
    clock: Optional[str] = None
    reset: Optional[str] = None
    disable_condition: Optional[str] = None


@dataclass
class SVAAssertion:
    """Represents a complete SVA assertion"""
    name: str
    property: SVAProperty
    label: Optional[str] = None
    severity: str = "error"  # error, warning, info


class SVAParser:
    """Parser for SystemVerilog Assertions"""
    
    def __init__(self):
        self.sequences: Dict[str, SVASequence] = {}
        self.properties: Dict[str, SVAProperty] = {}
        self.assertions: Dict[str, SVAAssertion] = {}
        
    def parse_sequence(self, sequence_text: str) -> SVASequence:
        """Parse a sequence definition"""
        # Remove comments and normalize whitespace
        clean_text = self._clean_text(sequence_text)
        
        # Extract sequence name and body
        sequence_match = re.search(r'sequence\s+(\w+)(?:\s*\(.*?\))?\s*;(.*?)endsequence', 
                                 clean_text, re.DOTALL)
        
        if not sequence_match:
            raise ValueError(f"Invalid sequence syntax: {sequence_text}")
            
        name = sequence_match.group(1)
        body = sequence_match.group(2).strip()
        
        # Extract clock and reset if present
        clock = self._extract_clock(clean_text)
        reset = self._extract_reset(clean_text)
        disable_condition = self._extract_disable_condition(clean_text)
        
        sequence = SVASequence(
            name=name,
            expression=body,
            clock=clock,
            reset=reset,
            disable_condition=disable_condition
        )
        
        self.sequences[name] = sequence
        return sequence
    
    def parse_property(self, property_text: str) -> SVAProperty:
        """Parse a property definition"""
        clean_text = self._clean_text(property_text)
        
        # Extract property name and body
        property_match = re.search(r'property\s+(\w+)(?:\s*\(.*?\))?\s*;(.*?)endproperty', 
                                 clean_text, re.DOTALL)
        
        if not property_match:
            raise ValueError(f"Invalid property syntax: {property_text}")
            
        name = property_match.group(1)
        body = property_match.group(2).strip()
        
        # Parse the property body to extract sequence
        sequence = self._parse_property_body(body)
        
        # Extract clock and reset if present
        clock = self._extract_clock(clean_text)
        reset = self._extract_reset(clean_text)
        disable_condition = self._extract_disable_condition(clean_text)
        
        property_obj = SVAProperty(
            name=name,
            sequence=sequence,
            clock=clock,
            reset=reset,
            disable_condition=disable_condition
        )
        
        self.properties[name] = property_obj
        return property_obj
    
    def parse_assertion(self, assertion_text: str) -> SVAAssertion:
        """Parse an assertion statement"""
        clean_text = self._clean_text(assertion_text)
        
        # Match different assertion types
        assert_match = re.search(r'(assert|assume|cover)\s+property\s*\(\s*(@\([^)]+\))?\s*([^)]+)\s*\)', 
                               clean_text)
        
        if not assert_match:
            raise ValueError(f"Invalid assertion syntax: {assertion_text}")
            
        assertion_type = assert_match.group(1)
        clock_expr = assert_match.group(2)
        property_expr = assert_match.group(3)
        
        # Extract label if present
        label_match = re.search(r'(\w+)\s*:', clean_text)
        label = label_match.group(1) if label_match else None
        
        # Create a property from the expression
        sequence = SVASequence(
            name="inline_seq",
            expression=property_expr,
            clock=self._extract_clock_from_expr(clock_expr) if clock_expr else None
        )
        
        property_obj = SVAProperty(
            name="inline_prop",
            sequence=sequence,
            property_type=assertion_type
        )
        
        assertion_name = label or f"{assertion_type}_assertion"
        assertion = SVAAssertion(
            name=assertion_name,
            property=property_obj,
            label=label,
            severity="error"
        )
        
        self.assertions[assertion_name] = assertion
        return assertion
    
    def parse_file(self, filename: str) -> List[SVAAssertion]:
        """Parse a SystemVerilog file containing SVA assertions"""
        with open(filename, 'r') as f:
            content = f.read()
        
        return self.parse_text(content)
    
    def parse_text(self, text: str) -> List[SVAAssertion]:
        """Parse SVA assertions from text"""
        assertions = []
        
        # Find all sequence definitions
        for match in re.finditer(r'sequence\s+\w+.*?endsequence', text, re.DOTALL):
            try:
                self.parse_sequence(match.group(0))
            except ValueError as e:
                print(f"Warning: Failed to parse sequence: {e}")
        
        # Find all property definitions
        for match in re.finditer(r'property\s+\w+.*?endproperty', text, re.DOTALL):
            try:
                self.parse_property(match.group(0))
            except ValueError as e:
                print(f"Warning: Failed to parse property: {e}")
        
        # Find all assertion statements
        for match in re.finditer(r'(?:(\w+)\s*:)?\s*(assert|assume|cover)\s+property\s*\([^;]+\);', text):
            try:
                assertion = self.parse_assertion(match.group(0))
                assertions.append(assertion)
            except ValueError as e:
                print(f"Warning: Failed to parse assertion: {e}")
        
        return assertions
    
    def _clean_text(self, text: str) -> str:
        """Clean and normalize text"""
        # Remove single-line comments
        text = re.sub(r'//.*$', '', text, flags=re.MULTILINE)
        
        # Remove multi-line comments
        text = re.sub(r'/\*.*?\*/', '', text, flags=re.DOTALL)
        
        # Normalize whitespace
        text = re.sub(r'\s+', ' ', text)
        
        return text.strip()
    
    def _extract_clock(self, text: str) -> Optional[str]:
        """Extract clock signal from text"""
        clock_match = re.search(r'@\s*\(\s*posedge\s+(\w+)', text)
        if clock_match:
            return clock_match.group(1)
        
        clock_match = re.search(r'@\s*\(\s*negedge\s+(\w+)', text)
        if clock_match:
            return f"~{clock_match.group(1)}"
        
        return None
    
    def _extract_reset(self, text: str) -> Optional[str]:
        """Extract reset signal from text"""
        reset_match = re.search(r'reset\s*\(\s*(\w+)\s*\)', text)
        if reset_match:
            return reset_match.group(1)
        
        return None
    
    def _extract_disable_condition(self, text: str) -> Optional[str]:
        """Extract disable condition from text"""
        disable_match = re.search(r'disable\s+iff\s*\(\s*([^)]+)\s*\)', text)
        if disable_match:
            return disable_match.group(1)
        
        return None
    
    def _extract_clock_from_expr(self, clock_expr: str) -> Optional[str]:
        """Extract clock from clock expression"""
        if not clock_expr:
            return None
        
        clock_match = re.search(r'posedge\s+(\w+)', clock_expr)
        if clock_match:
            return clock_match.group(1)
        
        clock_match = re.search(r'negedge\s+(\w+)', clock_expr)
        if clock_match:
            return f"~{clock_match.group(1)}"
        
        return None
    
    def _parse_property_body(self, body: str) -> SVASequence:
        """Parse property body to extract sequence"""
        # For now, treat the entire body as a sequence expression
        # This could be enhanced to handle more complex property structures
        return SVASequence(
            name="property_sequence",
            expression=body
        )
    
    def get_parsed_data(self) -> Dict[str, Any]:
        """Get all parsed data"""
        return {
            "sequences": self.sequences,
            "properties": self.properties,
            "assertions": self.assertions
        }

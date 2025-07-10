"""
SystemVerilog SVA to RTL State Machine Generator

This tool translates SystemVerilog Assertion (SVA) syntax into synthesizable
SystemVerilog state machines that implement the assertion checks at simulation time.
"""

__version__ = "1.0.0"
__author__ = "SVA to RTL Tool"

# Import classes only when needed to avoid circular imports
try:
    from .parser import SVAParser
    from .state_machine import StateMachineGenerator
    from .rtl_generator import RTLGenerator
    from .cli import main
except ImportError:
    # Handle import errors gracefully
    pass

__all__ = ["SVAParser", "StateMachineGenerator", "RTLGenerator", "main"]

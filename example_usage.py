#!/usr/bin/env python3
"""
Example usage of the SVA to RTL Tool
"""

import os
import sys
from pathlib import Path

# Add the project root to Python path
project_root = Path(__file__).parent
sys.path.insert(0, str(project_root))

from sva_to_rtl.parser import SVAParser
from sva_to_rtl.state_machine import StateMachineGenerator
from sva_to_rtl.rtl_generator import RTLGenerator

def main():
    """Example usage of the SVA to RTL tool"""
    
    print("SVA to RTL Translation Tool - Example Usage")
    print("=" * 50)
    
    # Example 1: Parse a simple assertion
    print("\n1. Parsing a simple assertion:")
    print("-" * 30)
    
    parser = SVAParser()
    assertion_text = "req_ack: assert property (@(posedge clk) req |-> ##1 ack);"
    
    try:
        assertion = parser.parse_assertion(assertion_text)
        print(f"✓ Parsed assertion: {assertion.name}")
        print(f"  Type: {assertion.property.property_type}")
        print(f"  Expression: {assertion.property.sequence.expression}")
        print(f"  Clock: {assertion.property.sequence.clock}")
        
        # Example 2: Generate state machine
        print("\n2. Generating state machine:")
        print("-" * 30)
        
        sm_generator = StateMachineGenerator()
        sm = sm_generator.generate(assertion)
        
        print(f"✓ Generated state machine: {sm.name}")
        print(f"  States: {len(sm.states)}")
        print(f"  Transitions: {len(sm.transitions)}")
        print(f"  Signals: {sorted(sm.signals)}")
        
        # Example 3: Generate RTL
        print("\n3. Generating RTL:")
        print("-" * 30)
        
        rtl_generator = RTLGenerator()
        rtl_module = rtl_generator.generate(sm)
        
        print(f"✓ Generated RTL module: {rtl_module.name}")
        print(f"  Ports: {len(rtl_module.ports)}")
        print(f"  Internal signals: {len(rtl_module.signals)}")
        
        # Example 4: Save to file
        print("\n4. Saving RTL to file:")
        print("-" * 30)
        
        output_dir = project_root / "example_output"
        output_dir.mkdir(exist_ok=True)
        
        rtl_file = output_dir / f"{rtl_module.name}.sv"
        rtl_generator.save_module(rtl_module, str(rtl_file))
        
        print(f"✓ Saved RTL to: {rtl_file}")
        
        # Example 5: Generate testbench
        print("\n5. Generating testbench:")
        print("-" * 30)
        
        tb_content = rtl_generator.generate_testbench(rtl_module)
        tb_file = output_dir / f"{rtl_module.name}_tb.sv"
        
        with open(tb_file, 'w') as f:
            f.write(tb_content)
        
        print(f"✓ Saved testbench to: {tb_file}")
        
        # Example 6: Process multiple assertions
        print("\n6. Processing multiple assertions:")
        print("-" * 30)
        
        multi_sva_text = """
        handshake: assert property (@(posedge clk) req |-> ##1 ack);
        data_valid: assert property (@(posedge clk) valid |-> ##2 ready);
        reset_check: cover property (@(posedge clk) rst_n);
        """
        
        assertions = parser.parse_text(multi_sva_text)
        print(f"✓ Parsed {len(assertions)} assertions")
        
        state_machines = sm_generator.generate_multiple(assertions)
        print(f"✓ Generated {len(state_machines)} state machines")
        
        rtl_modules = rtl_generator.generate_multiple(state_machines)
        print(f"✓ Generated {len(rtl_modules)} RTL modules")
        
        # Save all modules
        for name, module in rtl_modules.items():
            module_file = output_dir / f"{name}.sv"
            rtl_generator.save_module(module, str(module_file))
            print(f"  - Saved: {module_file.name}")
        
        print("\n" + "=" * 50)
        print("Example completed successfully!")
        print(f"Check the '{output_dir}' directory for generated files.")
        
    except Exception as e:
        print(f"✗ Error: {e}")
        import traceback
        traceback.print_exc()

if __name__ == "__main__":
    main()

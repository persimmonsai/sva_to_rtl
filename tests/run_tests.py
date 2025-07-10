# Test runner script
import os
import sys

# Add the parent directory to the path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

# Simple test runner without pytest
def run_tests():
    """Run all tests"""
    
    print("Running SVA to RTL Tool Tests")
    print("=" * 40)
    
    # Test basic functionality
    try:
        from sva_to_rtl.parser import SVAParser
        from sva_to_rtl.state_machine import StateMachineGenerator
        from sva_to_rtl.rtl_generator import RTLGenerator
        from sva_to_rtl.cocotb_generator import CocotbGenerator
        
        print("✓ All modules imported successfully")
        
        # Test parser
        parser = SVAParser()
        assertion_text = "basic_assert: assert property (@(posedge clk) a |-> b);"
        assertion = parser.parse_assertion(assertion_text)
        print(f"✓ Parser test passed: {assertion.name}")
        
        # Test state machine generator
        sm_generator = StateMachineGenerator()
        sm = sm_generator.generate(assertion)
        print(f"✓ State machine generator test passed: {sm.name}")
        
        # Test RTL generator
        rtl_generator = RTLGenerator()
        rtl_module = rtl_generator.generate(sm)
        print(f"✓ RTL generator test passed: {rtl_module.name}")
        
        # Test cocotb generator
        cocotb_generator = CocotbGenerator()
        cocotb_assertion = cocotb_generator.generate(assertion, sm)
        print(f"✓ Cocotb generator test passed: {cocotb_assertion.class_name}")
        
        # Test complete flow
        test_text = """
        assert1: assert property (@(posedge clk) req |-> ##1 ack);
        assert2: cover property (@(posedge clk) valid && ready);
        """
        
        assertions = parser.parse_text(test_text)
        state_machines = sm_generator.generate_multiple(assertions)
        rtl_modules = rtl_generator.generate_multiple(state_machines)
        cocotb_assertions = cocotb_generator.generate_multiple(assertions, state_machines)
        
        print(f"✓ Complete flow test passed: {len(rtl_modules)} RTL modules, {len(cocotb_assertions)} cocotb assertions generated")
        
        print("\n" + "=" * 40)
        print("All tests passed successfully!")
        
    except Exception as e:
        print(f"✗ Test failed: {e}")
        import traceback
        traceback.print_exc()
        return False
    
    return True

if __name__ == "__main__":
    success = run_tests()
    sys.exit(0 if success else 1)

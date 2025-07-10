#!/usr/bin/env python3
"""
Demonstration script for the SVA to RTL Translation Tool
"""

import os
import sys
import subprocess
from pathlib import Path

def run_demo():
    """Run demonstration of the SVA to RTL tool"""
    
    print("=" * 60)
    print("  SystemVerilog Assertion to RTL Translation Tool Demo")
    print("=" * 60)
    print()
    
    # Set up paths
    base_dir = Path(__file__).parent
    python_path = "python" 
    output_dir = base_dir / "demo_output"
    
    # Environment setup
    env = os.environ.copy()
    env["PYTHONPATH"] = str(base_dir)
    
    # Clean up previous demo output
    if output_dir.exists():
        import shutil
        shutil.rmtree(output_dir)
    
    print("1. Analyzing simple assertions...")
    print("-" * 40)
    
    # Run analysis
    result = subprocess.run([
        str(python_path), "-m", "sva_to_rtl.cli", "analyze", 
        "examples/simple_assertions.sv"
    ], env=env, capture_output=True, text=True, cwd=str(base_dir))
    
    print(result.stdout)
    
    print("\n2. Translating assertions to RTL...")
    print("-" * 40)
    
    # Run translation
    result = subprocess.run([
        str(python_path), "-m", "sva_to_rtl.cli", "translate", 
        "examples/simple_assertions.sv", "-o", "demo_output", "-t", "-v"
    ], env=env, capture_output=True, text=True, cwd=str(base_dir))
    
    print(result.stdout)
    
    print("\n3. Generated files:")
    print("-" * 40)
    
    # List generated files
    if output_dir.exists():
        for file in sorted(output_dir.glob("*.sv")):
            print(f"  - {file.name}")
        
        # Show a sample RTL file
        rtl_files = list(output_dir.glob("*_rtl.sv"))
        if rtl_files:
            print(f"\n4. Sample generated RTL ({rtl_files[0].name}):")
            print("-" * 40)
            with open(rtl_files[0], 'r') as f:
                lines = f.readlines()
                for i, line in enumerate(lines[:30]):  # Show first 30 lines
                    print(f"{i+1:2d}: {line.rstrip()}")
                if len(lines) > 30:
                    print(f"    ... ({len(lines) - 30} more lines)")
    
    print("\n5. Testing single assertion translation...")
    print("-" * 40)
    
    # Test single assertion
    result = subprocess.run([
        str(python_path), "-m", "sva_to_rtl.cli", "text", 
        "test_assert: assert property (@(posedge clk) req |-> ##1 ack);",
        "-o", "demo_output", "-m", "test_assertion"
    ], env=env, capture_output=True, text=True, cwd=str(base_dir))
    
    print(result.stdout)
    
    print("\n" + "=" * 60)
    print("Demo completed! Check the 'demo_output' directory for generated files.")
    print("=" * 60)

if __name__ == "__main__":
    run_demo()

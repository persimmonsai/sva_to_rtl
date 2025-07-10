"""
Command Line Interface for SVA to RTL Tool

This module provides a command-line interface for translating SVA assertions
to synthesizable RTL state machines.
"""

import click
import os
import sys
from typing import List, Optional
from pathlib import Path

from .parser import SVAParser
from .state_machine import StateMachineGenerator
from .rtl_generator import RTLGenerator
from .cocotb_generator import CocotbGenerator


@click.command()
@click.argument('input_file', type=click.Path(exists=True))
@click.option('--output-dir', '-o', type=click.Path(), default='output',
              help='Output directory for generated RTL files')
@click.option('--module-prefix', '-p', type=str, default='sva_checker',
              help='Prefix for generated module names')
@click.option('--generate-testbench', '-t', is_flag=True,
              help='Generate testbench files')
@click.option('--generate-cocotb', '--cocotb', is_flag=True,
              help='Generate cocotb Python test files')
@click.option('--optimize', is_flag=True,
              help='Optimize generated state machines')
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
@click.option('--clock-name', '-c', type=str, default='clk',
              help='Default clock signal name')
@click.option('--reset-name', '-r', type=str, default='rst_n',
              help='Default reset signal name')
@click.option('--list-assertions', '-l', is_flag=True,
              help='List all found assertions without generating RTL')
def main(input_file: str, output_dir: str, module_prefix: str, 
         generate_testbench: bool, generate_cocotb: bool, optimize: bool, verbose: bool,
         clock_name: str, reset_name: str, list_assertions: bool):
    """
    SVA to RTL Translation Tool
    
    Translates SystemVerilog Assertions (SVA) to synthesizable RTL state machines.
    
    INPUT_FILE: SystemVerilog file containing SVA assertions
    """
    
    if verbose:
        click.echo(f"Processing file: {input_file}")
    
    try:
        # Parse SVA assertions
        parser = SVAParser()
        assertions = parser.parse_file(input_file)
        
        if not assertions:
            click.echo("No SVA assertions found in the input file.", err=True)
            sys.exit(1)
        
        if verbose:
            click.echo(f"Found {len(assertions)} assertion(s)")
        
        # List assertions if requested
        if list_assertions:
            click.echo("Found assertions:")
            for assertion in assertions:
                click.echo(f"  - {assertion.name} ({assertion.property.property_type})")
                click.echo(f"    Expression: {assertion.property.sequence.expression}")
                click.echo()
            return
        
        # Generate state machines
        sm_generator = StateMachineGenerator()
        state_machines = sm_generator.generate_multiple(assertions)
        
        if verbose:
            click.echo(f"Generated {len(state_machines)} state machine(s)")
        
        # Optimize state machines if requested
        if optimize:
            if verbose:
                click.echo("Optimizing state machines...")
            optimized_sms = {}
            for name, sm in state_machines.items():
                optimized_sms[name] = sm_generator.optimize_state_machine(sm)
            state_machines = optimized_sms
        
        # Generate RTL
        rtl_generator = RTLGenerator()
        rtl_modules = rtl_generator.generate_multiple(state_machines)
        
        if verbose:
            click.echo(f"Generated {len(rtl_modules)} RTL module(s)")
        
        # Generate cocotb tests if requested
        cocotb_assertions = {}
        if generate_cocotb:
            cocotb_generator = CocotbGenerator()
            cocotb_assertions = cocotb_generator.generate_multiple(assertions, state_machines)
            
            if verbose:
                click.echo(f"Generated {len(cocotb_assertions)} cocotb assertion(s)")
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Save RTL modules
        for module_name, module in rtl_modules.items():
            output_file = output_path / f"{module_name}.sv"
            rtl_generator.save_module(module, str(output_file))
            
            if verbose:
                click.echo(f"Saved RTL module: {output_file}")
            
            # Generate testbench if requested
            if generate_testbench:
                tb_content = rtl_generator.generate_testbench(module)
                tb_file = output_path / f"{module_name}_tb.sv"
                with open(tb_file, 'w') as f:
                    f.write(tb_content)
                
                if verbose:
                    click.echo(f"Saved testbench: {tb_file}")
        
        # Generate cocotb test files if requested
        if generate_cocotb and cocotb_assertions:
            cocotb_file = output_path / "test_sva_assertions.py"
            cocotb_generator.save_test_file(list(cocotb_assertions.values()), str(cocotb_file))
            
            if verbose:
                click.echo(f"Saved cocotb test file: {cocotb_file}")
        
        # Generate summary report
        report_file = output_path / "translation_report.txt"
        generate_report(assertions, state_machines, rtl_modules, str(report_file), cocotb_assertions)
        
        if verbose:
            click.echo(f"Generated report: {report_file}")
        
        click.echo(f"Translation completed successfully!")
        click.echo(f"Output files saved to: {output_path}")
        
    except Exception as e:
        click.echo(f"Error: {e}", err=True)
        if verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


@click.command()
@click.argument('assertion_text', type=str)
@click.option('--output-dir', '-o', type=click.Path(), default='output',
              help='Output directory for generated RTL files')
@click.option('--module-name', '-m', type=str, default='sva_checker',
              help='Name for generated module')
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
def translate_text(assertion_text: str, output_dir: str, module_name: str, verbose: bool):
    """
    Translate a single SVA assertion from command line text
    
    ASSERTION_TEXT: SVA assertion text to translate
    """
    
    if verbose:
        click.echo(f"Processing assertion: {assertion_text}")
    
    try:
        # Parse assertion
        parser = SVAParser()
        assertions = parser.parse_text(assertion_text)
        
        if not assertions:
            click.echo("No valid SVA assertion found in the input text.", err=True)
            sys.exit(1)
        
        # Use the first assertion
        assertion = assertions[0]
        assertion.name = module_name
        
        # Generate state machine
        sm_generator = StateMachineGenerator()
        sm = sm_generator.generate(assertion)
        
        # Generate RTL
        rtl_generator = RTLGenerator()
        rtl_module = rtl_generator.generate(sm)
        
        # Create output directory
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Save RTL module
        output_file = output_path / f"{rtl_module.name}.sv"
        rtl_generator.save_module(rtl_module, str(output_file))
        
        click.echo(f"RTL module saved to: {output_file}")
        
        # Print module content to console if verbose
        if verbose:
            click.echo("\nGenerated RTL:")
            click.echo(rtl_module.to_string())
        
    except Exception as e:
        click.echo(f"Error: {e}", err=True)
        if verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


@click.command()
@click.argument('input_file', type=click.Path(exists=True))
@click.option('--verbose', '-v', is_flag=True,
              help='Enable verbose output')
def analyze(input_file: str, verbose: bool):
    """
    Analyze SVA assertions in a file without generating RTL
    
    INPUT_FILE: SystemVerilog file containing SVA assertions
    """
    
    try:
        # Parse SVA assertions
        parser = SVAParser()
        assertions = parser.parse_file(input_file)
        
        if not assertions:
            click.echo("No SVA assertions found in the input file.")
            return
        
        click.echo(f"Analysis of {input_file}")
        click.echo("=" * 50)
        
        for i, assertion in enumerate(assertions, 1):
            click.echo(f"\n{i}. Assertion: {assertion.name}")
            click.echo(f"   Type: {assertion.property.property_type}")
            click.echo(f"   Expression: {assertion.property.sequence.expression}")
            
            if assertion.property.clock:
                click.echo(f"   Clock: {assertion.property.clock}")
            
            if assertion.property.reset:
                click.echo(f"   Reset: {assertion.property.reset}")
            
            if assertion.property.disable_condition:
                click.echo(f"   Disable: {assertion.property.disable_condition}")
            
            if verbose:
                # Generate state machine for analysis
                sm_generator = StateMachineGenerator()
                sm = sm_generator.generate(assertion)
                
                click.echo(f"   State Machine Analysis:")
                click.echo(f"     - States: {len(sm.states)}")
                click.echo(f"     - Transitions: {len(sm.transitions)}")
                click.echo(f"     - Signals: {len(sm.signals)}")
                
                if sm.signals:
                    click.echo(f"     - Signal list: {', '.join(sorted(sm.signals))}")
        
        click.echo(f"\nTotal assertions found: {len(assertions)}")
        
    except Exception as e:
        click.echo(f"Error: {e}", err=True)
        if verbose:
            import traceback
            traceback.print_exc()
        sys.exit(1)


def generate_report(assertions, state_machines, rtl_modules, report_file, cocotb_assertions=None):
    """Generate a detailed translation report"""
    
    with open(report_file, 'w') as f:
        f.write("SVA to RTL Translation Report\n")
        f.write("=" * 50 + "\n\n")
        
        # Summary
        f.write("SUMMARY\n")
        f.write("-" * 20 + "\n")
        f.write(f"Total assertions processed: {len(assertions)}\n")
        f.write(f"State machines generated: {len(state_machines)}\n")
        f.write(f"RTL modules generated: {len(rtl_modules)}\n")
        if cocotb_assertions:
            f.write(f"Cocotb assertions generated: {len(cocotb_assertions)}\n")
        f.write("\n")
        
        # Assertion details
        f.write("ASSERTION DETAILS\n")
        f.write("-" * 20 + "\n")
        
        for assertion in assertions:
            f.write(f"Assertion: {assertion.name}\n")
            f.write(f"  Type: {assertion.property.property_type}\n")
            f.write(f"  Expression: {assertion.property.sequence.expression}\n")
            
            if assertion.property.clock:
                f.write(f"  Clock: {assertion.property.clock}\n")
            
            if assertion.property.reset:
                f.write(f"  Reset: {assertion.property.reset}\n")
            
            f.write("\n")
        
        # State machine details
        f.write("STATE MACHINE DETAILS\n")
        f.write("-" * 20 + "\n")
        
        for sm_name, sm in state_machines.items():
            f.write(f"State Machine: {sm_name}\n")
            f.write(f"  States: {len(sm.states)}\n")
            f.write(f"  Transitions: {len(sm.transitions)}\n")
            f.write(f"  Signals: {len(sm.signals)}\n")
            f.write(f"  Signal list: {', '.join(sorted(sm.signals))}\n")
            f.write("\n")
        
        # RTL module details
        f.write("RTL MODULE DETAILS\n")
        f.write("-" * 20 + "\n")
        
        for module_name, module in rtl_modules.items():
            f.write(f"Module: {module_name}\n")
            f.write(f"  Ports: {len(module.ports)}\n")
            f.write(f"  Internal signals: {len(module.signals)}\n")
            f.write(f"  Parameters: {len(module.parameters)}\n")
            f.write("\n")
        
        # Cocotb assertion details
        if cocotb_assertions:
            f.write("COCOTB ASSERTION DETAILS\n")
            f.write("-" * 20 + "\n")
            
            for assertion_name, cocotb_assertion in cocotb_assertions.items():
                f.write(f"Cocotb Assertion: {assertion_name}\n")
                f.write(f"  Class: {cocotb_assertion.class_name}\n")
                f.write(f"  Clock: {cocotb_assertion.clock_name}\n")
                f.write(f"  Reset: {cocotb_assertion.reset_name}\n")
                f.write(f"  Signals: {len(cocotb_assertion.signals)}\n")
                f.write(f"  Signal list: {', '.join(sorted(cocotb_assertion.signals))}\n")
                f.write("\n")


# Create CLI group
@click.group()
@click.version_option(version='1.0.0')
def cli():
    """SVA to RTL Translation Tool"""
    pass


# Add commands to the group
cli.add_command(main, name='translate')
cli.add_command(translate_text, name='text')
cli.add_command(analyze, name='analyze')


if __name__ == '__main__':
    cli()

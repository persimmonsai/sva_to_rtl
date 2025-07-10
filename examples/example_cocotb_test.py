"""
Example cocotb test file for SVA assertions
This demonstrates how the generated cocotb tests work
"""

import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
from cocotb.result import TestFailure
import logging


class HandshakeChecker:
    """Cocotb assertion checker for: req |-> ##1 ack"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.HandshakeChecker')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.req = dut.req
        self.ack = dut.ack

    @cocotb.coroutine
    async def check_assertion(self):
        """Main assertion checking coroutine"""

        while True:
            try:
                await self._check_assertion_logic()
            except TestFailure as e:
                self.fail_count += 1
                self.logger.error(f'Assertion failed: {e}')
                if self.fail_count >= 10:  # Configurable threshold
                    raise
            except Exception as e:
                self.logger.error(f'Unexpected error: {e}')
                raise

            await RisingEdge(self.clock)

    @cocotb.coroutine
    async def _check_assertion_logic(self):
        """Core assertion checking logic"""

        # Check implication: req |-> ##1 ack
        if self._evaluate_condition('req'):
            self.assertion_count += 1
            self.logger.debug(f'Antecedent triggered: req')

            # Wait 1 clock cycles
            await self._wait_cycles(1)

            # Check consequent: ack
            if not self._evaluate_condition('ack'):
                self.fail_count += 1
                raise TestFailure(f'Assertion handshake failed: consequent not satisfied')
            else:
                self.pass_count += 1
                self.logger.info(f'Assertion handshake passed')

    @cocotb.coroutine
    async def _wait_cycles(self, cycles):
        """Wait for specified number of clock cycles"""
        for _ in range(cycles):
            await RisingEdge(self.clock)

    def _evaluate_condition(self, condition):
        """Evaluate a condition string against DUT signals"""
        try:
            # Replace signal names with actual values
            eval_str = condition
            
            # Handle common signal operations
            for signal_name in ['req', 'ack']:  # Known signals
                if signal_name in eval_str:
                    signal_value = getattr(self.dut, signal_name).value
                    eval_str = eval_str.replace(signal_name, str(int(signal_value)))
            
            # Handle SystemVerilog operators
            eval_str = eval_str.replace('&&', ' and ')
            eval_str = eval_str.replace('||', ' or ')
            eval_str = eval_str.replace('!', ' not ')
            
            # Evaluate the condition
            return eval(eval_str)
            
        except Exception as e:
            self.logger.error(f'Error evaluating condition "{condition}": {e}')
            return False


@cocotb.test()
async def test_handshake_example(dut):
    """Example test demonstrating SVA assertion checking"""
    
    # Initialize clock
    clock = Clock(dut.clk, 10, units='ns')
    cocotb.start_soon(clock.start())
    
    # Reset sequence
    if hasattr(dut, 'rst_n'):
        dut.rst_n.value = 0
        await Timer(100, units='ns')
        dut.rst_n.value = 1
        await Timer(100, units='ns')
    
    # Create assertion checker
    handshake_checker = HandshakeChecker(dut)
    
    # Start assertion checking
    checker_task = cocotb.start_soon(handshake_checker.check_assertion())
    
    # Test stimulus
    dut.req.value = 0
    dut.ack.value = 0
    await RisingEdge(dut.clk)
    
    # Test case 1: Valid handshake
    dut.req.value = 1
    await RisingEdge(dut.clk)
    dut.req.value = 0
    dut.ack.value = 1
    await RisingEdge(dut.clk)
    dut.ack.value = 0
    
    # Wait a bit
    await Timer(200, units='ns')
    
    # Test case 2: Another valid handshake
    dut.req.value = 1
    await RisingEdge(dut.clk)
    dut.req.value = 0
    dut.ack.value = 1
    await RisingEdge(dut.clk)
    dut.ack.value = 0
    
    # Wait for test to complete
    await Timer(500, units='ns')
    
    # Report results
    dut._log.info(f'Handshake assertion: {handshake_checker.pass_count} passed, {handshake_checker.fail_count} failed')
    
    # Stop checker
    checker_task.kill()

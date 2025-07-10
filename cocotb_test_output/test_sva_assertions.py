"""
Cocotb test file generated from SVA assertions
"""

from cocotb.clock import Clock
from cocotb.result import TestFailure
from cocotb.result import TestSuccess
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from enum import Enum
import cocotb
import logging


class Basic_AssertChecker:
    """Cocotb assertion checker for: a |-> b"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.{class_name}')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.a = dut.a
        self.b = dut.b

    class State(Enum):
        FAILURE = 0
        IDLE = 1
        S1 = 2
        S2 = 3
        SUCCESS = 4

        self.current_state = self.State.IDLE

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

        # Check implication: a |-> b
        if self._evaluate_condition('a'):
            self.assertion_count += 1
            self.logger.debug(f'Antecedent triggered: a')

            # Check consequent: b
            if not self._evaluate_condition('b'):
                self.fail_count += 1
                raise TestFailure(f'Assertion basic_assert failed: consequent not satisfied')
            else:
                self.pass_count += 1
                self.logger.info(f'Assertion basic_assert passed')

    def _evaluate_condition(self, condition):
        """Evaluate a condition string against DUT signals"""
        try:
            # Replace signal names with actual values
            eval_str = condition
            
            # Handle common signal operations
            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):
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


class Delay_AssertChecker:
    """Cocotb assertion checker for: a |-> ##1 b"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.{class_name}')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.a = dut.a
        self.b = dut.b

    class State(Enum):
        FAILURE = 0
        IDLE = 1
        S1 = 2
        S2 = 3
        SUCCESS = 4

        self.current_state = self.State.IDLE

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

        # Check implication: a |-> ##1 b
        if self._evaluate_condition('a'):
            self.assertion_count += 1
            self.logger.debug(f'Antecedent triggered: a')

            # Wait 1 clock cycles
            await self._wait_cycles(1)

            # Check consequent: b
            if not self._evaluate_condition('b'):
                self.fail_count += 1
                raise TestFailure(f'Assertion delay_assert failed: consequent not satisfied')
            else:
                self.pass_count += 1
                self.logger.info(f'Assertion delay_assert passed')

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
            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):
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


class Multi_DelayChecker:
    """Cocotb assertion checker for: a |-> ##3 b"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.{class_name}')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.a = dut.a
        self.b = dut.b

    class State(Enum):
        FAILURE = 0
        IDLE = 1
        S1 = 2
        S2 = 3
        SUCCESS = 4

        self.current_state = self.State.IDLE

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

        # Check implication: a |-> ##3 b
        if self._evaluate_condition('a'):
            self.assertion_count += 1
            self.logger.debug(f'Antecedent triggered: a')

            # Wait 3 clock cycles
            await self._wait_cycles(3)

            # Check consequent: b
            if not self._evaluate_condition('b'):
                self.fail_count += 1
                raise TestFailure(f'Assertion multi_delay failed: consequent not satisfied')
            else:
                self.pass_count += 1
                self.logger.info(f'Assertion multi_delay passed')

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
            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):
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


class Cover_ExampleChecker:
    """Cocotb assertion checker for: a && b"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.{class_name}')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.a = dut.a
        self.b = dut.b

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

        # Check boolean expression: a && b
        if self._evaluate_condition('a && b'):
            self.pass_count += 1
            self.logger.info(f'Cover point cover_example hit')

    def _evaluate_condition(self, condition):
        """Evaluate a condition string against DUT signals"""
        try:
            # Replace signal names with actual values
            eval_str = condition
            
            # Handle common signal operations
            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):
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


class Assume_ExampleChecker:
    """Cocotb assertion checker for: a |-> ##1 b"""

    def __init__(self, dut):
        self.dut = dut
        self.clock = dut.clk
        self.logger = logging.getLogger(f'cocotb.{class_name}')
        self.assertion_count = 0
        self.pass_count = 0
        self.fail_count = 0
        self.a = dut.a
        self.b = dut.b

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

        # Check implication: a |-> ##1 b
        if self._evaluate_condition('a'):
            self.assertion_count += 1
            self.logger.debug(f'Antecedent triggered: a')

            # Wait 1 clock cycles
            await self._wait_cycles(1)

            # Check consequent: b
            if not self._evaluate_condition('b'):
                self.logger.warning(f'Consequent not satisfied: {consequent_condition}')
            else:
                self.pass_count += 1
                self.logger.info(f'Assertion assume_example passed')

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
            for signal_name in sorted(self.dut._signals.keys(), key=len, reverse=True):
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
async def test_sva_assertions(dut):
    """Main test function that runs all SVA assertions"""

    # Initialize clock
    clock = Clock(dut.clk, 10, units='ns')
    cocotb.start_soon(clock.start())

    # Reset sequence
    dut.rst_n.value = 0
    await Timer(100, units='ns')
    dut.rst_n.value = 1
    await Timer(100, units='ns')

    # Create assertion checkers
    basic_assert_checker = Basic_AssertChecker(dut)
    delay_assert_checker = Delay_AssertChecker(dut)
    multi_delay_checker = Multi_DelayChecker(dut)
    cover_example_checker = Cover_ExampleChecker(dut)
    assume_example_checker = Assume_ExampleChecker(dut)

    # Start assertion checking
    checker_tasks = []
    checker_tasks.append(cocotb.start_soon(basic_assert_checker.check_assertion()))
    checker_tasks.append(cocotb.start_soon(delay_assert_checker.check_assertion()))
    checker_tasks.append(cocotb.start_soon(multi_delay_checker.check_assertion()))
    checker_tasks.append(cocotb.start_soon(cover_example_checker.check_assertion()))
    checker_tasks.append(cocotb.start_soon(assume_example_checker.check_assertion()))

    # Test stimulus - customize as needed
    await Timer(1000, units='ns')

    # Report results
    dut._log.info(f'basic_assert: {basic_assert_checker.pass_count} passed, {basic_assert_checker.fail_count} failed')
    dut._log.info(f'delay_assert: {delay_assert_checker.pass_count} passed, {delay_assert_checker.fail_count} failed')
    dut._log.info(f'multi_delay: {multi_delay_checker.pass_count} passed, {multi_delay_checker.fail_count} failed')
    dut._log.info(f'cover_example: {cover_example_checker.pass_count} passed, {cover_example_checker.fail_count} failed')
    dut._log.info(f'assume_example: {assume_example_checker.pass_count} passed, {assume_example_checker.fail_count} failed')
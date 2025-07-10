# Makefile for cocotb testing of SVA assertions
# This demonstrates how to run cocotb tests with generated assertions

# Default simulator
SIM ?= icarus

# Top-level module
TOPLEVEL = example_design

# Python test modules
MODULE = test_sva_assertions

# SystemVerilog source files
VERILOG_SOURCES = $(PWD)/examples/example_design.sv

# Include cocotb's make rules
include $(shell cocotb-config --makefiles)/Makefile.sim

# Additional targets
.PHONY: clean test-rtl test-cocotb

clean:
	rm -rf __pycache__
	rm -rf results.xml
	rm -rf sim_build
	rm -f *.vcd
	rm -f *.wlf

test-rtl:
	@echo "Testing RTL generation..."
	python -m sva_to_rtl.cli translate examples/simple_assertions.sv -o test_output -t

test-cocotb:
	@echo "Testing cocotb generation..."
	python -m sva_to_rtl.cli translate examples/simple_assertions.sv -o test_output -c

test-all: test-rtl test-cocotb
	@echo "Running complete test suite..."
	python tests/run_tests.py

help:
	@echo "Available targets:"
	@echo "  clean      - Clean build artifacts"
	@echo "  test-rtl   - Test RTL generation"
	@echo "  test-cocotb - Test cocotb generation"
	@echo "  test-all   - Run all tests"
	@echo "  help       - Show this help"

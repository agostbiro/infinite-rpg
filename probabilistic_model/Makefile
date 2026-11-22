.DEFAULT_GOAL := help
.PHONY: help install build run test verify benchmark

PYTHON ?= python3
PORT ?= 8093

help:
	@echo "Exact Graph Workshop (separate from the original RPG server)"
	@echo "make install   Fetch the pinned Lean cache and build the proofs (requires elan)."
	@echo "make run       Run the graph UI at http://127.0.0.1:$(PORT)/."
	@echo "make test      Run the Python unit tests; no server is started."
	@echo "make verify    Check Lean certificates, including deliberately invalid ones."
	@echo "make benchmark Verify a 60-node graph and record generation/checking times."
	@echo "Validation uses exact rational probabilities and Lean certificates."
	@echo "Profile: uniform Attack/Defend, static equipment, no timed item effects."

# Python uses only its standard library. Lean and mathlib stay at the pinned versions.
install:
	@$(PYTHON) -c 'import sys; assert sys.version_info >= (3, 9), "Python 3.9+ is required"'
	@command -v elan >/dev/null || { echo "Install elan, then rerun make install."; exit 1; }
	elan toolchain install $$(cat lean-toolchain)
	lake exe cache get
	$(MAKE) build

build:
	lake build

# Stop any server already using PORT before running this target.
run: build
	$(PYTHON) -u workshop/server.py --port $(PORT)

test:
	$(PYTHON) -m unittest discover -s workshop -p 'test_*.py'

# Run sequentially: do not launch multiple Lean checks in this project at once.
verify: build test
	$(PYTHON) -u workshop/check_support_certificate.py --output workshop/benchmarks/support-checks

benchmark: build
	$(PYTHON) -u workshop/benchmark.py --output workshop/benchmarks/60-nodes

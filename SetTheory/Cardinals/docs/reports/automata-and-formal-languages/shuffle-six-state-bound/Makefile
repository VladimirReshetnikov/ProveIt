PYTHON ?= python3
CXX ?= c++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra
CXXFLAGS20 ?= -O2 -std=c++20 -Wall -Wextra -pedantic

.PHONY: all check check-all check-binary check-cores check-residual \
        pdf enumerate search regenerate-residual clean

all: check pdf

# ---------------------------------------------------------------- database A
audit:
	mkdir -p audit

build:
	mkdir -p build

audit/coverage: src/coverage.cpp | audit
	$(CXX) $(CXXFLAGS) $< -o $@

# Route 1: two-stage check of database A (the default).
check: audit/coverage
	$(PYTHON) src/check_certificates.py
	./audit/coverage audit/verified_targets.tsv > audit/coverage.json
	$(PYTHON) src/test_suite.py
	$(PYTHON) src/negative_coverage_test.py

build/verify_all: src/verify_all.cpp | build
	$(CXX) $(CXXFLAGS) -pedantic $< -o $@

# Route 2: single self-contained binary over the same database.
check-binary: build/verify_all
	./build/verify_all data/certificates.txt
	$(PYTHON) src/test_artifacts.py ./build/verify_all
	$(PYTHON) src/test_construct_iterative.py

# ---------------------------------------------------------------- database B
build/verify: src/verify.cpp src/core_enumeration.hpp | build
	$(CXX) $(CXXFLAGS20) $< -o $@

build/enumerate_cores: src/enumerate_cores.cpp src/core_enumeration.hpp | build
	$(CXX) $(CXXFLAGS20) $< -o $@

# Route 3: verifier that also regenerates the canonical representative set.
check-cores: build/verify
	./build/verify certificates/cores.cert
	$(PYTHON) tests/verify_certificates.py
	$(PYTHON) tests/test_construction.py

# ---------------------------------------------------------------- database C
# Route 4: pure Python, no compiler required.
check-residual:
	cd residual && $(PYTHON) verify.py --json verification.json
	cd residual && $(PYTHON) test_construct.py

# Deterministic, solver-free regeneration of database C.
regenerate-residual:
	cd residual && $(CXX) $(CXXFLAGS) generate.cpp -o generate
	cd residual && ./generate > regenerated.tsv 2> regenerated.log
	cd residual && $(PYTHON) verify.py --certificates regenerated.tsv

# All four independent routes.
check-all: check check-binary check-cores check-residual

# -------------------------------------------------------------------- output
pdf:
	latexmk -pdf -interaction=nonstopmode shuffle_six_state.tex

# --------------------------------------------------- optional Z3 discovery
audit/enumerate_targets: src/enumerate_targets.cpp | audit
	$(CXX) $(CXXFLAGS) $< -o $@

enumerate: audit/enumerate_targets
	./audit/enumerate_targets audit/enumerated_targets.tsv 2> audit/enumeration.log

# Refuses to overwrite audit/regenerated_certificates.jsonl.
search: enumerate
	$(PYTHON) src/search_certificates.py

clean:
	latexmk -c shuffle_six_state.tex || true
	rm -f shuffle_six_state.aux shuffle_six_state.log shuffle_six_state.out shuffle_six_state.toc
	rm -f audit/coverage audit/enumerate_targets
	rm -rf build
	rm -f residual/generate residual/regenerated.tsv residual/regenerated.log

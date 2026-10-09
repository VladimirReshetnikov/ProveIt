PYTHON ?= python3
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17

.PHONY: all pdf verify tables exact-binaries clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error a275672.tex

verify:
	$(PYTHON) src/verify_results.py
	$(PYTHON) computations/constructions/scripts/verify_bundle.py

tables:
	$(PYTHON) src/make_result_tables.py

exact-binaries: build/rainbow_exact_v5 build/rainbow_edge_prefix

build:
	mkdir -p build

build/rainbow_exact_v5: computations/exact/rainbow_exact_v5.cpp | build
	$(CXX) $(CXXFLAGS) $< -o $@

build/rainbow_edge_prefix: computations/exact/rainbow_edge_prefix.cpp | build
	$(CXX) $(CXXFLAGS) $< -o $@

clean:
	latexmk -c a275672.tex

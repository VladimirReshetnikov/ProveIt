CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17
PROGRAMS = adaptive spread feasible_walk deep_walk complete

all: $(PROGRAMS:%=bin/%)

bin:
	mkdir -p bin

bin/%: src/%.cpp | bin
	$(CXX) $(CXXFLAGS) $< -o $@

verify:
	python3 scripts/verify_bundle.py

.PHONY: all verify

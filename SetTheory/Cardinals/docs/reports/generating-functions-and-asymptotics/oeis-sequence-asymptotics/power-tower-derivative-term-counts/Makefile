SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra -Wconversion
PYTHON ?= python3

.PHONY: all pdf clean \
        verify-xx verify-xx2 verify-xxx verify \
        exact modular certify

all: pdf

build:
	mkdir -p build

# ---------------------------------------------------------------- article ---
pdf: | build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	cp build/article.pdf article.pdf

# ------------------------------------------------- Part II: x^x, A293239 ---
# Note: verify.py rewrites data/python_report.json.
verify-xx:
	$(PYTHON) code/verify.py --max-n 1500
	$(PYTHON) code/verify_diagonals.py

build/verify_gmp: code/verify_gmp.cpp | build
	$(CXX) $(CXXFLAGS) $< -lgmp -o $@

# --------------------------------------------- Part III: x^(x^2), A290268 ---
# Note: these tee their run logs into data/, replacing the shipped copies.
build/verify_modular: code/verify_modular.cpp | build
	$(CXX) $(CXXFLAGS) $< -o $@

exact:
	$(PYTHON) code/verify_exact.py --max-n 200 --formula-n 16 | tee data/exact_run.log

modular: build/verify_modular
	build/verify_modular 3000 1000000007 data/p1000000007 data/watch_coordinates.csv | tee data/p1000000007_run.log
	build/verify_modular 3000 1000000009 data/p1000000009 data/watch_coordinates.csv | tee data/p1000000009_run.log

certify:
	$(PYTHON) code/combine_certificates.py | tee data/certificate_run.log

verify-xx2: exact modular certify

# --------------------------------------------- Part IV: x^(x^x), A281434 ---
verify-xxx:
	$(PYTHON) code/test_a281434.py
	$(PYTHON) code/run_experiments.py

# ------------------------------------------------------------------- all ---
verify: verify-xx verify-xx2 verify-xxx

clean:
	rm -rf build

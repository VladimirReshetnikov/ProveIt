SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra -Wconversion
PYTHON ?= python3
ARTICLE := A290268_partial_results

.PHONY: all pdf exact modular certify verify clean
all: pdf

build:
	mkdir -p build

pdf: | build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build $(ARTICLE).tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build $(ARTICLE).tex
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build $(ARTICLE).tex
	cp build/$(ARTICLE).pdf $(ARTICLE).pdf

build/verify_modular: code/verify_modular.cpp | build
	$(CXX) $(CXXFLAGS) $< -o $@

exact:
	$(PYTHON) code/verify_exact.py --max-n 200 --formula-n 16 | tee data/exact_run.log

modular: build/verify_modular
	build/verify_modular 3000 1000000007 data/p1000000007 data/watch_coordinates.csv | tee data/p1000000007_run.log
	build/verify_modular 3000 1000000009 data/p1000000009 data/watch_coordinates.csv | tee data/p1000000009_run.log

certify:
	$(PYTHON) code/combine_certificates.py | tee data/certificate_run.log

verify: exact modular
	$(PYTHON) code/combine_certificates.py | tee data/certificate_run.log

clean:
	rm -rf build

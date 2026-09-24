PYTHON ?= python3
CXX ?= c++
CXXFLAGS ?= -std=c++17 -O2 -Wall -Wextra -pedantic
CXXFLAGS_EXHAUSTIVE ?= -std=c++17 -O3 -Wall -Wextra -pedantic

.PHONY: all pdf article check cppcheck independent audits test certificates clean
all: pdf

pdf: article.pdf
article: article.pdf

article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode article.tex

check:
	$(PYTHON) code/run_checks.py --max-n 30
	$(PYTHON) code/check_bound_certificate.py

independent:
	$(PYTHON) code/check_large_example.py

orbit_count: code/orbit_count.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

cppcheck: orbit_count
	./orbit_count < code/bfs_cases.txt

build/exhaustive: code/exhaustive.cpp
	mkdir -p build
	$(CXX) $(CXXFLAGS_EXHAUSTIVE) $< -o $@

audits: build/exhaustive
	mkdir -p results
	./build/exhaustive 4 > results/exhaustive.json
	PYTHONOPTIMIZE= $(PYTHON) code/run_experiments.py > results/python_audit_log.txt
	$(PYTHON) code/certificate_checker.py results/certificates.json > results/certificate_check.txt
	PYTHONOPTIMIZE= $(PYTHON) -m unittest discover -s code -p 'test_*.py' -v > results/unit_tests.txt 2>&1
	cat results/python_audit_log.txt results/certificate_check.txt results/unit_tests.txt

test:
	PYTHONOPTIMIZE= $(PYTHON) -m unittest discover -s code -p 'test_*.py' -v

certificates:
	$(PYTHON) code/certificate_checker.py results/certificates.json

clean:
	latexmk -c article.tex
	rm -rf build code/__pycache__ orbit_count orbit_count.exe

PYTHON ?= python
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra -pedantic
LATEXMK ?= latexmk

.PHONY: all pdf data test test-independent test-symbolic clean
all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex
	$(LATEXMK) -c article.tex

pdf-pdflatex:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

exhaustive: code/exhaustive.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

data:
	$(PYTHON) code/research.py data --maximum 1000

# Exhaustion in C++ (n <= 11), compared set-by-set against structural generation.
test: exhaustive
	./exhaustive 11 > data/exhaustive.csv 2> verification/exhaustive_run.txt
	$(PYTHON) code/research.py verify --exhaustive-csv data/exhaustive.csv --report verification/exact_checks.json

# The separately written standard-library exhaustion (n <= 10). Kept alongside
# the C++ program on purpose: the two implementations are independent.
# Do not run it under `python -O`; its checks are assertions.
test-independent:
	$(PYTHON) code/verify.py --brute-max 10 --max-n 1000

test-symbolic:
	$(PYTHON) code/verify_symbolic.py

test-all: test test-independent test-symbolic

clean:
	$(LATEXMK) -c article.tex
	rm -f exhaustive exhaustive.exe

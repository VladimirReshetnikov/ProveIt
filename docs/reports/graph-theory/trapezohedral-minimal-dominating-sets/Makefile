PYTHON ?= python
CXX ?= g++
CXXFLAGS ?= -O3 -std=c++17 -Wall -Wextra -pedantic

.PHONY: all pdf data test test-symbolic clean
all: pdf

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

exhaustive: code/exhaustive.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

data:
	$(PYTHON) code/research.py data --maximum 1000

test: exhaustive
	./exhaustive 11 > data/exhaustive.csv 2> verification/exhaustive_run.txt
	$(PYTHON) code/research.py verify --exhaustive-csv data/exhaustive.csv --report verification/exact_checks.json

test-symbolic:
	$(PYTHON) code/verify_symbolic.py

clean:
	rm -f exhaustive exhaustive.exe article.aux article.log article.out article.toc article.fls article.fdb_latexmk

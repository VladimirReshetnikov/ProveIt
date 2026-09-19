PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf check clean

all: check pdf

check:
	$(PYTHON) counterexample.py
	$(PYTHON) verify.py
	$(PYTHON) certify_densities.py

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
	cp build/article.pdf article.pdf

clean:
	rm -rf build __pycache__

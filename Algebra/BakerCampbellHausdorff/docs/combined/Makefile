PYTHON ?= python

.PHONY: all pdf tables verify clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error bch_combined.tex

tables:
	$(PYTHON) code/make_tables.py

verify:
	$(PYTHON) code/run_all_verifiers.py

clean:
	latexmk -c bch_combined.tex

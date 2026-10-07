.PHONY: all pdf verify inversion figures clean

PYTHON ?= python3
LATEXMK ?= latexmk

all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error ordered_matrix_removal.tex

verify:
	$(PYTHON) code/verify.py

inversion:
	$(PYTHON) code/verify_inversion.py --require-symbolic --dps 120 > code/inversion_results.json

figures:
	$(PYTHON) code/generate_figures.py

clean:
	$(LATEXMK) -c ordered_matrix_removal.tex

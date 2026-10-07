PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all verify figure

all: paper.pdf

paper.pdf: paper.tex references.bib $(wildcard sections/*.tex) figures/parameter_region.pdf
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error paper.tex

verify:
	$(PYTHON) verify.py

figure:
	$(PYTHON) figures/make_parameter_region.py


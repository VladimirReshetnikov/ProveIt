PYTHON ?= python3

.PHONY: all reproduce check clean

all: report.pdf

reproduce:
	$(PYTHON) code/verify_lower_bound.py
	$(PYTHON) code/reproduce.py

check: reproduce

report.pdf: report.tex references.bib $(wildcard sections/*.tex) $(wildcard figures/*.pdf)
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build report.tex
	cp build/report.pdf report.pdf

clean:
	rm -rf build

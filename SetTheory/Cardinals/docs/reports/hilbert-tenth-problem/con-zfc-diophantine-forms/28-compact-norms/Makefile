.PHONY: all verify coefficients pdf

all: verify pdf

verify:
	python3 -B reproduce.py

coefficients:
	python3 -B reproduce.py --rebuild-coefficients

pdf: report.tex $(wildcard sections/*.tex)
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

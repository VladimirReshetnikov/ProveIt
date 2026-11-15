PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all check pdf clean

all: check pdf

check:
	$(PYTHON) code/validate_exact.py --output code/validation.json

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

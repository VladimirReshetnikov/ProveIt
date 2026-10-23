PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all check pdf clean

all: pdf

check:
	$(PYTHON) -B reproduce.py

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

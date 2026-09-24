PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic clean
all: pdf
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex
verify:
	$(PYTHON) code/verify.py
symbolic:
	$(PYTHON) code/verify_symbolic.py
clean:
	rm -f research.aux research.log research.out research.toc research.fls research.fdb_latexmk
	rm -rf code/__pycache__

PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf check full-check clean
all: pdf
pdf: research.pdf

research.pdf: research.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error research.tex

check:
	$(PYTHON) code/compact_check.py
	$(PYTHON) code/verify.py

full-check:
	$(PYTHON) code/compact_check.py
	$(PYTHON) code/verify.py --numpy-dense 19
	$(PYTHON) code/symbolic_verify.py

clean:
	rm -f research.aux research.log research.out research.toc research.fls research.fdb_latexmk

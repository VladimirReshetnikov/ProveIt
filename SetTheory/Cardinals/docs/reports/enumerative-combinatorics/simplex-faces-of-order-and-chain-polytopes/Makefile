PYTHON ?= python3
PDFLATEX ?= pdflatex
BASE = Largest_Simplex_Faces

.PHONY: all pdf verify quick clean
all: pdf

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(BASE).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(BASE).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(BASE).tex

verify:
	$(PYTHON) verify.py --full --output reproduced_results

quick:
	$(PYTHON) verify.py --quick --output quick_results

clean:
	rm -f $(BASE).aux $(BASE).out $(BASE).toc $(BASE).log

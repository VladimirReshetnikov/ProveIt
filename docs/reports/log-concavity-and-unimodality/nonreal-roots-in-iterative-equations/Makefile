PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all verify illustrations pdf clean
all: verify pdf

verify:
	$(PYTHON) code/verify.py

illustrations:
	$(PYTHON) code/analytic_demo.py --plots

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

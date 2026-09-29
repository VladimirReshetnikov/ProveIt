PYTHON ?= python
LATEX ?= pdflatex

.PHONY: all pdf verify clean

all: pdf

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --max-n 65536

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all test quick pdf clean

all: test pdf

test:
	$(PYTHON) code/verify.py

quick:
	$(PYTHON) code/verify.py --quick

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all test pdf clean

all: test pdf

test:
	$(PYTHON) verify.py

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

.PHONY: all pdf verify clean

PYTHON ?= python3
PDFLATEX ?= pdflatex

all: pdf

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls article.synctex.gz

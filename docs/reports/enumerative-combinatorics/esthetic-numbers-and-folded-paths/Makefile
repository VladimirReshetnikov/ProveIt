PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic clean
all: pdf
pdf: article.pdf

article.pdf: article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py

symbolic:
	$(PYTHON) symbolic_verify.py

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

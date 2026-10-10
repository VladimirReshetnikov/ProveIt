PYTHON ?= python
PDFLATEX ?= pdflatex

.PHONY: all article verify numerics clean
all: verify article

article:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py

numerics:
	$(PYTHON) code/numerics.py

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

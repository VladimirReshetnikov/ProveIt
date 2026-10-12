PYTHON ?= python
PDFLATEX ?= pdflatex

.PHONY: all pdf verify exact numeric clean
all: pdf

pdf: article.tex results/numeric_table.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify: exact numeric

exact:
	$(PYTHON) code/verify_exact.py

numeric:
	$(PYTHON) code/verify_numeric.py --dps 180

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk article.synctex.gz

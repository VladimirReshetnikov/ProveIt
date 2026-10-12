PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf check clean
all: pdf
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
check:
	$(PYTHON) scripts/verify_exact.py
	$(PYTHON) scripts/verify_numeric.py
	$(PYTHON) scripts/verify_coefficient_problem.py
clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

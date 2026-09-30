PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf check clean
all: check pdf

check:
	$(PYTHON) code/verify.py --order 36 --output build/verification

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic clean

all: pdf verify

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py

symbolic:
	$(PYTHON) verify_symbolic.py

clean:
	rm -f article.aux article.log article.out article.toc

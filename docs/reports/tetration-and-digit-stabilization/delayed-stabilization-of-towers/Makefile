PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all verify pdf clean
all: verify pdf

verify:
	$(PYTHON) code/verify.py

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc

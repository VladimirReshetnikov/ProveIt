PYTHON ?= python3
TEX ?= pdflatex

.PHONY: all verify pdf clean
all: verify pdf

verify:
	$(PYTHON) code/verify_results.py

pdf:
	$(TEX) -interaction=nonstopmode -halt-on-error article.tex
	$(TEX) -interaction=nonstopmode -halt-on-error article.tex
	$(TEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc

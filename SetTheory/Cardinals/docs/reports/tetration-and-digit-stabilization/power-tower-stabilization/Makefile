PYTHON ?= python3
PDFLATEX ?= pdflatex
LATEXMK ?= latexmk

.PHONY: all verify test pdf pdf-latexmk clean
all: verify pdf

verify:
	$(PYTHON) code/verify.py

# Alias kept so that the merged report's second source package's documented
# command keeps working.
test: verify

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

pdf-latexmk:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc \
	      article.fdb_latexmk article.fls

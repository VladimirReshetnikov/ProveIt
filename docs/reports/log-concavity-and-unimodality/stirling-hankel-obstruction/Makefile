PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic clean
all: pdf verify

pdf:
	$(PDFLATEX) -halt-on-error -interaction=nonstopmode article.tex
	$(PDFLATEX) -halt-on-error -interaction=nonstopmode article.tex
	$(PDFLATEX) -halt-on-error -interaction=nonstopmode article.tex

verify:
	$(PYTHON) code/verify.py

symbolic:
	$(PYTHON) code/symbolic_identity.py

clean:
	rm -f article.aux article.log article.out article.toc

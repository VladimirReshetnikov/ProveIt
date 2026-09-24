PYTHON ?= python
PDFLATEX ?= pdflatex

.PHONY: all verify figures symbolic pdf clean
all: verify figures symbolic pdf

verify:
	$(PYTHON) code/verify.py

figures:
	$(PYTHON) code/reproduce.py

symbolic:
	$(PYTHON) code/symbolic_check.py

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc

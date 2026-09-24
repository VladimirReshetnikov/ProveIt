PYTHON ?= python3
LATEX ?= pdflatex
LATEXFLAGS ?= -interaction=nonstopmode -halt-on-error

.PHONY: all verify pdf clean
all: verify pdf

verify:
	$(PYTHON) code/verify.py --output results

pdf: article.pdf

results/worked_table.tex: code/verify.py
	$(PYTHON) code/verify.py --output results

article.pdf: article.tex results/worked_table.tex
	$(LATEX) $(LATEXFLAGS) article.tex
	$(LATEX) $(LATEXFLAGS) article.tex
	$(LATEX) $(LATEXFLAGS) article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
	rm -rf code/__pycache__

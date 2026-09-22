PYTHON ?= python3
PDFLATEX ?= pdflatex
TEXFLAGS = -interaction=nonstopmode -halt-on-error

.PHONY: all verify pdf clean

all: verify pdf

verify:
	$(PYTHON) code/verify.py --output data/verification-rerun.json

pdf:
	$(PDFLATEX) $(TEXFLAGS) article.tex
	$(PDFLATEX) $(TEXFLAGS) article.tex
	$(PDFLATEX) $(TEXFLAGS) article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

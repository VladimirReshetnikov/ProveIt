PYTHON ?= python3
PDFLATEX ?= pdflatex
TEXFLAGS = -interaction=nonstopmode -halt-on-error

.PHONY: all verify numerical tables clean
all: article.pdf

article.pdf: article.tex
	$(PDFLATEX) $(TEXFLAGS) article.tex
	$(PDFLATEX) $(TEXFLAGS) article.tex
	$(PDFLATEX) $(TEXFLAGS) article.tex

verify:
	$(PYTHON) code/verify_exact.py --order 300

numerical:
	$(PYTHON) code/diagnostics.py --order 1000 --powers 2 3

tables:
	$(PYTHON) code/report_tables.py

clean:
	rm -f article.aux article.log article.out article.toc

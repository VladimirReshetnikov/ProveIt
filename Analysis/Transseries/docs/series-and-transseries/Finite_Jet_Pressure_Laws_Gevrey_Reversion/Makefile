.PHONY: check diagnostics pdf clean
PYTHON ?= python3
PDFLATEX ?= pdflatex

check:
	$(PYTHON) code/verify.py

diagnostics:
	$(PYTHON) code/diagnostics.py --max-n 10000

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc

PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic clean
all: pdf verify

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py --output data > verification.log
	cat verification.log

symbolic:
	$(PYTHON) verify_symbolic.py > symbolic_verification.log
	cat symbolic_verification.log

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

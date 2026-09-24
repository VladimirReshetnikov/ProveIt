PYTHON ?= python3
PDFLATEX ?= pdflatex
.PHONY: all pdf verify generate clean
all: pdf verify
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
verify:
	$(PYTHON) code/test_structure.py
	$(PYTHON) code/verify_certificates.py --max-k 200
generate:
	$(PYTHON) code/generate_certificates.py --max-k 200
clean:
	rm -f article.aux article.log article.out article.toc

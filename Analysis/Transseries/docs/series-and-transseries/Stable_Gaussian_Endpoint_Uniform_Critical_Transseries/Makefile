PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: pdf verify clean
pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --max-n 4096 > data/run_summary.txt

clean:
	rm -f article.aux article.log article.out article.toc

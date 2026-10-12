PYTHON ?= python3
PDFLATEX ?= pdflatex
OUT ?= replay
MAX_N ?= 4096

.PHONY: pdf verify clean
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --output-dir $(OUT) --max-n $(MAX_N)

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

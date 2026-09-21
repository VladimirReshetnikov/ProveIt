PYTHON ?= python3

.PHONY: all pdf verify symbolic clean
all: pdf verify

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py --max-n 1000 --exhaustive 11

symbolic:
	$(PYTHON) symbolic_check.py

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

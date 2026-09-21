PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf verify clean

all: pdf verify

pdf: article.pdf

article.pdf: article.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py --out-dir artifacts

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

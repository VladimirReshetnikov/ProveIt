PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf verify clean

all: pdf verify

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --brute-max 10 --max-n 1000

clean:
	$(LATEXMK) -c article.tex

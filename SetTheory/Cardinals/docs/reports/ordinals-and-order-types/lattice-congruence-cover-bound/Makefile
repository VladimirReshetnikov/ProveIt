PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf verify clean
all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error sharp_cover_bound.tex

verify:
	$(PYTHON) code/verify.py --max-n 8 --independent-through 7
	$(PYTHON) code/examples.py

clean:
	$(LATEXMK) -c sharp_cover_bound.tex

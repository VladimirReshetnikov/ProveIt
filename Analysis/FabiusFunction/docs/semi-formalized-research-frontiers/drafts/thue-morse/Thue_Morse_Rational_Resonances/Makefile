ARTICLE = thue_morse_rational_resonances
PYTHON ?= python3

.PHONY: all pdf verify clean
all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

verify:
	$(PYTHON) verify.py --output results

clean:
	latexmk -c $(ARTICLE).tex

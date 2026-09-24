.PHONY: all pdf check clean

PYTHON ?= python3
LATEXMK ?= latexmk

all: check pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

check:
	$(PYTHON) code/verify.py --output data/verification.json

clean:
	$(LATEXMK) -c article.tex

PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all test pdf clean
all: test pdf

test:
	$(PYTHON) code/verify.py

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	$(LATEXMK) -c article.tex

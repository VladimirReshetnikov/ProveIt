PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf verify figures clean
all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py

figures:
	$(PYTHON) code/make_figures.py

clean:
	$(LATEXMK) -c article.tex
	rm -rf code/__pycache__

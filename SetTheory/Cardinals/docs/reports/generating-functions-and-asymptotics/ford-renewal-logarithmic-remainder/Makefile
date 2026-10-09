PYTHON ?= python3

.PHONY: all pdf verify figures clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
	cp build/article.pdf article.pdf

verify:
	$(PYTHON) code/verify_recurrence.py --nmax 1000 --out rerun/data
	$(PYTHON) code/verify_symbolic.py --out rerun/symbolic_checks.json

figures:
	$(PYTHON) code/make_figures.py --input data --out rerun

clean:
	latexmk -C -outdir=build article.tex

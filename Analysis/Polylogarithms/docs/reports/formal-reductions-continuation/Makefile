PYTHON ?= python3

.PHONY: all pdf verify figures recompute-figure standalone clean

all: pdf

pdf:
	latexmk -cd -pdf -interaction=nonstopmode -halt-on-error article/main.tex

verify:
	$(PYTHON) code/run_checks.py

figures:
	$(PYTHON) code/plot_lerch_n2_branches.py --render-only

recompute-figure:
	$(PYTHON) code/plot_lerch_n2_branches.py

standalone:
	$(PYTHON) code/flatten_tex.py

clean:
	latexmk -cd -c article/main.tex

PYTHON ?= python3
ARTICLE = polylogarithm_order_jets

.PHONY: all pdf verify figure
all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

verify:
	$(PYTHON) code/run_checks.py

figure:
	$(PYTHON) code/plot_complex_resonance.py --data data/complex_resonance_checks.json --output-dir figures

.PHONY: all verify experiments refined figures pdf

all:
	$(MAKE) verify
	$(MAKE) experiments
	$(MAKE) refined
	$(MAKE) figures
	$(MAKE) pdf

verify:
	python3 code/verify_finite.py --output results/finite_validation.json

experiments:
	python3 code/experiments.py --samples 6000

refined:
	python3 code/refined_center.py

figures:
	python3 code/make_figures.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error spectral_extremes.tex
	pdflatex -interaction=nonstopmode -halt-on-error spectral_extremes.tex

.PHONY: all pdf verify clean

all: verify pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error density_aware_sat_improvement.tex

verify:
	python3 code/verify_components.py --output verification_results.json

clean:
	latexmk -c density_aware_sat_improvement.tex

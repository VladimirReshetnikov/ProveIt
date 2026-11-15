.PHONY: all examples clean

all:
	latexmk -pdf -interaction=nonstopmode -halt-on-error puiseux_ipra.tex

examples:
	python3 code/check_examples.py --cutoff 96 --output evidence/example_checks.json

clean:
	latexmk -c puiseux_ipra.tex

.PHONY: all pdf test diagnostics clean

all: pdf test

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error brun_ipra.tex

test:
	python3 -m unittest discover -s tests -v

diagnostics:
	python3 artifacts/finite_sieve.py --json artifacts/verification.json

clean:
	latexmk -c brun_ipra.tex

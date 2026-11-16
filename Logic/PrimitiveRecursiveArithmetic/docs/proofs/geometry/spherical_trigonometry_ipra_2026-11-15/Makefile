.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 scripts/verify_identities.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error spherical_trigonometry_ipra.tex

clean:
	latexmk -c spherical_trigonometry_ipra.tex

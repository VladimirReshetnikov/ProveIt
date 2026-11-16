.PHONY: all verify pdf clean

all: verify pdf

verify:
	./scripts/verify_all.sh

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error trigonometric_identities_ipra.tex

clean:
	latexmk -C trigonometric_identities_ipra.tex

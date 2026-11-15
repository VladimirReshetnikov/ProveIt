.PHONY: all pdf verify clean

all: pdf verify

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error apery_ipra.tex

verify:
	python3 code/verify.py

clean:
	latexmk -c apery_ipra.tex

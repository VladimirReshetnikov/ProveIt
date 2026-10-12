.PHONY: all pdf verify clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 verification/verify.py

clean:
	latexmk -c article.tex

.PHONY: all pdf check clean

all: pdf check

pdf:
	latexmk -pdf -halt-on-error -interaction=nonstopmode article.tex

check:
	python3 code/verify.py

clean:
	latexmk -c article.tex

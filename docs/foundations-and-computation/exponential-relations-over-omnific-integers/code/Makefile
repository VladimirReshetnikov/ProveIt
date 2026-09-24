.PHONY: all pdf checks clean

all: pdf checks

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

checks:
	python3 code/checks.py --output data/check_results.json

clean:
	latexmk -c article.tex

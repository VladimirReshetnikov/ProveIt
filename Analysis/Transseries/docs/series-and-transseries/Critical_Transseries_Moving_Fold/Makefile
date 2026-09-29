.PHONY: all pdf verify quick clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python verify.py

quick:
	python verify.py --quick

clean:
	latexmk -c article.tex

.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 code/verify.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex

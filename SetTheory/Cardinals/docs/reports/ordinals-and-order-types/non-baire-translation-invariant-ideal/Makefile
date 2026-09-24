.PHONY: all pdf verify clean

all: pdf verify

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 verify.py

clean:
	latexmk -c article.tex

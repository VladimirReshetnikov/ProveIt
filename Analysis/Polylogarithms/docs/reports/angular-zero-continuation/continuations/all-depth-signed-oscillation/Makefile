.PHONY: all verify regenerate clean
all: article.pdf
article.pdf: article.tex references.tex $(wildcard sections/*.tex)
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify.py
regenerate:
	python code/verify.py --regenerate
clean:
	latexmk -c article.tex

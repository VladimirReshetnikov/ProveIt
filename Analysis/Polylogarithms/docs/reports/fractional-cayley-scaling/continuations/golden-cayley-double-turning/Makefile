.PHONY: all verify figures clean

all: article.pdf

article.pdf: article.tex references.tex $(wildcard sections/*.tex) $(wildcard figures/*.pdf)
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 code/run_all.py

figures:
	python3 code/make_figures.py

clean:
	latexmk -c article.tex

.PHONY: all verify diagnostics figures clean

all: article.pdf

article.pdf: article.tex references.tex $(wildcard sections/*.tex) $(wildcard figures/*.pdf)
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 code/run_verification.py

diagnostics:
	python3 code/run_verification.py --diagnostics

figures:
	python3 code/make_figures.py
	python3 code/zeros/make_bessel_figure.py

clean:
	latexmk -c article.tex

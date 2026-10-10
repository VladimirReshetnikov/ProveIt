.PHONY: all pdf verify diagnostics figures clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python3 code/verify_all.py

diagnostics:
	python3 code/verify_all.py --diagnostics

figures:
	python3 code/plot_n5_zeros.py

clean:
	latexmk -c article.tex

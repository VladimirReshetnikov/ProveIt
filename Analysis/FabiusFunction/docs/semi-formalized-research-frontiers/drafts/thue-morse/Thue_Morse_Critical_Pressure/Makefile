.PHONY: all pdf verify quick clean
all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	OPENBLAS_NUM_THREADS=1 python code/verify.py --full

quick:
	OPENBLAS_NUM_THREADS=1 python code/verify.py

clean:
	latexmk -c article.tex

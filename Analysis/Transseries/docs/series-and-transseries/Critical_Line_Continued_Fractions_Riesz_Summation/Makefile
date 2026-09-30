PYTHON ?= python3

.PHONY: all verify pdf
all: verify pdf

verify:
	$(PYTHON) verify.py --outdir build/results

pdf:
	mkdir -p build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/latex-pass-1.txt
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/latex-pass-2.txt
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build article.tex > build/latex-pass-3.txt
	cp build/article.pdf article.pdf

.PHONY: all verify clean
all: article.pdf
article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python verify_spectra.py
clean:
	latexmk -c article.tex

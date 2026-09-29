.PHONY: all verify clean
all: article.pdf

article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python verify_pressure.py
	python verify_minimum.py

clean:
	latexmk -c article.tex

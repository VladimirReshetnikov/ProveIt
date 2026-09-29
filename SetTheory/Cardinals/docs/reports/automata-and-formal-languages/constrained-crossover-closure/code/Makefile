.PHONY: pdf check clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

check:
	python3 code/verify.py

clean:
	latexmk -c article.tex

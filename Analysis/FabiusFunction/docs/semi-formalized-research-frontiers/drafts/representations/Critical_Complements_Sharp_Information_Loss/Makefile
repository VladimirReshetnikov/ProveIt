.PHONY: pdf diagnostics clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

diagnostics:
	python code/verify.py
	python code/make_figures.py

clean:
	latexmk -c article.tex

.PHONY: all verify diagnostics clean
all: article.pdf
article.pdf: article.tex data/diagnostics_table.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python3 code/verify.py
diagnostics:
	python3 code/analyze.py --precision 70
clean:
	latexmk -c article.tex

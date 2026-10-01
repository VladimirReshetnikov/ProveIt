.PHONY: check reproduce pdf
check:
	python3 code/run_all.py
reproduce:
	python3 code/reproduce_all.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

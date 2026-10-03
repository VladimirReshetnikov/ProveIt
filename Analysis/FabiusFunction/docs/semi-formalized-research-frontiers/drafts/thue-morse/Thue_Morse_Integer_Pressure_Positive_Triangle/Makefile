.PHONY: all check pdf
all: check pdf
check:
	python3 code/run_all.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

.PHONY: all pdf verify clean
all: verify pdf
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify_exact.py
	python code/verify_numeric.py
clean:
	latexmk -c article.tex

.PHONY: all pdf standalone check exact numeric clean

all: pdf standalone

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

standalone:
	python code/flatten_tex.py

check: exact numeric

exact:
	python code/verify_exact.py --bound 500

numeric:
	python code/verify_numeric.py --dps 90 140

clean:
	latexmk -c article.tex
	rm -rf code/__pycache__

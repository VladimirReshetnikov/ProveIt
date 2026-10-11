.PHONY: pdf check exact numeric clean
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
exact:
	python code/verify_exact.py
numeric:
	python code/verify_numeric.py
check: exact numeric
clean:
	latexmk -c article.tex

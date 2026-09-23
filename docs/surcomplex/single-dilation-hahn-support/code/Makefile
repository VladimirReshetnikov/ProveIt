.PHONY: all check clean

all: article.pdf check

article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

check: verify.py
	python3 verify.py > verification.txt
	cat verification.txt

clean:
	latexmk -c article.tex

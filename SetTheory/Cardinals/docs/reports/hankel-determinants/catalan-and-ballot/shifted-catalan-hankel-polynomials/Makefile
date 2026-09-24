.PHONY: all pdf test clean

all: pdf test

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

test:
	python3 code/verify.py --out data > data/verification.txt
	cat data/verification.txt

clean:
	latexmk -c article.tex
	rm -rf code/__pycache__

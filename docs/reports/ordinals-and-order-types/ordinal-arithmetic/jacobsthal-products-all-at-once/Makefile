.PHONY: all check pdf clean

all: check pdf

check:
	python3 code/verify.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex
	rm -rf code/__pycache__

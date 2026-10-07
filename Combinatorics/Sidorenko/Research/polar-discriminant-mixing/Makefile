.PHONY: all pdf check clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error polar-discriminant-mixing.tex

check:
	python code/verify.py

clean:
	latexmk -c polar-discriminant-mixing.tex
	rm -rf code/__pycache__

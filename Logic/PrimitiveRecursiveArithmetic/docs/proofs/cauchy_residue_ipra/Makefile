.PHONY: all pdf validate clean

all: pdf validate

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

validate:
	python3 code/run_validation.py

clean:
	latexmk -c report.tex

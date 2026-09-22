.PHONY: all test clean

all: report.pdf

report.pdf: report.tex
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

test:
	python3 code/run_all.py

clean:
	latexmk -c report.tex

.PHONY: all verify pdf clean
all: verify pdf

verify:
	python3 reproduce.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

clean:
	latexmk -c report.tex

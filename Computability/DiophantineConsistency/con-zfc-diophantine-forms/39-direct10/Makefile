.PHONY: all verify pdf

all: verify pdf

verify:
	python3 reproduce.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

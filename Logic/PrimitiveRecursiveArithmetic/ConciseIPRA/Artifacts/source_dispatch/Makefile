.PHONY: all report check

all: report

report:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

check:
	python3 reproduce.py

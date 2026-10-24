PYTHON ?= python3

.PHONY: all pdf check clean
all: check pdf

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

check:
	$(PYTHON) verify.py

clean:
	rm -f report.aux report.log report.out report.toc

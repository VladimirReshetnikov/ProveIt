.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 reproduce.py

pdf:
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

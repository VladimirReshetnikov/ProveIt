.PHONY: all clean

all: report.pdf

report.pdf: report.tex $(wildcard sections/*.tex)
	xelatex -interaction=nonstopmode -halt-on-error report.tex
	xelatex -interaction=nonstopmode -halt-on-error report.tex
	xelatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

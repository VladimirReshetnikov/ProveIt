.PHONY: all verify clean

all: report.pdf

report.pdf: report.tex integer/section.tex positive/section.tex direct/section.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 verify.py

clean:
	rm -f report.aux report.log report.out report.toc report.fls report.fdb_latexmk

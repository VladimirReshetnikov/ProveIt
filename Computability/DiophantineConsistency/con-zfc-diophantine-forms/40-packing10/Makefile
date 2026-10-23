.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 code/verify.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc report.fls report.fdb_latexmk

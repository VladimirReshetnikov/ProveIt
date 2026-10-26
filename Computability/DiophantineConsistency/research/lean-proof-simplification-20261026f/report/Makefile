.PHONY: all clean qa
all: proof_simplification_report.pdf

proof_simplification_report.pdf: proof_simplification_report.tex preamble.tex $(wildcard sections/*.tex)
	bash build.sh

qa: proof_simplification_report.pdf
	mkdir -p qa/pages
	pdftoppm -r 110 -png proof_simplification_report.pdf qa/pages/page
	pdftotext -layout proof_simplification_report.pdf qa/extracted.txt

clean:
	latexmk -c proof_simplification_report.tex

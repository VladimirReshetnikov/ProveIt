.PHONY: all verify pdf tables clean
all: verify pdf

verify:
	python3 -B code/verify_all.py --output verification_receipt.json

tables:
	python3 -B code/build_tables.py

pdf: report.tex circuit.tex cross_counts.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

.PHONY: all verify integrity pdf clean

all: verify pdf

verify:
	python3 reproduce.py

integrity:
	python3 reproduce.py --check-release

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc report.fdb_latexmk report.fls

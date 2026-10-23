.PHONY: all verify pdf clean

all: verify pdf

verify:
	python3 verify_all.py

pdf: report.tex $(wildcard sections/*.tex) signed10/SIGNED10_SECTION.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	python3 -c "from pathlib import Path; [p.unlink() for s in ('aux','log','out','toc') for p in Path('.').glob('report.'+s)]"

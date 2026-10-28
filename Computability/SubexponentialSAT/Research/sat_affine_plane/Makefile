.PHONY: pdf check
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
check:
	python3 code/reproduce.py --optimized

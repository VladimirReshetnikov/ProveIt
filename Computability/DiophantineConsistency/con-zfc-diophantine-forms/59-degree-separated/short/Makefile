.PHONY: verify pdf
verify:
	python3 build.py
	python3 audit.py
	python3 -O audit.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

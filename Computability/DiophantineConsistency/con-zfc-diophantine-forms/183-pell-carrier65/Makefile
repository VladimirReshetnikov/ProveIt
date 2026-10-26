.PHONY: verify pdf

verify:
	python3 -B verify.py
	python3 -B -O verify.py
	python3 -B code/build.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error equation.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

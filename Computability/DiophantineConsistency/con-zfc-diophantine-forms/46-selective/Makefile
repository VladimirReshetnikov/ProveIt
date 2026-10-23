.PHONY: verify pdf figure

verify:
	python3 verify.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

figure:
	python3 code/make_figure.py

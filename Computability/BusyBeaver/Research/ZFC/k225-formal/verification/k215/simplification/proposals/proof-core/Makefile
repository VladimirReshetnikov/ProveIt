.PHONY: all verify
all: report.pdf

report.pdf: report.tex results_macros.tex four_shapes.tex allocation_followup.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 verify.py

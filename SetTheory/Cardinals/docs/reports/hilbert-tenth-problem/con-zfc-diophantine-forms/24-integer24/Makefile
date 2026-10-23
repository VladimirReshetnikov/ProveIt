PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: verify reproduce pdf

verify:
	$(PYTHON) verify.py

reproduce:
	$(PYTHON) reproduce.py

pdf:
	$(PYTHON) code/assemble_report.py
	$(LATEX) -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex

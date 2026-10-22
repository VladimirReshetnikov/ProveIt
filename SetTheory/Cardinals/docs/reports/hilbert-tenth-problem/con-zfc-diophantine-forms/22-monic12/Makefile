PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all check pdf clean

all: check pdf

check:
	$(PYTHON) code/reproduce.py

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex

clean:
	rm -f con_zfc_synthesis.aux con_zfc_synthesis.log con_zfc_synthesis.out con_zfc_synthesis.fls con_zfc_synthesis.fdb_latexmk

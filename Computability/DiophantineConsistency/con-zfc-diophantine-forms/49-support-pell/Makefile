PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all verify pdf rebuild clean

all: verify pdf

verify:
	$(PYTHON) verify_all.py

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error report.tex

rebuild:
	$(PYTHON) code/build.py
	$(PYTHON) nine/build_multitarget_nine.py
	$(PYTHON) materialize.py
	$(PYTHON) eleven/build_eleven.py
	$(PYTHON) short/build_offset44.py
	$(PYTHON) verify_all.py

clean:
	rm -f report.aux report.log report.out report.toc

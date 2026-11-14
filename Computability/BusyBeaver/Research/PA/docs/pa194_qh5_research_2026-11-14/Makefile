PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: verify quick report

verify:
	$(PYTHON) -B verify.py

quick:
	$(PYTHON) -B verify.py --quick

report:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=report report/pa194_qh5_report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=report report/pa194_qh5_report.tex

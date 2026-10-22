PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: verify pdf integrity

verify:
	$(PYTHON) verify.py

integrity:
	$(PYTHON) verify.py --manifest-only

pdf:
	mkdir -p .build
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=.build report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=.build report.tex
	cp .build/report.pdf report.pdf

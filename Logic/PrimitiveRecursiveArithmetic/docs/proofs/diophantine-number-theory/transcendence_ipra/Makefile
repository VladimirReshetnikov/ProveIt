PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf checks bounds clean
all: pdf checks bounds

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error transcendence_ipra.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error transcendence_ipra.tex

checks:
	mkdir -p verification
	$(PYTHON) code/e_checks.py > verification/e_checks.json
	$(PYTHON) code/matrix_checks.py > verification/matrix_checks.json
	$(PYTHON) code/finite_analysis_checks.py > verification/finite_analysis_checks.json

bounds:
	$(PYTHON) code/bounds.py --output verification/bounds_x_minus_3.json

clean:
	rm -f transcendence_ipra.aux transcendence_ipra.log transcendence_ipra.out transcendence_ipra.toc


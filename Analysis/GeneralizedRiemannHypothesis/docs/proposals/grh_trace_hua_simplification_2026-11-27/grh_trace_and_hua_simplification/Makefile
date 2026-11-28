PYTHON ?= python3

.PHONY: pdf check clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

check:
	$(PYTHON) checks/check_trace_transfer.py --output results/trace_transfer_check_results.json
	$(PYTHON) checks/check_bordered_hua.py --output results/bordered_hua_checks.json
	$(PYTHON) checks/check_bordered_geometry.py --output results/bordered_geometry_checks.json

clean:
	latexmk -c paper.tex

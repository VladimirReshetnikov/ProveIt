PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all papers checks figure clean
all: papers

papers:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -jobname=deep_padic_roots main.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error -jobname=positive_filter_rigidity companion_filters.tex

checks:
	$(PYTHON) checks/exact_lattice_check.py > data/lattice_certificates.json
	$(PYTHON) checks/independent_dvr_check.py > data/independent_dvr_results.json
	$(PYTHON) checks/compare_certificates.py > data/certificate_comparison.json
	$(PYTHON) checks/witness_audit.py > data/witness_audit.json
	$(PYTHON) checks/transport_check.py > data/transport_results.json
	$(PYTHON) checks/filter_hessian_check.py > data/filter_hessian_results.json

figure:
	$(PYTHON) checks/make_newton_figure.py

clean:
	$(LATEXMK) -c -jobname=deep_padic_roots main.tex
	$(LATEXMK) -c -jobname=positive_filter_rigidity companion_filters.tex


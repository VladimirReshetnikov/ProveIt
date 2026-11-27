PYTHON ?= python3
SOURCE ?=

.PHONY: all pdf figures verify source-audit clean
all: pdf

figures:
	$(PYTHON) code/make_figures.py

pdf: figures
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

verify:
	$(PYTHON) code/cubic_verify.py
	$(PYTHON) code/cubic_independent_enumeration.py
	$(PYTHON) code/verify_unequal_branches.py --output results/unequal_branches.json

source-audit:
	@test -n "$(SOURCE)" || (echo 'Set SOURCE to a ProveIt checkout at the pinned revision'; exit 2)
	$(PYTHON) code/audit_sources.py "$(SOURCE)" --output provenance/source_static_audit.json

clean:
	latexmk -c report.tex

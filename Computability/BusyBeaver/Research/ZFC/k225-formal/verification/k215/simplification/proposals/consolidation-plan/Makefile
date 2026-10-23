.PHONY: report verify census

PDFLATEX ?= pdflatex
PYTHON ?= python3

report:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -file-line-error report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -file-line-error report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -file-line-error report.tex

verify:
	$(PYTHON) scripts/verify_bundle.py

# Usage: make census REPO=/absolute/path/to/ProveIt OUT=/tmp/k215-census.json
census:
	@test -n "$(REPO)" -a -n "$(OUT)" || (echo "Set REPO and OUT"; exit 2)
	$(PYTHON) scripts/census.py --repo "$(REPO)" --out "$(OUT)"

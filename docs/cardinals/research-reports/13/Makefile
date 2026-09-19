MAIN := Cyclic_Symmetry_Ultraexacting
PYTHON ?= python3

.PHONY: all pdf audit clean

all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error $(MAIN).tex

audit:
	$(PYTHON) finite_symmetry_audit.py --max-period 5 --output audit_results.json > audit_log.txt
	cat audit_log.txt

clean:
	latexmk -c $(MAIN).tex

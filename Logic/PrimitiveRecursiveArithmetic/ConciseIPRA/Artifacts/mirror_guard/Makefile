PYTHON ?= python3

.PHONY: all verify pdf clean

all: verify pdf

verify:
	$(PYTHON) reproduce.py
	$(PYTHON) tools/audit_named_formulas.py --kernel-dir . --output evidence/named_formula_audit.json
	$(PYTHON) tools/render_evidence.py

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc

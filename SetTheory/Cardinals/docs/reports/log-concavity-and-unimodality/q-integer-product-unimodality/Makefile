PYTHON ?= python3

.PHONY: all report verify quick check symbolic clean
all: report

report: report.pdf
report.pdf: report.tex code/minimal_certificate.py
	latexmk -pdf -interaction=nonstopmode report.tex

# Full recorded run of both verifiers; overwrites the recorded results.
verify:
	$(PYTHON) code/verify_products.py --full --out data/verification_results.json
	$(PYTHON) code/verify_threshold.py
	$(PYTHON) code/minimal_certificate.py

# Smoke test only; does not overwrite data/verification_results.json.
quick:
	$(PYTHON) code/verify_products.py

check: verify

# Optional; requires SymPy (see requirements-optional.txt).
symbolic:
	$(PYTHON) code/symbolic_checks.py

clean:
	latexmk -c report.tex

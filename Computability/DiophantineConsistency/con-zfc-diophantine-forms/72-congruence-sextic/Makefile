PYTHON ?= python3

.PHONY: verify verify-optimized pdf

verify:
	$(PYTHON) verify_all.py

verify-optimized:
	$(PYTHON) -O verify_all.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

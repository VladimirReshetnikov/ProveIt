PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: verify full pdf

verify:
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) code/verify.py

full:
	PYTHONDONTWRITEBYTECODE=1 $(PYTHON) code/verify.py --full

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error report.tex

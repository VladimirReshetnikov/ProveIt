PYTHON ?= python3

.PHONY: all check check-cas-free check-sympy pdf clean

all: check pdf

check: check-cas-free check-sympy

# Everything below needs only the Python standard library.
check-cas-free:
	$(PYTHON) certificates.py
	$(PYTHON) verify.py
	$(PYTHON) code/verify_rows.py --max-n 300 --output-dir data

# The one target with a third-party dependency; see requirements.txt.
check-sympy:
	$(PYTHON) code/verify_certificates.py --output data/certificate_checks.json

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex

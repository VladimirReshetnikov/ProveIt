PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf verify verify-wide minimal certificate symbolic rebuild clean
all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py

verify-wide:
	$(PYTHON) code/verify_wide.py --out reproduced_results

minimal:
	$(PYTHON) minimal_certificate.py

certificate:
	$(PYTHON) code/certificate.py

symbolic:
	$(PYTHON) independent_sympy_check.py

rebuild: verify
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	$(LATEXMK) -c article.tex

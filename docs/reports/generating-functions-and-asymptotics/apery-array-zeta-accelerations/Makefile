PYTHON ?= python3
PDFLATEX ?= pdflatex
LATEXMK ?= latexmk

.PHONY: all pdf verify verify-independent symbolic symbolic-independent \
        numerical diagnostics check clean
all: pdf

pdf: article.pdf

article.pdf: article.tex data/error_table.tex
	$(LATEXMK) -pdf -interaction=nonstopmode article.tex
	$(LATEXMK) -c

verify:
	$(PYTHON) verify.py --max-index 40 --offsets 12 --output-dir data
	$(PYTHON) make_error_table.py

verify-independent:
	$(PYTHON) verify_independent.py

symbolic:
	$(PYTHON) symbolic_certificates.py > data/symbolic_verification.txt
	cat data/symbolic_verification.txt

symbolic-independent:
	$(PYTHON) symbolic_certificates_independent.py

numerical:
	$(PYTHON) numerical_checks.py

diagnostics:
	$(PYTHON) asymptotic_diagnostics.py

check: verify verify-independent symbolic symbolic-independent numerical diagnostics

clean:
	$(LATEXMK) -c
	rm -f article.aux article.log article.out article.toc

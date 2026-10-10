PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all pdf exact diagnostics clean
all: exact pdf
pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
exact:
	$(PYTHON) verification/certify.py
	$(PYTHON) verification/certify_minimum.py
	$(PYTHON) verification/test_algebra.py
	$(PYTHON) verification/test_integration.py
diagnostics:
	$(PYTHON) verification/numerical_checks.py identity
	$(PYTHON) verification/numerical_checks.py roots
	$(PYTHON) verification/numerical_checks.py minimum
	$(PYTHON) verification/numerical_checks.py fold
clean:
	rm -f article.aux article.log article.out article.toc

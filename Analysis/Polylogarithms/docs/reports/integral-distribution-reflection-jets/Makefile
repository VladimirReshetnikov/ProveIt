PYTHON ?= python3
LATEX ?= pdflatex
.PHONY: pdf exact optional all clean
pdf:
	cd article && $(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	cd article && $(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	cd article && $(LATEX) -interaction=nonstopmode -halt-on-error article.tex
exact:
	$(PYTHON) code/verify_certificates.py
	$(PYTHON) code/test_exact.py
optional:
	$(PYTHON) code/test_smith.py
	$(PYTHON) code/numerical_diagnostics.py
all: pdf exact optional
clean:
	rm -f article/*.aux article/*.out article/*.toc article/*.log

PYTHON ?= python3
LATEX ?= pdflatex
MAIN = ordinal_chomp_counterexample

.PHONY: all pdf verify test certificates clean
all: pdf verify

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error $(MAIN).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(MAIN).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(MAIN).tex

verify:
	$(PYTHON) code/minimal_verifier.py
	$(PYTHON) code/verify.py
	$(PYTHON) code/independent_check.py
	$(PYTHON) code/verify_poisoned_certificate.py

test:
	$(PYTHON) code/test_poisoned_certificate.py

certificates:
	$(PYTHON) code/build_certificates.py
	$(PYTHON) code/make_poisoned_certificate.py
	$(PYTHON) code/export_poisoned_tables.py

clean:
	rm -f $(MAIN).aux $(MAIN).log $(MAIN).out $(MAIN).toc

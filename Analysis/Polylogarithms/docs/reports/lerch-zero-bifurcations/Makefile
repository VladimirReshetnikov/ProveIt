PYTHON ?= python3
LATEX ?= pdflatex
ARTICLE = lerch_zero_bifurcations

.PHONY: pdf certify test diagnostics samples symbolic verify clean

pdf:
	cd article && $(LATEX) -interaction=nonstopmode -halt-on-error $(ARTICLE).tex
	cd article && $(LATEX) -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

certify:
	$(PYTHON) verification/certify.py

test:
	$(PYTHON) verification/test_exact.py

diagnostics:
	$(PYTHON) verification/diagnostics.py --full

samples:
	$(PYTHON) verification/sample_branches.py

symbolic:
	$(PYTHON) verification/symbolic_identities.py

verify: certify test

clean:
	rm -f article/$(ARTICLE).aux article/$(ARTICLE).log article/$(ARTICLE).out article/$(ARTICLE).toc

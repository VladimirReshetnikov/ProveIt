PYTHON ?= python3
LATEX ?= pdflatex
ARTICLE = direct_inverse_harmonic

.PHONY: all pdf verify clean
all: pdf
pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error $(ARTICLE).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(ARTICLE).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(ARTICLE).tex
verify:
	$(PYTHON) verification/verify.py
	$(PYTHON) verification/derive_amplitudes.py
clean:
	rm -f $(ARTICLE).aux $(ARTICLE).log $(ARTICLE).out $(ARTICLE).toc

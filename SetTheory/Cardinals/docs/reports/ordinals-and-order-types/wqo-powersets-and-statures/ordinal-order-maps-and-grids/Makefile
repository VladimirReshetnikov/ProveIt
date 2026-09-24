PYTHON ?= python3
PDFLATEX ?= pdflatex
PAPER = ordinal_order_maps

.PHONY: all pdf verify demo clean
all: pdf
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(PAPER).tex
verify:
	$(PYTHON) code/verify.py
	$(PYTHON) code/profiles.py
demo:
	$(PYTHON) code/ordinal_maps.py --demo
clean:
	rm -f $(PAPER).aux $(PAPER).log $(PAPER).out $(PAPER).toc

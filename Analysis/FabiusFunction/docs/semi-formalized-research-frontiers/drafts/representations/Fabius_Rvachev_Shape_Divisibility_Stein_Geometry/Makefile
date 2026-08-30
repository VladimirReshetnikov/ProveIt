PYTHON ?= python3
LATEX ?= pdflatex
REPORT := fabius_rvachev_frontier_report

.PHONY: all figures pdf clean

all: figures pdf

figures:
	$(PYTHON) rvachev_frontier_experiments.py --output-dir numerical_output

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error $(REPORT).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(REPORT).tex
	$(LATEX) -interaction=nonstopmode -halt-on-error $(REPORT).tex

clean:
	rm -f $(REPORT).aux $(REPORT).log $(REPORT).out $(REPORT).toc $(REPORT).lof

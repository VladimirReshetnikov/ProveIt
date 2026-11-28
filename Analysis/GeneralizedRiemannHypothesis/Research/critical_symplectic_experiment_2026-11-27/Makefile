PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all paper profiles exact simulations clean
all: paper

paper:
	$(LATEX) -interaction=nonstopmode -halt-on-error paper.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error paper.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error paper.tex

profiles:
	$(PYTHON) code/critical_profiles.py

exact:
	$(PYTHON) code/exact_binary_experiment.py

simulations:
	$(PYTHON) code/pencil_checks.py

clean:
	rm -f paper.aux paper.log paper.out paper.toc

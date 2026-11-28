PYTHON ?= python3
PDFLATEX ?= pdflatex
MC_REPETITIONS ?= 5000
MAIN = finite_observation_and_critical_recovery

.PHONY: all pdf verify

all: pdf

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(MAIN).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(MAIN).tex

verify:
	$(PYTHON) code/verify_hidden_forms.py --repetitions $(MC_REPETITIONS)
	$(PYTHON) code/verify_analytic_algebra.py

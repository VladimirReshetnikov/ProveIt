PYTHON ?= python3
PDFLATEX ?= pdflatex
LATEXFLAGS = -interaction=nonstopmode -halt-on-error

.PHONY: all pdf check figures clean

all: pdf

pdf:
	$(PDFLATEX) $(LATEXFLAGS) paper.tex
	$(PDFLATEX) $(LATEXFLAGS) paper.tex
	$(PDFLATEX) $(LATEXFLAGS) paper.tex
	cd companion && $(PDFLATEX) $(LATEXFLAGS) critical_profile.tex
	cd companion && $(PDFLATEX) $(LATEXFLAGS) critical_profile.tex

check:
	$(PYTHON) code/cycle_laws.py --self-check
	$(PYTHON) code/verify.py --output results/independent_enumeration.json
	$(PYTHON) code/verify_anchors.py --output results/anchor_verification.json
	$(PYTHON) companion/code/verify.py

figures:
	$(PYTHON) code/make_figures.py

clean:
	rm -f paper.aux paper.log paper.out paper.toc build.log
	rm -f companion/critical_profile.aux companion/critical_profile.log companion/critical_profile.out

.PHONY: all pdf test clean

REPORT := coarse_jump_spectra
BUILD := build
PYTHON ?= python3
PDFLATEX ?= pdflatex

all: pdf test

pdf:
	mkdir -p $(BUILD)
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD) $(REPORT).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD) $(REPORT).tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory=$(BUILD) $(REPORT).tex
	cp $(BUILD)/$(REPORT).pdf $(REPORT).pdf

test:
	cd code && PYTHONDONTWRITEBYTECODE=1 $(PYTHON) -m unittest -v test_finite.py

clean:
	rm -rf $(BUILD) code/__pycache__

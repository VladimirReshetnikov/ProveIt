LATEX ?= pdflatex
LATEXFLAGS ?= -interaction=nonstopmode -halt-on-error -file-line-error
PYTHON ?= python3
MANUSCRIPT = holder_zygmund_spectra

.PHONY: all build verify clean

all: build

# Three passes settle the table of contents, references, and destinations.
build:
	$(LATEX) $(LATEXFLAGS) $(MANUSCRIPT).tex
	$(LATEX) $(LATEXFLAGS) $(MANUSCRIPT).tex
	$(LATEX) $(LATEXFLAGS) $(MANUSCRIPT).tex

verify:
	cd verification && $(PYTHON) verify.py --output results.json

# Preserve the final PDF, source, exact results, and documentation.
clean:
	$(RM) $(MANUSCRIPT).aux $(MANUSCRIPT).log $(MANUSCRIPT).out
	$(RM) $(MANUSCRIPT).toc $(MANUSCRIPT).fls $(MANUSCRIPT).fdb_latexmk
	$(RM) $(MANUSCRIPT).synctex.gz

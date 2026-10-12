PYTHON ?= python
PDFLATEX ?= pdflatex
LATEXFLAGS = -no-shell-escape -interaction=nonstopmode -halt-on-error

.PHONY: all pdf verify exact numerical clean
all: pdf verify
pdf: main.tex
	$(PDFLATEX) $(LATEXFLAGS) main.tex
	$(PDFLATEX) $(LATEXFLAGS) main.tex
	$(PDFLATEX) $(LATEXFLAGS) main.tex

verify: exact numerical
exact:
	$(PYTHON) verification/verify.py --mode exact --output verification/exact_results.json
numerical:
	$(PYTHON) verification/verify.py --mode numerical --output verification/numerical_results.json

clean:
	rm -f main.aux main.log main.out main.toc

PYTHON ?= python3
LATEXMK ?= latexmk

.PHONY: all pdf exact numeric verify clean
all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

exact:
	$(PYTHON) src/verify_exact.py
	$(PYTHON) src/verify_s4_obstruction.py
	$(PYTHON) src/verify_trace_coefficients.py

numeric:
	$(PYTHON) src/verify_numeric.py

verify: exact numeric

clean:
	$(LATEXMK) -c article.tex

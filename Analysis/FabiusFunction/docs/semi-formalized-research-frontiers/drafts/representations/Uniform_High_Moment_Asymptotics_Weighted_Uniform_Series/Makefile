PYTHON ?= python3
.PHONY: all coefficients check tables pdf clean
all: coefficients check tables pdf
coefficients:
	$(PYTHON) code/coefficients.py
check:
	$(PYTHON) code/test_results.py
tables:
	$(PYTHON) code/experiments.py
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
clean:
	latexmk -c article.tex

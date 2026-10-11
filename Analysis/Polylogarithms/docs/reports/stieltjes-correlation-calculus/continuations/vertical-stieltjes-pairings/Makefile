PYTHON ?= python3
.PHONY: all pdf checks clean
all: checks pdf
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
checks:
	$(PYTHON) verification/exact_checks.py
	$(PYTHON) verification/numerical_checks.py core
	$(PYTHON) verification/numerical_checks.py extensions
	$(PYTHON) verification/complex_safe_replay.py
clean:
	latexmk -c article.tex

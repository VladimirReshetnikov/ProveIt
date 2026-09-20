PYTHON ?= python3

.PHONY: all verify pdf clean
all: verify pdf

verify:
	$(PYTHON) code/verify.py

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex
	find code -type d -name __pycache__ -exec rm -rf {} +

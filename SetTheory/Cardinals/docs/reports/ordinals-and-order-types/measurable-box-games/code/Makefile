PYTHON ?= python3

.PHONY: all pdf verify clean
all: pdf verify

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify_certificates.py
	$(PYTHON) verify_certificates.py --check certificates.json
	$(PYTHON) formal_series.py --degree 10

clean:
	latexmk -c article.tex

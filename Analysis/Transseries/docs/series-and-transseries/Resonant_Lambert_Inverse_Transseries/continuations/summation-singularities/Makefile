PYTHON ?= python3
LATEXMK ?= latexmk
ARTICLE = polylogarithmic_reversion

.PHONY: all pdf tables checks package clean

all: pdf

pdf: tables
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

tables:
	$(PYTHON) scripts/make_figures.py

checks:
	$(PYTHON) scripts/verify_angular.py
	$(PYTHON) scripts/verify_lambert.py
	$(PYTHON) scripts/verify_endpoint.py
	$(PYTHON) scripts/make_figures.py

package: pdf
	$(PYTHON) scripts/package.py

clean:
	$(LATEXMK) -c $(ARTICLE).tex

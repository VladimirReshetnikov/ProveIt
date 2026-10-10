PYTHON ?= python
LATEXMK ?= latexmk

.PHONY: all verify reproduce certificates pdf clean

# Build after reproduction has completed, including with make -j.
all: verify
	$(MAKE) pdf

verify: reproduce certificates

reproduce:
	$(PYTHON) code/reproduce.py

certificates:
	$(PYTHON) code/exact_certificates.py --k 1 2 5 10 20 50 100 200 500 > data/exact_sandwich_certificates.jsonl

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error spectral_concentration.tex

clean:
	$(LATEXMK) -c spectral_concentration.tex

PYTHON ?= python3

.PHONY: all check data pdf clean
all: check pdf

check:
	$(PYTHON) verify.py
	$(PYTHON) minimal_check.py

data:
	$(PYTHON) verify.py --write-data

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex

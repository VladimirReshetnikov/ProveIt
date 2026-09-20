PYTHON ?= python3

.PHONY: all article verify tables clean
all: article

article:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --max-n 200 --output data/verification.json

tables:
	$(PYTHON) code/make_tables.py

clean:
	latexmk -c article.tex

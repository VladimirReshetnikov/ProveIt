PYTHON ?= python3
LATEXMK ?= latexmk
ARTICLE = Confluent_Critical_Transseries

.PHONY: all pdf checks exact clean
all: pdf

pdf: $(ARTICLE).tex data/coefficient_table.tex data/inversion_table.tex
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error $(ARTICLE).tex

checks:
	$(PYTHON) code/verify.py --part all

exact:
	$(PYTHON) code/verify.py --part exact

clean:
	$(LATEXMK) -c $(ARTICLE).tex

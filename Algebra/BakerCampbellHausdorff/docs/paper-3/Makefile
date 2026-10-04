PYTHON ?= python3
DEGREE ?= 10

.PHONY: all paper verify clean
all: paper
paper:
	latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
verify:
	$(PYTHON) code/verify_bch.py --degree $(DEGREE) --out data
clean:
	latexmk -c paper.tex

PYTHON ?= python
LATEXMK ?= latexmk

.PHONY: all pdf verify clean

all: pdf

pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --max-n 4096 --dps 90 > data/verification_run.txt
	@cat data/verification_run.txt

clean:
	$(LATEXMK) -c article.tex

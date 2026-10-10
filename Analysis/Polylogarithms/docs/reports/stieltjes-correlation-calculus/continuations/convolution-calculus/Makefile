PYTHON ?= python3

.PHONY: all pdf check quick clean
all: pdf

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error Stieltjes_Convolution_Calculus.tex

check:
	$(PYTHON) verification/run_all.py

quick:
	$(PYTHON) verification/run_all.py --quick

clean:
	latexmk -c Stieltjes_Convolution_Calculus.tex

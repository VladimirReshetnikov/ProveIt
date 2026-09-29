.PHONY: pdf verify figures all clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error inverse_digamma_spectral.tex
	pdflatex -interaction=nonstopmode -halt-on-error inverse_digamma_spectral.tex
	pdflatex -interaction=nonstopmode -halt-on-error inverse_digamma_spectral.tex

verify:
	python verification/verify.py
	python verification/contour_check.py

figures:
	python verification/make_figures.py

all: verify figures pdf

clean:
	rm -f inverse_digamma_spectral.aux inverse_digamma_spectral.log
	rm -f inverse_digamma_spectral.out inverse_digamma_spectral.toc
	rm -rf verification/__pycache__

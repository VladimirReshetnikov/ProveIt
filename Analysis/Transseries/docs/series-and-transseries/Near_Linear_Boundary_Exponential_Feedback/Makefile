PYTHON ?= python3
TEX = near_linear_feedback

.PHONY: all pdf verify clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex
verify:
	$(PYTHON) code/verify.py
clean:
	rm -f $(TEX).aux $(TEX).log $(TEX).out $(TEX).toc

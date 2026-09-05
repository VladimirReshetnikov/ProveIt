TEX = q_binomial_coefficient_calculus
PYTHON ?= python3

.PHONY: pdf verify clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex
	pdflatex -interaction=nonstopmode -halt-on-error $(TEX).tex

verify:
	$(PYTHON) verify_identities.py --group all

clean:
	rm -f $(TEX).aux $(TEX).log $(TEX).out $(TEX).toc

PYTHON ?= python

.PHONY: pdf verify derive clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify.py --max-k 40 --export-count 251

derive:
	$(PYTHON) code/derive.py --max-d 6 --check-only

clean:
	rm -f article.aux article.log article.out article.toc

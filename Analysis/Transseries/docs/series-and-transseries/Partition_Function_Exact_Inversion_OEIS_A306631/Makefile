PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf exact numerics clean
all: pdf exact

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

exact:
	$(PYTHON) code/certify.py --output results/certificate.json --details results/finite_comparisons.csv
	$(PYTHON) code/series.py --order 12 --output results/coefficients.json

numerics:
	$(PYTHON) code/experiments.py --output results/numerics.json

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

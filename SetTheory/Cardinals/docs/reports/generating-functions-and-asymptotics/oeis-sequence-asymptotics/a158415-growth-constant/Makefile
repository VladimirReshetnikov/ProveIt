PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all pdf verify regenerate clean

all: pdf verify

pdf:
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify_certificate.py --output data/verification_results.json
	$(PYTHON) certify_upper_bound.py --output data/upper_bound_certificate.json
	$(PYTHON) analyze_counts.py

regenerate:
	$(PYTHON) certified_enumerate.py --max-n 28 --precision 256 --output data
	$(MAKE) verify

clean:
	rm -f article.aux article.log article.out article.toc
	rm -rf __pycache__

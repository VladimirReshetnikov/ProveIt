PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify verify-all clean
all: pdf

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

# Do not use Python's -O option: assertions form part of these checks.
verify:
	$(PYTHON) certify_integer.py --output integer_certificate.json > integer_certificate.log
	cat integer_certificate.log

verify-all: verify
	$(PYTHON) certify_constants.py --output constants_certificate.json > constants_certificate.log
	cat constants_certificate.log
	$(PYTHON) verify_algebra.py --output algebra_certificate.json > algebra_certificate.log
	cat algebra_certificate.log

clean:
	rm -f article.aux article.log article.out article.toc

PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all pdf verify symbolic numerical check clean
all: pdf

pdf: article.pdf

article.pdf: article.tex data/error_table.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) verify.py --max-index 40 --offsets 12 --output-dir data
	$(PYTHON) make_error_table.py

symbolic:
	$(PYTHON) symbolic_certificates.py > data/symbolic_verification.txt
	cat data/symbolic_verification.txt

numerical:
	$(PYTHON) numerical_checks.py

check: verify symbolic numerical

clean:
	rm -f article.aux article.log article.out article.toc

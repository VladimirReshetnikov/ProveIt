PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all test audit example benchmark tables pdf verify clean
all: test verify pdf

test:
	$(PYTHON) -m unittest discover -s tests -v

audit:
	$(PYTHON) code/audit.py

example:
	$(PYTHON) code/example.py

benchmark:
	$(PYTHON) code/benchmark.py --repeats 5

tables:
	$(PYTHON) code/make_tables.py

pdf: tables
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex

verify:
	$(PYTHON) code/verify_example.py

clean:
	rm -f article.aux article.log article.out article.toc
	find code tests -type d -name __pycache__ -prune -exec rm -rf {} +

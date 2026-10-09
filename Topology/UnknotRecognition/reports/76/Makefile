.PHONY: all pdf test audit benchmark examples clean
PYTHON ?= python
all: test pdf
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
test:
	$(PYTHON) -m unittest discover -s tests -v
audit:
	$(PYTHON) code/audit.py --output data/audit-rerun.json
benchmark:
	$(PYTHON) code/benchmark.py --output data/benchmarks-rerun.json --csv data/benchmarks-rerun.csv --repeats 3
examples:
	$(PYTHON) code/compressed_search.py examples/huge_repetition.json --certificate examples/huge-rerun.cert.json --output examples/huge-rerun.result.json
	$(PYTHON) code/checker.py examples/huge_repetition.json examples/huge-rerun.cert.json
clean:
	latexmk -c article.tex

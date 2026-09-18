.PHONY: test benchmark report clean
PYTHON ?= python

test:
	$(PYTHON) -m unittest discover -s tests -v

benchmark:
	$(PYTHON) tools/benchmark.py --repeats 3 --cap 20
	$(PYTHON) tools/summarize_results.py

report:
	cd docs && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd docs && pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f docs/report.aux docs/report.log docs/report.out docs/report.toc

.PHONY: test report benchmark clean

test:
	PYTHONHASHSEED=0 python -m unittest discover -s tests -v

report:
	python tools/benchmark_tables.py
	cd docs && pdflatex -interaction=nonstopmode -halt-on-error report.tex
	cd docs && pdflatex -interaction=nonstopmode -halt-on-error report.tex

benchmark:
	python tools/benchmark.py --seconds 8 --repetitions 5

clean:
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f docs/report.aux docs/report.log docs/report.out docs/report.toc

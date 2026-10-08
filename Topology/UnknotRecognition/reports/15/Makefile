.PHONY: test validate benchmark tables paper clean

test:
	python -m unittest discover -s tests -v
validate:
	python experiments/validate_algebra.py
	python experiments/validate_braids.py
	python experiments/validate_marked.py
benchmark:
	python experiments/benchmark.py
	python experiments/make_tables.py
tables:
	python experiments/make_tables.py
paper: tables
	cd article && pdflatex -halt-on-error -interaction=nonstopmode article.tex
	cd article && pdflatex -halt-on-error -interaction=nonstopmode article.tex
clean:
	find . -type d -name __pycache__ -prune -exec rm -rf {} +
	rm -f article/*.aux article/*.log article/*.out article/*.toc

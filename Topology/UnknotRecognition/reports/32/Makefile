.PHONY: test validate growth benchmark tables paper clean
PYTHON ?= python3

test:
	$(PYTHON) -m unittest discover -s tests -v
validate:
	$(PYTHON) experiments/validate.py
	$(PYTHON) experiments/check_bounds.py
growth:
	$(PYTHON) experiments/growth.py
benchmark:
	$(PYTHON) experiments/benchmark.py --rounds 5
tables:
	$(PYTHON) experiments/make_tables.py
paper:
	cd article && pdflatex -interaction=nonstopmode -halt-on-error graded_torus_scanning.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error graded_torus_scanning.tex
	cd article && pdflatex -interaction=nonstopmode -halt-on-error graded_torus_scanning.tex
clean:
	rm -f article/*.aux article/*.log article/*.out article/*.toc
	find . -type d -name __pycache__ -prune -exec rm -rf {} +

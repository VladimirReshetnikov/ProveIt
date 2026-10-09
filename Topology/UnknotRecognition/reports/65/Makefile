PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: test audit example benchmark tables pdf clean

test:
	@mkdir -p results
	@PYTHONPATH=code $(PYTHON) -m unittest discover -s tests -v > results/tests.txt 2>&1 || { cat results/tests.txt; exit 1; }
	@cat results/tests.txt

audit:
	@mkdir -p results
	@$(PYTHON) code/audit.py > results/audit.txt
	@cat results/audit.txt

example:
	@$(PYTHON) code/example.py > examples/example_run.txt
	@cat examples/example_run.txt

benchmark:
	@mkdir -p results
	@$(PYTHON) code/benchmark.py --repeats 3 > results/benchmark.txt
	@cat results/benchmark.txt

tables:
	@$(PYTHON) code/make_tables.py

pdf: tables
	@mkdir -p results
	@$(LATEX) -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass1.txt || { cat results/latex_pass1.txt; exit 1; }
	@$(LATEX) -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass2.txt || { cat results/latex_pass2.txt; exit 1; }
	@$(LATEX) -interaction=nonstopmode -halt-on-error article.tex > results/latex_pass3.txt || { cat results/latex_pass3.txt; exit 1; }

clean:
	rm -f article.aux article.log article.out article.toc
	find code tests -type d -name __pycache__ -prune -exec rm -rf {} +

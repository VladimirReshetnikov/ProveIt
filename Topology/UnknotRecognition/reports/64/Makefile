PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: test audit benchmark tables example check-example pdf checksums verify-checksums clean

test:
	@mkdir -p results
	$(PYTHON) -m unittest discover -s tests -v > results/tests.txt 2>&1
	@cat results/tests.txt

audit:
	$(PYTHON) code/audit.py > results/audit.txt
	@cat results/audit.txt

benchmark:
	$(PYTHON) code/benchmark.py > results/benchmark.txt
	@cat results/benchmark.txt

tables:
	$(PYTHON) code/make_tables.py

example:
	$(PYTHON) code/example.py > results/example.txt
	@cat results/example.txt

check-example:
	$(PYTHON) code/check_certificate.py examples/input.json examples/certificate.json

pdf: tables
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex > results/latex-final.txt
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex >> results/latex-final.txt
	$(LATEX) -interaction=nonstopmode -halt-on-error article.tex >> results/latex-final.txt

checksums:
	$(PYTHON) code/checksums.py

verify-checksums:
	$(PYTHON) code/checksums.py --verify

clean:
	rm -f article.aux article.log article.out article.toc
	find code tests -type d -name __pycache__ -prune -exec rm -rf {} +

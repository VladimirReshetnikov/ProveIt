PYTHON ?= python3

.PHONY: pdf exact symbolic check clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

exact:
	$(PYTHON) verify.py
	$(PYTHON) binary_checks.py

symbolic:
	$(PYTHON) symbolic_checks.py

check: exact symbolic

clean:
	latexmk -c article.tex
	rm -rf __pycache__

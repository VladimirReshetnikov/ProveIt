PYTHON ?= python
LATEXMK ?= latexmk

.PHONY: all check exact numeric tables pdf preview clean
all: check tables pdf preview
check: exact numeric
exact:
	$(PYTHON) code/verify_exact.py
numeric:
	$(PYTHON) code/verify_numeric.py --part 1
	$(PYTHON) code/verify_numeric.py --part 2
tables:
	$(PYTHON) code/build_tables.py
pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex
preview:
	cd integration && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error core-preview.tex
clean:
	$(LATEXMK) -c article.tex
	cd integration && $(LATEXMK) -c core-preview.tex

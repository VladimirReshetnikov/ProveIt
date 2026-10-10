PYTHON ?= python
LATEXMK ?= latexmk

.PHONY: all check exact numeric canary pdf integration-test clean
all: check pdf
check: exact numeric canary
exact:
	$(PYTHON) code/exact_coefficients.py --max-total 8
numeric:
	$(PYTHON) code/verify_numeric.py --dps 45
	$(PYTHON) code/verify_stieltjes_pairs.py
canary:
	$(PYTHON) code/polylog_derivative_canary.py
pdf:
	$(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error article.tex
integration-test:
	cd integration && $(LATEXMK) -pdf -interaction=nonstopmode -halt-on-error standalone.tex
clean:
	$(LATEXMK) -c article.tex
	cd integration && $(LATEXMK) -c standalone.tex

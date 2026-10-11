PYTHON ?= python3
.PHONY: all test exact numerical diagnostics pdf clean
all: test pdf
test: exact numerical
exact:
	$(PYTHON) code/verify_exact.py
numerical:
	$(PYTHON) code/verify_numerical.py
diagnostics:
	$(PYTHON) code/endpoint_diagnostics.py
pdf:
	cd article && latexmk -pdf -interaction=nonstopmode -halt-on-error endpoint_regularization.tex
clean:
	rm -f article/*.aux article/*.log article/*.out article/*.toc article/*.fls article/*.fdb_latexmk
	rm -rf code/__pycache__

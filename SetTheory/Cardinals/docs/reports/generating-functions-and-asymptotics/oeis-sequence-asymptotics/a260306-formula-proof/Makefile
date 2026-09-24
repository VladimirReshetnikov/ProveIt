PYTHON ?= python3

.PHONY: pdf check numerical clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error a260306_proof.tex

check:
	$(PYTHON) code/verify.py

numerical:
	$(PYTHON) code/numerical_check.py

clean:
	latexmk -c a260306_proof.tex

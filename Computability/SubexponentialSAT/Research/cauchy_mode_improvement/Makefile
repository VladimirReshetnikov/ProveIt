PYTHON ?= python3

.PHONY: pdf verify counts exhibits clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

verify:
	$(PYTHON) code/verify_modes.py

counts:
	$(PYTHON) code/count_modes.py

exhibits:
	$(PYTHON) code/build_exhibits.py

clean:
	latexmk -c report.tex

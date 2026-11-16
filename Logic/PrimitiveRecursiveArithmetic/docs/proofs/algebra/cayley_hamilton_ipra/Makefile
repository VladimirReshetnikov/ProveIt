.PHONY: pdf check clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error cayley_hamilton_ipra.tex

check:
	python3 code/verify_core.py --output verification/core_results.json
	python3 code/verify_trace.py

clean:
	latexmk -c cayley_hamilton_ipra.tex


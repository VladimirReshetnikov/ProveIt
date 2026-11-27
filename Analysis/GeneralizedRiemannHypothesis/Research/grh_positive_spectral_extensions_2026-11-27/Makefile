.PHONY: pdf checks clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

checks:
	python3 scripts/filter_checks.py
	python3 scripts/real_weight_checks.py --output results/real_weight_checks.json

clean:
	latexmk -c report.tex


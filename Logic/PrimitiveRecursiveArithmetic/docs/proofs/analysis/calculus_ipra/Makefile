.PHONY: pdf check

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

check:
	python3 code/bernoulli_em.py --validate --output code/validation.json
	python3 code/integral_demo.py --output code/integral_validation.json

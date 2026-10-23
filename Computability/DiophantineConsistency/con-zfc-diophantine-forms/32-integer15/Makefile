.PHONY: verify pdf
verify:
	python3 verify_all.py
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

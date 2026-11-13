.PHONY: pdf verify clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 checkers/verify.py
	python3 mathematics/mathematical_checks.py

clean:
	latexmk -c report.tex

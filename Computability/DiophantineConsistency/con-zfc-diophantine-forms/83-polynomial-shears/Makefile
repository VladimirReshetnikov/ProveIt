.PHONY: pdf verify verify-optimized

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 verify.py

verify-optimized:
	python3 verify.py --optimized

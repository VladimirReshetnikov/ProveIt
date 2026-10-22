.PHONY: pdf verify verify-full

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

verify:
	python3 reproduce.py

verify-full:
	python3 reproduce.py --full-t4

.PHONY: all pdf verify
all: pdf verify
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
verify:
	python3 verify.py > verification.txt
	cat verification.txt

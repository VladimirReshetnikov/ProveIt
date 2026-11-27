.PHONY: pdf check clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
check:
	python3 check.py
clean:
	rm -f paper.aux paper.log paper.out

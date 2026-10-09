.PHONY: all reproduce pdf test clean
all: reproduce pdf
reproduce:
	python3 code/reproduce.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
	pdflatex -interaction=nonstopmode -halt-on-error paper.tex
test:
	python3 -m unittest discover -s code -p 'test_*.py' -v
	python3 code/sampling_checks.py
clean:
	rm -f paper.aux paper.log paper.out paper.toc

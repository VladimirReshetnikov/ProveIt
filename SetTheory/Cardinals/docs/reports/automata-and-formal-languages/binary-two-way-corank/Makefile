.PHONY: all audit clean

all: article.pdf

article.pdf: article.tex references.bib $(wildcard sections/*.tex)
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	bibtex article
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

audit:
	python3 code/run_all.py --output-dir reproduced

clean:
	rm -f article.aux article.log article.out article.toc article.blg

.PHONY: all check pdf clean

all: check pdf

check:
	python3 code/verify.py --order 70

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

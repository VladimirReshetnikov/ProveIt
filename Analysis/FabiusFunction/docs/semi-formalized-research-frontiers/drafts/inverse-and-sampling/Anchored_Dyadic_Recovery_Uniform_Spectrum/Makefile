.PHONY: all pdf check clean
all: pdf check
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
check:
	python code/verify.py
clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

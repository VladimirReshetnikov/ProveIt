.PHONY: all pdf check diagnostics clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
check:
	python code/verify.py --order 24
diagnostics:
	python code/majorant.py
clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

.PHONY: all pdf verify clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify.py --degree 320
clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

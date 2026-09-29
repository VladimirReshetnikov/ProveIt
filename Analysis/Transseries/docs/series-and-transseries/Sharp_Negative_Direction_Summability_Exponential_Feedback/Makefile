.PHONY: all pdf exact verify clean
all: pdf

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

exact:
	python code/verify.py --order 120 --exact-only

verify:
	python code/verify.py --order 120

clean:
	rm -f article.aux article.log article.out article.toc

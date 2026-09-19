.PHONY: all verify figures pdf clean
all: verify pdf
verify:
	python code/verify.py
figures:
	python code/make_figures.py
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
clean:
	rm -f article.aux article.log article.out article.toc

.PHONY: all pdf verify figures clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python code/verify.py > data/verification_log.txt
figures:
	python code/make_figures.py
clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

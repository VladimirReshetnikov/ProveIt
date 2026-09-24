.PHONY: pdf verify figure clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/independent_check.py
	python code/verify.py --long

figure:
	python code/make_figure.py

clean:
	rm -f article.aux article.log article.out article.toc

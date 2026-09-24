.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/verify.py

clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

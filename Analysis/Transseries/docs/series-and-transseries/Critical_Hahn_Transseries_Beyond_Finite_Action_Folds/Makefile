.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/verify.py --max-n 4096

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

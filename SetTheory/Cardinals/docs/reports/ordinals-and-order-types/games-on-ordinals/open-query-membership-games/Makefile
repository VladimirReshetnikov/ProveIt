.PHONY: pdf verify clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python3 code/verify.py --max-n 6
clean:
	rm -f article.aux article.log article.out article.toc article.fdb_latexmk article.fls

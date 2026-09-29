.PHONY: pdf verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/verify_conditioning.py --proposals 160000
	python code/make_tables.py

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

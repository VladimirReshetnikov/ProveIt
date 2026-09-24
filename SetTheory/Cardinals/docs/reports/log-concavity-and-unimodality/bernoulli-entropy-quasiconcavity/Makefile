.PHONY: pdf check symbolic figures clean
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
check:
	python code/verify_exact.py
symbolic:
	python code/verify_symbolic.py
figures:
	python code/make_figures.py
clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

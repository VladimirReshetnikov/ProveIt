.PHONY: pdf check clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

check:
	python verify_results.py

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

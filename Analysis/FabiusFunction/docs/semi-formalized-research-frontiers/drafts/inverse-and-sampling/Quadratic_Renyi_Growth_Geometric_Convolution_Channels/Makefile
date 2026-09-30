.PHONY: pdf check clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

check:
	python checks/verify.py --dps 100

clean:
	rm -f article.aux article.log article.out article.toc

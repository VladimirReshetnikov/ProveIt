.PHONY: all pdf exact numeric verify clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
exact:
	python verification/verify.py --exact-only
numeric:
	python verification/verify.py --numeric-only --dps 40
verify: exact numeric
clean:
	rm -f article.aux article.log article.out article.toc

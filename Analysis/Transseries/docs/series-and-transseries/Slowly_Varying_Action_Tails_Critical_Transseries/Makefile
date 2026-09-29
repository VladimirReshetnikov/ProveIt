.PHONY: pdf exact verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

exact:
	python verification/verify.py --exact-only

verify:
	python verification/verify.py
	python verification/make_tables.py

clean:
	rm -f article.aux article.log article.out article.toc

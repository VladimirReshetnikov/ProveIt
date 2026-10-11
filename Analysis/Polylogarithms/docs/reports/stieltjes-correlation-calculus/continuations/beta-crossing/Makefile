.PHONY: pdf exact numeric check clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

exact:
	python verification/check_exact.py

numeric:
	python verification/check_numeric.py --dps 65

check: exact numeric

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk article.synctex.gz

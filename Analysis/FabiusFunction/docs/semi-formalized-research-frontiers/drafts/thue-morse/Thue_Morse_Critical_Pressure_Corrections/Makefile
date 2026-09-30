.PHONY: pdf verify identities clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	OPENBLAS_NUM_THREADS=1 python code/verify.py

identities:
	python code/verify.py --identities-only --output-dir fresh_checks

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk

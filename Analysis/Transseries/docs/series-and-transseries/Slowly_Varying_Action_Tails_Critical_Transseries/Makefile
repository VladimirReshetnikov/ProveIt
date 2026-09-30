.PHONY: pdf exact verify clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

exact:
	python verification/verify.py --exact-only

# ed. 2026-09-29: writes into rerun/, not into the recorded verification/.
verify:
	python verification/verify.py
	python verification/make_tables.py --input rerun/results.json

clean:
	rm -f article.aux article.log article.out article.toc

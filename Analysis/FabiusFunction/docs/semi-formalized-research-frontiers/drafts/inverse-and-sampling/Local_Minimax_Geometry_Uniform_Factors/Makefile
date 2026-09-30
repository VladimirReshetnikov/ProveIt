.PHONY: pdf check diagnostics clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

check:
	python verify_results.py --output recomputed/exact.json

diagnostics:
	python verify_results.py --numerics --output recomputed/full.json

clean:
	rm -f article.aux article.log article.out article.toc

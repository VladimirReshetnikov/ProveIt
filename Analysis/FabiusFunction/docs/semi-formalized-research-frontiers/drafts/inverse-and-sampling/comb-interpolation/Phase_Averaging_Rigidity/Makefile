.PHONY: all pdf check exact clean
all: pdf
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
check:
	python verify.py --output verification.json
exact:
	python verify.py --skip-numerical --output exact_results.json
clean:
	rm -f article.aux article.log article.out article.toc

.PHONY: all pdf verify verify-fast clean

all: pdf

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

verify:
	python verification/verify.py --output verification/results.json

verify-fast:
	python verification/verify.py --skip-lateral --output verification/results-fast.json

clean:
	rm -f article.aux article.log article.out article.toc

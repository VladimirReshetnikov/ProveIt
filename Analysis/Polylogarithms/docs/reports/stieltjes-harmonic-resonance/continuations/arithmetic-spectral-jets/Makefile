.PHONY: all pdf verify clean
all: pdf verify
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python verification/verify_exact.py
	python verification/verify_numerical.py --full
clean:
	latexmk -c article.tex
	latexmk -c article_singlefile.tex

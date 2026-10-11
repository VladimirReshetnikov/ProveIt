.PHONY: all pdf verify manifest clean
all: pdf verify
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
verify:
	python verification/verify.py --part all
manifest:
	python verification/check_manifest.py
clean:
	latexmk -c article.tex

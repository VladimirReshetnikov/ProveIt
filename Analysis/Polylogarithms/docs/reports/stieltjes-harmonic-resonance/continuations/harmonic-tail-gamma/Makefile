.PHONY: all pdf standalone verify

all: pdf standalone

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
	cp build/article.pdf article.pdf

standalone:
	python3 tools/make_standalone.py

verify:
	python3 verification/run_all.py

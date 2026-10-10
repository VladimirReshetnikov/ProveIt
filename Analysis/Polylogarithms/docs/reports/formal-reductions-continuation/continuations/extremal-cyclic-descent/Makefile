.PHONY: all pdf verify diagnostics flatten clean

all: pdf flatten

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build article.tex
	cp build/article.pdf article.pdf

flatten:
	python code/flatten_tex.py

verify:
	python code/replay_all.py

diagnostics:
	python code/replay_all.py --diagnostics

clean:
	latexmk -c -outdir=build article.tex

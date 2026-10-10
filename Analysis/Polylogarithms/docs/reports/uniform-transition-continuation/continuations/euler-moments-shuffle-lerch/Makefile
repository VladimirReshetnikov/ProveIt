.PHONY: all pdf source verify numerical figures clean

all: pdf

source:
	python3 code/build_article.py

pdf:
	python3 code/build_article.py --compile

verify:
	python3 code/verify_all.py

numerical:
	python3 code/verify_all.py --numerical

figures:
	python3 code/make_figures.py

clean:
	latexmk -c article.tex

.PHONY: all verify tables clean
all: article.pdf

verify:
	python3 code/verify.py --report data/verification.json
	python3 code/check_profile.py data/profiles_18.csv

tables:
	python3 code/make_tables.py

article.pdf: article.tex $(wildcard tex/*.tex)
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

clean:
	latexmk -c article.tex

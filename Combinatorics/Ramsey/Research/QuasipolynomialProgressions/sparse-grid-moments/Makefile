.PHONY: all pdf check clean
all: pdf
pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
check:
	python3 verify.py --fields 2,3,4,5,7 --output verification_results.json
clean:
	latexmk -c article.tex

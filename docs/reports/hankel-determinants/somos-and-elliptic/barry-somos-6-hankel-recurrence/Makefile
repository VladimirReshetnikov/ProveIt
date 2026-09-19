.PHONY: all pdf verify symbolic quick clean

all: pdf verify

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

verify:
	python code/verify.py

symbolic:
	python code/symbolic_certificates.py

quick:
	python code/verify.py --quick

clean:
	latexmk -c article.tex

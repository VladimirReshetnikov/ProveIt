.PHONY: all verify optional clean
all: article.pdf

article.pdf: article.tex
	latexmk -pdf -interaction=nonstopmode article.tex

verify:
	python code/verify.py

optional:
	python code/derive_quartic.py
	python code/symbolic_certificate.py
	python code/asymptotics.py

clean:
	latexmk -c

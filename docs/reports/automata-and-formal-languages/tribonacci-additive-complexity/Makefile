PYTHON ?= python3
LATEX ?= pdflatex

.PHONY: all pdf verify tables clean
all: pdf

pdf:
	mkdir -p build
	$(LATEX) -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	$(LATEX) -interaction=nonstopmode -halt-on-error -output-directory=build article.tex
	cp build/article.pdf article.pdf

verify:
	$(PYTHON) code/verify.py

tables:
	$(PYTHON) code/make_tables.py

clean:
	rm -rf build code/__pycache__

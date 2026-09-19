PYTHON ?= python3
PDFLATEX ?= pdflatex

.NOTPARALLEL:

.PHONY: all verify tables pdf clean
all: verify tables pdf

verify:
	$(PYTHON) code/verify.py > data/verification_console.txt
	$(PYTHON) code/test_api.py > data/api_tests.txt 2>&1

tables:
	$(PYTHON) code/make_tex_tables.py

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error article.tex

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
	rm -rf code/__pycache__

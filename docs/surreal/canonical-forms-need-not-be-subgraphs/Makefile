PYTHON ?= python3

.PHONY: all check check-core check-sparse clean

all: surreal_graphs.pdf

surreal_graphs.pdf: surreal_graphs.tex references.bib
	pdflatex -interaction=nonstopmode -halt-on-error surreal_graphs.tex
	pdflatex -interaction=nonstopmode -halt-on-error surreal_graphs.tex
	pdflatex -interaction=nonstopmode -halt-on-error surreal_graphs.tex

check: check-core check-sparse

check-core:
	$(PYTHON) code/verify.py

check-sparse:
	$(PYTHON) code/verify_sparse.py

clean:
	rm -f surreal_graphs.aux surreal_graphs.bbl surreal_graphs.blg
	rm -f surreal_graphs.log surreal_graphs.out surreal_graphs.toc
	rm -f surreal_graphs.fls surreal_graphs.fdb_latexmk
	rm -rf code/__pycache__

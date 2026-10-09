PYTHON ?= python

.PHONY: all verify figures pdf clean
all: verify figures pdf

verify:
	$(PYTHON) code/verify_exact.py
	$(PYTHON) code/verify_numeric.py

figures:
	$(PYTHON) code/make_figures.py

pdf:
	$(PYTHON) code/build_pdf.py

clean:
	$(PYTHON) -c "from pathlib import Path; [p.unlink() for ext in ('aux','bbl','blg','fdb_latexmk','fls','log','out','toc') if (p:=Path('article.'+ext)).exists()]"

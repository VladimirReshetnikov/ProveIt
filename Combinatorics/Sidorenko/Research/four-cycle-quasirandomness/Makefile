PYTHON ?= python

.PHONY: all verify diagnostics pdf clean
all: verify diagnostics pdf
verify:
	$(PYTHON) code/verify_exact.py
diagnostics:
	$(PYTHON) code/diagnostics.py
pdf:
	$(PYTHON) code/build_pdf.py
clean:
	rm -f article.aux article.blg article.fdb_latexmk article.fls article.log article.out article.toc

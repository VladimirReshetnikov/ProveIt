PYTHON ?= python3
PDFLATEX ?= pdflatex
TEX := rueppel_hankel.tex

.PHONY: all pdf test verify table clean
all: pdf
pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(TEX)
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(TEX)
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error $(TEX)
test:
	$(PYTHON) -m unittest discover -s tests -v
verify:
	$(PYTHON) code/verify.py
table:
	$(PYTHON) code/make_table.py
clean:
	rm -f rueppel_hankel.aux rueppel_hankel.log rueppel_hankel.out rueppel_hankel.toc
	rm -f rueppel_hankel.fls rueppel_hankel.fdb_latexmk

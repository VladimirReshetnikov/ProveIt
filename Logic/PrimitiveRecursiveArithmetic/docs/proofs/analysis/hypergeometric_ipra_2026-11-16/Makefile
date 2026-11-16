.PHONY: all pdf validate inventory checksums clean

PDFLATEX ?= pdflatex
PYTHON ?= python3

all: inventory validate pdf checksums

inventory:
	$(PYTHON) code/build_inventory.py

validate:
	$(PYTHON) code/validate_finite.py --output evidence/validation.json --dps 100

pdf:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error report.tex

checksums:
	find . -type f ! -name SHA256SUMS.txt ! -path './.git/*' -print0 | \
	  sort -z | xargs -0 sha256sum > SHA256SUMS.txt

clean:
	rm -f report.aux report.log report.out report.toc report.fdb_latexmk \
	  report.fls report.synctex.gz

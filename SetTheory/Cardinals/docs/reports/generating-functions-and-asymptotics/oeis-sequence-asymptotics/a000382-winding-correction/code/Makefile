PYTHON ?= python3
PDF_SCRIPT ?= /home/oai/skills/pdfs/scripts/latex_to_pdf.py

.PHONY: all verify pdf clean

all: verify pdf

verify:
	$(PYTHON) verify.py | tee verification_output.txt

pdf:
	$(PYTHON) $(PDF_SCRIPT) article.tex -o article.pdf

clean:
	rm -f article.aux article.log article.out article.toc article.pdf

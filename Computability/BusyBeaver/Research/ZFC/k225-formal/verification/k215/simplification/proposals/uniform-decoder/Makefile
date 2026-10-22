PDFLATEX ?= pdflatex
PDF_BUILD ?= .build-pdf

.PHONY: pdf clean

pdf: report.tex
	mkdir -p "$(PDF_BUILD)"
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory="$(PDF_BUILD)" report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory="$(PDF_BUILD)" report.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error -output-directory="$(PDF_BUILD)" report.tex
	cp "$(PDF_BUILD)/report.pdf" report.pdf

clean:
	rm -f "$(PDF_BUILD)/report.aux" "$(PDF_BUILD)/report.log" "$(PDF_BUILD)/report.out" "$(PDF_BUILD)/report.toc" "$(PDF_BUILD)/report.pdf"

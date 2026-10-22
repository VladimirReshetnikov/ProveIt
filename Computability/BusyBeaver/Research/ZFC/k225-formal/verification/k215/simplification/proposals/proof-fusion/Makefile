.PHONY: pdf clean

pdf: report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

clean:
	rm -f report.aux report.log report.out report.toc report.fdb_latexmk report.fls

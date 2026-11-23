.PHONY: pdf validate clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -interaction=nonstopmode -halt-on-error report.tex

validate:
	python3 code/validate.py

clean:
	rm -f report.aux report.log report.out report.toc

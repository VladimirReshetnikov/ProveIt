.PHONY: pdf check clean

pdf:
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error report.tex

check:
	python3 code/verify_all.py

clean:
	rm -f report.aux report.log report.out report.toc

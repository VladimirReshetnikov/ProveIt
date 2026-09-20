.PHONY: all verify clean
all:
	pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
	pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
	pdflatex -interaction=nonstopmode -halt-on-error surreal_product_birthdays.tex
verify:
	python3 code/verify.py
clean:
	rm -f *.aux *.bbl *.blg *.log *.out *.toc *.fls *.fdb_latexmk

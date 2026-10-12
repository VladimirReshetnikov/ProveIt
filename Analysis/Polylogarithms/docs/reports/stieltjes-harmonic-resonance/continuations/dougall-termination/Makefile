.PHONY: all article preview exact numeric clean
all: article preview
article:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
preview:
	cd integration && pdflatex -interaction=nonstopmode -halt-on-error preview.tex
	cd integration && pdflatex -interaction=nonstopmode -halt-on-error preview.tex
exact:
	python code/verify_exact.py
numeric:
	python code/verify_numeric.py --part 1
	python code/verify_numeric.py --part 2
	python code/verify_numeric.py --part 3
clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
	rm -f integration/preview.aux integration/preview.log integration/preview.out

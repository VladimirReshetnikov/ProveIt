# Requires a standard TeX Live or MiKTeX installation. No shell escape.
.PHONY: pdf verify clean
pdf:
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof-simplification.tex
	pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error proof-simplification.tex
verify:
	python3 verify.py
clean:
	rm -f proof-simplification.aux proof-simplification.log proof-simplification.out proof-simplification.toc

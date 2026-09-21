.PHONY: pdf check symbolic clean

pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

check:
	python3 code/verify.py

symbolic:
	python3 code/symbolic_checks.py

clean:
	rm -f article.aux article.log article.out article.toc

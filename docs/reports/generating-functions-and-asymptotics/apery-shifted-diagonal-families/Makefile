.PHONY: all pdf verify symbolic diagnostics clean
all: pdf verify
pdf:
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
verify:
	python3 verify.py
symbolic:
	python3 check_symbolic.py
diagnostics:
	python3 diagnostics.py
clean:
	rm -f article.aux article.log article.out article.toc

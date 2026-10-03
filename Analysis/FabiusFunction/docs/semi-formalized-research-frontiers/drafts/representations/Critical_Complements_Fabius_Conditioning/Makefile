.PHONY: pdf check reproduce clean

pdf:
	latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

check:
	MPLBACKEND=Agg python code/verify.py

reproduce: check pdf

clean:
	latexmk -c article.tex

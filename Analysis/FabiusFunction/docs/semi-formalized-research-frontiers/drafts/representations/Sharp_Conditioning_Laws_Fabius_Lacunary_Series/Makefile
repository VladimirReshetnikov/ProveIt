.PHONY: pdf figures verify fast-check clean

pdf: article.pdf

article.pdf: article.tex figures/tv_profile.pdf figures/boundary_phase.pdf
	pdflatex -interaction=nonstopmode -halt-on-error article.tex
	pdflatex -interaction=nonstopmode -halt-on-error article.tex

figures:
	python verification.py --skip-monte-carlo

verify:
	python verification.py --draws 240000

fast-check:
	python verification.py --skip-monte-carlo

clean:
	rm -f article.aux article.log article.out article.toc article.fls article.fdb_latexmk
